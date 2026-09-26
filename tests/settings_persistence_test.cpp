#include <chrono>
#include <filesystem>
#include <fstream>
#include <sstream>
#include <string>
#include <system_error>

#include <gtest/gtest.h>

#include "settings.h"

namespace {

std::string readText(const std::filesystem::path &path) {
  const std::ifstream stream(path);
  std::ostringstream contents;
  contents << stream.rdbuf();
  return contents.str();
}

class SettingsPersistence : public testing::Test {
protected:
  void SetUp() override {
    const auto stamp = std::chrono::steady_clock::now().time_since_epoch().count();
    directory_ =
        std::filesystem::path(testing::TempDir()) / ("blackhole-settings-" + std::to_string(stamp));
    ASSERT_TRUE(std::filesystem::create_directory(directory_));
    SettingsManager::instance().resetToDefaults();
  }

  void TearDown() override {
    SettingsManager::instance().resetToDefaults();
    std::error_code error;
    std::filesystem::remove_all(directory_, error);
    EXPECT_FALSE(error) << error.message();
  }

  [[nodiscard]] const std::filesystem::path &testDirectory() const { return directory_; }

private:
  std::filesystem::path directory_;
};

TEST_F(SettingsPersistence, EverySerializedFieldLoadsANondefaultValue) {
  auto &manager = SettingsManager::instance();
  const auto original = testDirectory() / "original.json";
  ASSERT_TRUE(manager.save(original.string()));
  std::istringstream lines(readText(original));
  std::ostringstream changed;
  std::string line;
  int fieldCount = 0;
  while (std::getline(lines, line)) {
    const auto separator = line.find(": ");
    if (separator != std::string::npos) {
      const auto valueStart = separator + 2;
      const bool hasComma = line.back() == ',';
      const std::string value =
          line.substr(valueStart, line.size() - valueStart - (hasComma ? 1 : 0));
      std::string replacement = std::to_string(fieldCount + 17);
      if (value == "true") {
        replacement = "false";
      } else if (value == "false") {
        replacement = "true";
      } else if (value.starts_with('"')) {
        replacement = "\"fixture-background\"";
      }
      line.erase(valueStart);
      line.append(replacement);
      if (hasComma) {
        line.push_back(',');
      }
      ++fieldCount;
    }
    changed << line << '\n';
  }
  ASSERT_GT(fieldCount, 70);
  const auto input = testDirectory() / "changed.json";
  {
    std::ofstream stream(input);
    stream << changed.str();
    stream.close();
    ASSERT_TRUE(stream);
  }
  ASSERT_TRUE(manager.load(input.string()));
  const auto output = testDirectory() / "roundtrip.json";
  ASSERT_TRUE(manager.save(output.string()));
  EXPECT_EQ(readText(output), changed.str());
}

TEST_F(SettingsPersistence, ExplicitSwapIntervalWinsInEitherFileOrder) {
  auto &manager = SettingsManager::instance();
  const auto input = testDirectory() / "aliases.json";
  for (const std::string &contents : {std::string("\"vsync\": false,\n\"swapInterval\": 2\n"),
                                      std::string("\"swapInterval\": 2,\n\"vsync\": false\n")}) {
    std::ofstream stream(input);
    stream << contents;
    stream.close();
    ASSERT_TRUE(stream);
    manager.resetToDefaults();
    ASSERT_TRUE(manager.load(input.string()));
    EXPECT_EQ(manager.get().swapInterval, 2);
  }
}

TEST_F(SettingsPersistence, LegacyVsyncAndUnknownKeysRemainSupported) {
  const auto input = testDirectory() / "legacy.json";
  std::ofstream stream(input);
  stream << "\"vsync\": false,\n\"futureSetting\": 42\n";
  stream.close();
  ASSERT_TRUE(stream);
  auto &manager = SettingsManager::instance();
  ASSERT_TRUE(manager.load(input.string()));
  EXPECT_EQ(manager.get().swapInterval, 0);
  EXPECT_EQ(manager.get().windowWidth, Settings{}.windowWidth);
}

TEST_F(SettingsPersistence, FreshSettingsCarryTheRuleExposureAndSkyIntensity) {
  const Settings fresh;
  EXPECT_EQ(fresh.toneExposure, K_DEFAULT_TONE_EXPOSURE);
  EXPECT_EQ(fresh.backgroundIntensity, K_DEFAULT_BACKGROUND_INTENSITY);
  auto &manager = SettingsManager::instance();
  const auto output = testDirectory() / "fresh.json";
  ASSERT_TRUE(manager.save(output.string()));
  EXPECT_TRUE(readText(output).contains("\"toneExposure\": 4.9,"));
}

TEST_F(SettingsPersistence, LegacyFileWithoutExposureKeepsItsLook) {
  const auto input = testDirectory() / "legacy-exposure.json";
  std::ofstream stream(input);
  stream << "\"backgroundIntensity\": 1,\n\"gamma\": 2.5\n";
  stream.close();
  ASSERT_TRUE(stream);
  auto &manager = SettingsManager::instance();
  ASSERT_TRUE(manager.load(input.string()));
  EXPECT_EQ(manager.get().toneExposure, K_LEGACY_TONE_EXPOSURE);
  EXPECT_EQ(manager.get().backgroundIntensity, 1.0f);
}

TEST_F(SettingsPersistence, SavedExposureRoundTrips) {
  auto &manager = SettingsManager::instance();
  manager.get().toneExposure = 2.75f;
  const auto output = testDirectory() / "exposure.json";
  ASSERT_TRUE(manager.save(output.string()));
  manager.resetToDefaults();
  ASSERT_TRUE(manager.load(output.string()));
  EXPECT_EQ(manager.get().toneExposure, 2.75f);
}

TEST_F(SettingsPersistence, FileWithoutCameraKeysTakesTheDefaultCamera) {
  const auto input = testDirectory() / "no-camera.json";
  std::ofstream stream(input);
  stream << "\"windowWidth\": 1280\n";
  stream.close();
  ASSERT_TRUE(stream);
  auto &manager = SettingsManager::instance();
  ASSERT_TRUE(manager.load(input.string()));
  EXPECT_EQ(manager.get().cameraDistance, K_DEFAULT_CAMERA_DISTANCE);
  EXPECT_EQ(manager.get().cameraPitch, K_DEFAULT_CAMERA_PITCH_DEG);
  // The default camera sits outside the disk's 100 r_s = 200 unit outer edge.
  EXPECT_GT(K_DEFAULT_CAMERA_DISTANCE, 200.0f);
}

TEST_F(SettingsPersistence, SavedCameraKeysKeepTheirValues) {
  const auto input = testDirectory() / "saved-camera.json";
  std::ofstream stream(input);
  stream << "\"cameraYaw\": 0,\n\"cameraPitch\": -6,\n\"cameraDistance\": 15\n";
  stream.close();
  ASSERT_TRUE(stream);
  auto &manager = SettingsManager::instance();
  ASSERT_TRUE(manager.load(input.string()));
  EXPECT_EQ(manager.get().cameraDistance, 15.0f);
  EXPECT_EQ(manager.get().cameraPitch, -6.0f);
}

} // namespace
