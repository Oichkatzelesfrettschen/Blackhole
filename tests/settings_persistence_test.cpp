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

} // namespace
