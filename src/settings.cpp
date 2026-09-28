/**
 * @file settings.cpp
 * @brief Implementation of SettingsManager: JSON load/save and default reset.
 */

#include "settings.h"

#include <algorithm>
#include <array>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <string>
#include <string_view>
#include <type_traits>

namespace {

std::string trim(const std::string &s) {
  size_t const start = s.find_first_not_of(" \t\n\r");
  if (start == std::string::npos) {
    return "";
  }
  size_t const end = s.find_last_not_of(" \t\n\r");
  return s.substr(start, end - start + 1);
}

std::string extractValue(const std::string &line) {
  size_t const colonPos = line.find(':');
  if (colonPos == std::string::npos) {
    return "";
  }
  std::string value = line.substr(colonPos + 1);
  value = trim(value);
  if (!value.empty() && value.back() == ',') {
    value.pop_back();
  }
  if (value.size() >= 2 && value.front() == '"' && value.back() == '"') {
    value = value.substr(1, value.size() - 2);
  }
  return value;
}

bool parseBool(const std::string &value) {
  return value == "true" || value == "1";
}

int parseInt(const std::string &value) {
  return std::stoi(value);
}

float parseFloat(const std::string &value) {
  return std::stof(value);
}

struct SettingBinding {
  std::string_view key;
  void (*assign)(Settings &, const std::string &);
};

template <auto Member> void assignSetting(Settings &settings, const std::string &value) {
  using FieldType = std::remove_cvref_t<decltype(settings.*Member)>;
  if constexpr (std::is_same_v<FieldType, bool>) {
    settings.*Member = parseBool(value);
  } else if constexpr (std::is_same_v<FieldType, int>) {
    settings.*Member = parseInt(value);
  } else if constexpr (std::is_same_v<FieldType, float>) {
    settings.*Member = parseFloat(value);
  } else {
    settings.*Member = value;
  }
}

void assignLegacyVsync(Settings &settings, const std::string &value) {
  settings.swapInterval = parseBool(value) ? 1 : 0;
}

// Preserve file-order matching and the legacy vsync alias while binding each
// persisted key to the type of its Settings member.
constexpr std::array<SettingBinding, 85> K_SETTING_BINDINGS{{
    {.key = "\"windowWidth\"", .assign = assignSetting<&Settings::windowWidth>},
    {.key = "\"windowHeight\"", .assign = assignSetting<&Settings::windowHeight>},
    {.key = "\"fullscreen\"", .assign = assignSetting<&Settings::fullscreen>},
    {.key = "\"swapInterval\"", .assign = assignSetting<&Settings::swapInterval>},
    {.key = "\"vsync\"", .assign = assignLegacyVsync},
    {.key = "\"renderScale\"", .assign = assignSetting<&Settings::renderScale>},
    {.key = "\"gamma\"", .assign = assignSetting<&Settings::gamma>},
    {.key = "\"mouseSensitivity\"", .assign = assignSetting<&Settings::mouseSensitivity>},
    {.key = "\"keyboardSensitivity\"", .assign = assignSetting<&Settings::keyboardSensitivity>},
    {.key = "\"scrollSensitivity\"", .assign = assignSetting<&Settings::scrollSensitivity>},
    {.key = "\"invertMouseX\"", .assign = assignSetting<&Settings::invertMouseX>},
    {.key = "\"invertMouseY\"", .assign = assignSetting<&Settings::invertMouseY>},
    {.key = "\"invertKeyboardX\"", .assign = assignSetting<&Settings::invertKeyboardX>},
    {.key = "\"invertKeyboardY\"", .assign = assignSetting<&Settings::invertKeyboardY>},
    {.key = "\"holdToToggleCamera\"", .assign = assignSetting<&Settings::holdToToggleCamera>},
    {.key = "\"timeScale\"", .assign = assignSetting<&Settings::timeScale>},
    {.key = "\"keyQuit\"", .assign = assignSetting<&Settings::keyQuit>},
    {.key = "\"keyToggleUI\"", .assign = assignSetting<&Settings::keyToggleUI>},
    {.key = "\"keyToggleFullscreen\"", .assign = assignSetting<&Settings::keyToggleFullscreen>},
    {.key = "\"keyResetCamera\"", .assign = assignSetting<&Settings::keyResetCamera>},
    {.key = "\"keyResetSettings\"", .assign = assignSetting<&Settings::keyResetSettings>},
    {.key = "\"keyPause\"", .assign = assignSetting<&Settings::keyPause>},
    {.key = "\"keyCameraForward\"", .assign = assignSetting<&Settings::keyCameraForward>},
    {.key = "\"keyCameraBackward\"", .assign = assignSetting<&Settings::keyCameraBackward>},
    {.key = "\"keyCameraLeft\"", .assign = assignSetting<&Settings::keyCameraLeft>},
    {.key = "\"keyCameraRight\"", .assign = assignSetting<&Settings::keyCameraRight>},
    {.key = "\"keyCameraUp\"", .assign = assignSetting<&Settings::keyCameraUp>},
    {.key = "\"keyCameraDown\"", .assign = assignSetting<&Settings::keyCameraDown>},
    {.key = "\"keyCameraRollLeft\"", .assign = assignSetting<&Settings::keyCameraRollLeft>},
    {.key = "\"keyCameraRollRight\"", .assign = assignSetting<&Settings::keyCameraRollRight>},
    {.key = "\"keyZoomIn\"", .assign = assignSetting<&Settings::keyZoomIn>},
    {.key = "\"keyZoomOut\"", .assign = assignSetting<&Settings::keyZoomOut>},
    {.key = "\"keyIncreaseFontSize\"", .assign = assignSetting<&Settings::keyIncreaseFontSize>},
    {.key = "\"keyDecreaseFontSize\"", .assign = assignSetting<&Settings::keyDecreaseFontSize>},
    {.key = "\"keyIncreaseTimeScale\"", .assign = assignSetting<&Settings::keyIncreaseTimeScale>},
    {.key = "\"keyDecreaseTimeScale\"", .assign = assignSetting<&Settings::keyDecreaseTimeScale>},
    {.key = "\"gamepadEnabled\"", .assign = assignSetting<&Settings::gamepadEnabled>},
    {.key = "\"gamepadDeadzone\"", .assign = assignSetting<&Settings::gamepadDeadzone>},
    {.key = "\"gamepadLookSensitivity\"",
     .assign = assignSetting<&Settings::gamepadLookSensitivity>},
    {.key = "\"gamepadRollSensitivity\"",
     .assign = assignSetting<&Settings::gamepadRollSensitivity>},
    {.key = "\"gamepadZoomSensitivity\"",
     .assign = assignSetting<&Settings::gamepadZoomSensitivity>},
    {.key = "\"gamepadTriggerZoomSensitivity\"",
     .assign = assignSetting<&Settings::gamepadTriggerZoomSensitivity>},
    {.key = "\"gamepadInvertX\"", .assign = assignSetting<&Settings::gamepadInvertX>},
    {.key = "\"gamepadInvertY\"", .assign = assignSetting<&Settings::gamepadInvertY>},
    {.key = "\"gamepadInvertRoll\"", .assign = assignSetting<&Settings::gamepadInvertRoll>},
    {.key = "\"gamepadInvertZoom\"", .assign = assignSetting<&Settings::gamepadInvertZoom>},
    {.key = "\"gamepadYawAxis\"", .assign = assignSetting<&Settings::gamepadYawAxis>},
    {.key = "\"gamepadPitchAxis\"", .assign = assignSetting<&Settings::gamepadPitchAxis>},
    {.key = "\"gamepadRollAxis\"", .assign = assignSetting<&Settings::gamepadRollAxis>},
    {.key = "\"gamepadZoomAxis\"", .assign = assignSetting<&Settings::gamepadZoomAxis>},
    {.key = "\"gamepadZoomInAxis\"", .assign = assignSetting<&Settings::gamepadZoomInAxis>},
    {.key = "\"gamepadZoomOutAxis\"", .assign = assignSetting<&Settings::gamepadZoomOutAxis>},
    {.key = "\"gamepadResetButton\"", .assign = assignSetting<&Settings::gamepadResetButton>},
    {.key = "\"gamepadPauseButton\"", .assign = assignSetting<&Settings::gamepadPauseButton>},
    {.key = "\"gamepadToggleUIButton\"", .assign = assignSetting<&Settings::gamepadToggleUIButton>},
    {.key = "\"tonemappingEnabled\"", .assign = assignSetting<&Settings::tonemappingEnabled>},
    {.key = "\"toneExposure\"", .assign = assignSetting<&Settings::toneExposure>},
    {.key = "\"bloomStrength\"", .assign = assignSetting<&Settings::bloomStrength>},
    {.key = "\"bloomIterations\"", .assign = assignSetting<&Settings::bloomIterations>},
    {.key = "\"backgroundEnabled\"", .assign = assignSetting<&Settings::backgroundEnabled>},
    {.key = "\"backgroundId\"", .assign = assignSetting<&Settings::backgroundId>},
    {.key = "\"backgroundIntensity\"", .assign = assignSetting<&Settings::backgroundIntensity>},
    {.key = "\"backgroundParallaxStrength\"",
     .assign = assignSetting<&Settings::backgroundParallaxStrength>},
    {.key = "\"backgroundDriftStrength\"",
     .assign = assignSetting<&Settings::backgroundDriftStrength>},
    {.key = "\"cameraYaw\"", .assign = assignSetting<&Settings::cameraYaw>},
    {.key = "\"cameraPitch\"", .assign = assignSetting<&Settings::cameraPitch>},
    {.key = "\"cameraRoll\"", .assign = assignSetting<&Settings::cameraRoll>},
    {.key = "\"cameraDistance\"", .assign = assignSetting<&Settings::cameraDistance>},
    {.key = "\"cameraMode\"", .assign = assignSetting<&Settings::cameraMode>},
    {.key = "\"orbitRadius\"", .assign = assignSetting<&Settings::orbitRadius>},
    {.key = "\"orbitSpeed\"", .assign = assignSetting<&Settings::orbitSpeed>},
    {.key = "\"gravitationalLensing\"", .assign = assignSetting<&Settings::gravitationalLensing>},
    {.key = "\"renderBlackHole\"", .assign = assignSetting<&Settings::renderBlackHole>},
    {.key = "\"adiskEnabled\"", .assign = assignSetting<&Settings::adiskEnabled>},
    {.key = "\"adiskParticle\"", .assign = assignSetting<&Settings::adiskParticle>},
    {.key = "\"adiskDensityV\"", .assign = assignSetting<&Settings::adiskDensityV>},
    {.key = "\"adiskDensityH\"", .assign = assignSetting<&Settings::adiskDensityH>},
    {.key = "\"adiskHeight\"", .assign = assignSetting<&Settings::adiskHeight>},
    {.key = "\"adiskLit\"", .assign = assignSetting<&Settings::adiskLit>},
    {.key = "\"adiskNoiseLOD\"", .assign = assignSetting<&Settings::adiskNoiseLOD>},
    {.key = "\"adiskNoiseScale\"", .assign = assignSetting<&Settings::adiskNoiseScale>},
    {.key = "\"adiskSpeed\"", .assign = assignSetting<&Settings::adiskSpeed>},
    {.key = "\"workspaceSchemaVersion\"", .assign = assignSetting<&Settings::workspaceSchemaVersion>},
    {.key = "\"workspaceKind\"", .assign = assignSetting<&Settings::workspaceKind>},
    {.key = "\"advancedControls\"", .assign = assignSetting<&Settings::advancedControls>},
}};

} // namespace

SettingsManager &SettingsManager::instance() {
  static SettingsManager instance;
  return instance;
}

bool SettingsManager::load(const std::string &filepath) {
  lastFilepath_ = filepath;

  std::ifstream file(filepath);
  if (!file.is_open()) {
    return false;
  }

  std::string line;
  bool swapIntervalParsed = false;
  bool toneExposureParsed = false;
  while (std::getline(file, line)) {
    line = trim(line);
    if (line.empty() || line.at(0) == '{' || line.at(0) == '}') {
      continue;
    }

    std::string const value = extractValue(line);
    if (value.empty()) {
      continue;
    }

    const auto *binding =
        std::ranges::find_if(K_SETTING_BINDINGS, [&](const SettingBinding &candidate) {
          return line.contains(candidate.key) &&
                 (candidate.key != "\"vsync\"" || !swapIntervalParsed);
        });
    if (binding != K_SETTING_BINDINGS.end()) {
      binding->assign(settings_, value);
      swapIntervalParsed = swapIntervalParsed || binding->key == "\"swapInterval\"";
      toneExposureParsed = toneExposureParsed || binding->key == "\"toneExposure\"";
    }
  }
  if (!toneExposureParsed) {
    settings_.toneExposure = K_LEGACY_TONE_EXPOSURE;
  }

  return true;
}

bool SettingsManager::save(const std::string &filepath) {
  lastFilepath_ = filepath;

  std::ofstream file(filepath);
  if (!file.is_open()) {
    return false;
  }

  auto writeBool = [](bool v) { return v ? "true" : "false"; };

  file << "{\n";
  file << "  \"workspaceSchemaVersion\": " << settings_.workspaceSchemaVersion << ",\n";
  file << "  \"workspaceKind\": " << settings_.workspaceKind << ",\n";
  file << "  \"advancedControls\": " << writeBool(settings_.advancedControls) << ",\n";

  // Display
  file << "  \"windowWidth\": " << settings_.windowWidth << ",\n";
  file << "  \"windowHeight\": " << settings_.windowHeight << ",\n";
  file << "  \"fullscreen\": " << writeBool(settings_.fullscreen) << ",\n";
  file << "  \"swapInterval\": " << settings_.swapInterval << ",\n";
  file << "  \"renderScale\": " << settings_.renderScale << ",\n";
  file << "  \"gamma\": " << settings_.gamma << ",\n";

  // Controls
  file << "  \"mouseSensitivity\": " << settings_.mouseSensitivity << ",\n";
  file << "  \"keyboardSensitivity\": " << settings_.keyboardSensitivity << ",\n";
  file << "  \"scrollSensitivity\": " << settings_.scrollSensitivity << ",\n";
  file << "  \"invertMouseX\": " << writeBool(settings_.invertMouseX) << ",\n";
  file << "  \"invertMouseY\": " << writeBool(settings_.invertMouseY) << ",\n";
  file << "  \"invertKeyboardX\": " << writeBool(settings_.invertKeyboardX) << ",\n";
  file << "  \"invertKeyboardY\": " << writeBool(settings_.invertKeyboardY) << ",\n";
  file << "  \"holdToToggleCamera\": " << writeBool(settings_.holdToToggleCamera) << ",\n";
  file << "  \"timeScale\": " << settings_.timeScale << ",\n";

  // Key bindings
  file << "  \"keyQuit\": " << settings_.keyQuit << ",\n";
  file << "  \"keyToggleUI\": " << settings_.keyToggleUI << ",\n";
  file << "  \"keyToggleFullscreen\": " << settings_.keyToggleFullscreen << ",\n";
  file << "  \"keyResetCamera\": " << settings_.keyResetCamera << ",\n";
  file << "  \"keyResetSettings\": " << settings_.keyResetSettings << ",\n";
  file << "  \"keyPause\": " << settings_.keyPause << ",\n";
  file << "  \"keyCameraForward\": " << settings_.keyCameraForward << ",\n";
  file << "  \"keyCameraBackward\": " << settings_.keyCameraBackward << ",\n";
  file << "  \"keyCameraLeft\": " << settings_.keyCameraLeft << ",\n";
  file << "  \"keyCameraRight\": " << settings_.keyCameraRight << ",\n";
  file << "  \"keyCameraUp\": " << settings_.keyCameraUp << ",\n";
  file << "  \"keyCameraDown\": " << settings_.keyCameraDown << ",\n";
  file << "  \"keyCameraRollLeft\": " << settings_.keyCameraRollLeft << ",\n";
  file << "  \"keyCameraRollRight\": " << settings_.keyCameraRollRight << ",\n";
  file << "  \"keyZoomIn\": " << settings_.keyZoomIn << ",\n";
  file << "  \"keyZoomOut\": " << settings_.keyZoomOut << ",\n";
  file << "  \"keyIncreaseFontSize\": " << settings_.keyIncreaseFontSize << ",\n";
  file << "  \"keyDecreaseFontSize\": " << settings_.keyDecreaseFontSize << ",\n";
  file << "  \"keyIncreaseTimeScale\": " << settings_.keyIncreaseTimeScale << ",\n";
  file << "  \"keyDecreaseTimeScale\": " << settings_.keyDecreaseTimeScale << ",\n";

  // Gamepad
  file << "  \"gamepadEnabled\": " << writeBool(settings_.gamepadEnabled) << ",\n";
  file << "  \"gamepadDeadzone\": " << settings_.gamepadDeadzone << ",\n";
  file << "  \"gamepadLookSensitivity\": " << settings_.gamepadLookSensitivity << ",\n";
  file << "  \"gamepadRollSensitivity\": " << settings_.gamepadRollSensitivity << ",\n";
  file << "  \"gamepadZoomSensitivity\": " << settings_.gamepadZoomSensitivity << ",\n";
  file << "  \"gamepadTriggerZoomSensitivity\": " << settings_.gamepadTriggerZoomSensitivity
       << ",\n";
  file << "  \"gamepadInvertX\": " << writeBool(settings_.gamepadInvertX) << ",\n";
  file << "  \"gamepadInvertY\": " << writeBool(settings_.gamepadInvertY) << ",\n";
  file << "  \"gamepadInvertRoll\": " << writeBool(settings_.gamepadInvertRoll) << ",\n";
  file << "  \"gamepadInvertZoom\": " << writeBool(settings_.gamepadInvertZoom) << ",\n";
  file << "  \"gamepadYawAxis\": " << settings_.gamepadYawAxis << ",\n";
  file << "  \"gamepadPitchAxis\": " << settings_.gamepadPitchAxis << ",\n";
  file << "  \"gamepadRollAxis\": " << settings_.gamepadRollAxis << ",\n";
  file << "  \"gamepadZoomAxis\": " << settings_.gamepadZoomAxis << ",\n";
  file << "  \"gamepadZoomInAxis\": " << settings_.gamepadZoomInAxis << ",\n";
  file << "  \"gamepadZoomOutAxis\": " << settings_.gamepadZoomOutAxis << ",\n";
  file << "  \"gamepadResetButton\": " << settings_.gamepadResetButton << ",\n";
  file << "  \"gamepadPauseButton\": " << settings_.gamepadPauseButton << ",\n";
  file << "  \"gamepadToggleUIButton\": " << settings_.gamepadToggleUIButton << ",\n";

  // Rendering
  file << "  \"tonemappingEnabled\": " << writeBool(settings_.tonemappingEnabled) << ",\n";
  file << "  \"toneExposure\": " << settings_.toneExposure << ",\n";
  file << "  \"bloomStrength\": " << settings_.bloomStrength << ",\n";
  file << "  \"bloomIterations\": " << settings_.bloomIterations << ",\n";
  file << "  \"backgroundEnabled\": " << writeBool(settings_.backgroundEnabled) << ",\n";
  file << R"(  "backgroundId": ")" << settings_.backgroundId << "\",\n";
  file << "  \"backgroundIntensity\": " << settings_.backgroundIntensity << ",\n";
  file << "  \"backgroundParallaxStrength\": " << settings_.backgroundParallaxStrength << ",\n";
  file << "  \"backgroundDriftStrength\": " << settings_.backgroundDriftStrength << ",\n";

  // Camera
  file << "  \"cameraYaw\": " << settings_.cameraYaw << ",\n";
  file << "  \"cameraPitch\": " << settings_.cameraPitch << ",\n";
  file << "  \"cameraRoll\": " << settings_.cameraRoll << ",\n";
  file << "  \"cameraDistance\": " << settings_.cameraDistance << ",\n";
  file << "  \"cameraMode\": " << settings_.cameraMode << ",\n";
  file << "  \"orbitRadius\": " << settings_.orbitRadius << ",\n";
  file << "  \"orbitSpeed\": " << settings_.orbitSpeed << ",\n";

  // Black hole parameters
  file << "  \"gravitationalLensing\": " << writeBool(settings_.gravitationalLensing) << ",\n";
  file << "  \"renderBlackHole\": " << writeBool(settings_.renderBlackHole) << ",\n";
  file << "  \"adiskEnabled\": " << writeBool(settings_.adiskEnabled) << ",\n";
  file << "  \"adiskParticle\": " << writeBool(settings_.adiskParticle) << ",\n";
  file << "  \"adiskDensityV\": " << settings_.adiskDensityV << ",\n";
  file << "  \"adiskDensityH\": " << settings_.adiskDensityH << ",\n";
  file << "  \"adiskHeight\": " << settings_.adiskHeight << ",\n";
  file << "  \"adiskLit\": " << settings_.adiskLit << ",\n";
  file << "  \"adiskNoiseLOD\": " << settings_.adiskNoiseLOD << ",\n";
  file << "  \"adiskNoiseScale\": " << settings_.adiskNoiseScale << ",\n";
  file << "  \"adiskSpeed\": " << settings_.adiskSpeed << "\n";

  file << "}\n";

  return true;
}

void SettingsManager::resetToDefaults() {
  settings_ = Settings();
}
