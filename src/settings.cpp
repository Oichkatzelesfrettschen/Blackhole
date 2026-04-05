/**
 * @file settings.cpp
 * @brief Implementation of SettingsManager: JSON load/save and default reset.
 */

#include "settings.h"

#include <cstdio>
#include <cstring>
#include <fstream>
#include <string>

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

} // namespace

SettingsManager &SettingsManager::instance() {
  static SettingsManager instance;
  return instance;
}

bool SettingsManager::load(
    const std::string &filepath) { // NOLINT(readability-function-cognitive-complexity) -- INI
                                   // parser inherently has many branches
  lastFilepath_ = filepath;

  std::ifstream file(filepath);
  if (!file.is_open()) {
    return false;
  }

  std::string line;
  bool swapIntervalParsed = false;
  while (std::getline(file, line)) {
    line = trim(line);
    if (line.empty() || line.at(0) == '{' || line.at(0) == '}') {
      continue;
    }

    std::string const value = extractValue(line);
    if (value.empty()) {
      continue;
    }

    // Display settings
    if (line.contains("\"windowWidth\"")) {
      {
        settings_.windowWidth = parseInt(value);
      }
    } else if (line.contains("\"windowHeight\"")) {
      {
        settings_.windowHeight = parseInt(value);
      }
    } else if (line.contains("\"fullscreen\"")) {
      {
        settings_.fullscreen = parseBool(value);
      }
    } else if (line.contains("\"swapInterval\"")) {
      settings_.swapInterval = parseInt(value);
      swapIntervalParsed = true;
    } else if (line.contains("\"vsync\"") && !swapIntervalParsed) {
      settings_.swapInterval = parseBool(value) ? 1 : 0;
    } else if (line.contains("\"renderScale\"")) {
      {
        settings_.renderScale = parseFloat(value);
      }
    } else if (line.contains("\"gamma\"")) {
      {
        settings_.gamma = parseFloat(value);

        // Controls
      }
    } else if (line.contains("\"mouseSensitivity\"")) {
      {
        settings_.mouseSensitivity = parseFloat(value);
      }
    } else if (line.contains("\"keyboardSensitivity\"")) {
      {
        settings_.keyboardSensitivity = parseFloat(value);
      }
    } else if (line.contains("\"scrollSensitivity\"")) {
      {
        settings_.scrollSensitivity = parseFloat(value);
      }
    } else if (line.contains("\"invertMouseX\"")) {
      {
        settings_.invertMouseX = parseBool(value);
      }
    } else if (line.contains("\"invertMouseY\"")) {
      {
        settings_.invertMouseY = parseBool(value);
      }
    } else if (line.contains("\"invertKeyboardX\"")) {
      {
        settings_.invertKeyboardX = parseBool(value);
      }
    } else if (line.contains("\"invertKeyboardY\"")) {
      {
        settings_.invertKeyboardY = parseBool(value);
      }
    } else if (line.contains("\"holdToToggleCamera\"")) {
      {
        settings_.holdToToggleCamera = parseBool(value);
      }
    } else if (line.contains("\"timeScale\"")) {
      {
        settings_.timeScale = parseFloat(value);

        // Key bindings
      }
    } else if (line.contains("\"keyQuit\"")) {
      {
        settings_.keyQuit = parseInt(value);
      }
    } else if (line.contains("\"keyToggleUI\"")) {
      {
        settings_.keyToggleUI = parseInt(value);
      }
    } else if (line.contains("\"keyToggleFullscreen\"")) {
      {
        settings_.keyToggleFullscreen = parseInt(value);
      }
    } else if (line.contains("\"keyResetCamera\"")) {
      {
        settings_.keyResetCamera = parseInt(value);
      }
    } else if (line.contains("\"keyResetSettings\"")) {
      {
        settings_.keyResetSettings = parseInt(value);
      }
    } else if (line.contains("\"keyPause\"")) {
      {
        settings_.keyPause = parseInt(value);
      }
    } else if (line.contains("\"keyCameraForward\"")) {
      {
        settings_.keyCameraForward = parseInt(value);
      }
    } else if (line.contains("\"keyCameraBackward\"")) {
      {
        settings_.keyCameraBackward = parseInt(value);
      }
    } else if (line.contains("\"keyCameraLeft\"")) {
      {
        settings_.keyCameraLeft = parseInt(value);
      }
    } else if (line.contains("\"keyCameraRight\"")) {
      {
        settings_.keyCameraRight = parseInt(value);
      }
    } else if (line.contains("\"keyCameraUp\"")) {
      {
        settings_.keyCameraUp = parseInt(value);
      }
    } else if (line.contains("\"keyCameraDown\"")) {
      {
        settings_.keyCameraDown = parseInt(value);
      }
    } else if (line.contains("\"keyCameraRollLeft\"")) {
      {
        settings_.keyCameraRollLeft = parseInt(value);
      }
    } else if (line.contains("\"keyCameraRollRight\"")) {
      {
        settings_.keyCameraRollRight = parseInt(value);
      }
    } else if (line.contains("\"keyZoomIn\"")) {
      {
        settings_.keyZoomIn = parseInt(value);
      }
    } else if (line.contains("\"keyZoomOut\"")) {
      {
        settings_.keyZoomOut = parseInt(value);
      }
    } else if (line.contains("\"keyIncreaseFontSize\"")) {
      {
        settings_.keyIncreaseFontSize = parseInt(value);
      }
    } else if (line.contains("\"keyDecreaseFontSize\"")) {
      {
        settings_.keyDecreaseFontSize = parseInt(value);
      }
    } else if (line.contains("\"keyIncreaseTimeScale\"")) {
      {
        settings_.keyIncreaseTimeScale = parseInt(value);
      }
    } else if (line.contains("\"keyDecreaseTimeScale\"")) {
      {
        settings_.keyDecreaseTimeScale = parseInt(value);

        // Gamepad
      }
    } else if (line.contains("\"gamepadEnabled\"")) {
      {
        settings_.gamepadEnabled = parseBool(value);
      }
    } else if (line.contains("\"gamepadDeadzone\"")) {
      {
        settings_.gamepadDeadzone = parseFloat(value);
      }
    } else if (line.contains("\"gamepadLookSensitivity\"")) {
      {
        settings_.gamepadLookSensitivity = parseFloat(value);
      }
    } else if (line.contains("\"gamepadRollSensitivity\"")) {
      {
        settings_.gamepadRollSensitivity = parseFloat(value);
      }
    } else if (line.contains("\"gamepadZoomSensitivity\"")) {
      {
        settings_.gamepadZoomSensitivity = parseFloat(value);
      }
    } else if (line.contains("\"gamepadTriggerZoomSensitivity\"")) {
      {
        settings_.gamepadTriggerZoomSensitivity = parseFloat(value);
      }
    } else if (line.contains("\"gamepadInvertX\"")) {
      {
        settings_.gamepadInvertX = parseBool(value);
      }
    } else if (line.contains("\"gamepadInvertY\"")) {
      {
        settings_.gamepadInvertY = parseBool(value);
      }
    } else if (line.contains("\"gamepadInvertRoll\"")) {
      {
        settings_.gamepadInvertRoll = parseBool(value);
      }
    } else if (line.contains("\"gamepadInvertZoom\"")) {
      {
        settings_.gamepadInvertZoom = parseBool(value);
      }
    } else if (line.contains("\"gamepadYawAxis\"")) {
      {
        settings_.gamepadYawAxis = parseInt(value);
      }
    } else if (line.contains("\"gamepadPitchAxis\"")) {
      {
        settings_.gamepadPitchAxis = parseInt(value);
      }
    } else if (line.contains("\"gamepadRollAxis\"")) {
      {
        settings_.gamepadRollAxis = parseInt(value);
      }
    } else if (line.contains("\"gamepadZoomAxis\"")) {
      {
        settings_.gamepadZoomAxis = parseInt(value);
      }
    } else if (line.contains("\"gamepadZoomInAxis\"")) {
      {
        settings_.gamepadZoomInAxis = parseInt(value);
      }
    } else if (line.contains("\"gamepadZoomOutAxis\"")) {
      {
        settings_.gamepadZoomOutAxis = parseInt(value);
      }
    } else if (line.contains("\"gamepadResetButton\"")) {
      {
        settings_.gamepadResetButton = parseInt(value);
      }
    } else if (line.contains("\"gamepadPauseButton\"")) {
      {
        settings_.gamepadPauseButton = parseInt(value);
      }
    } else if (line.contains("\"gamepadToggleUIButton\"")) {
      {
        settings_.gamepadToggleUIButton = parseInt(value);

        // Rendering
      }
    } else if (line.contains("\"tonemappingEnabled\"")) {
      {
        settings_.tonemappingEnabled = parseBool(value);
      }
    } else if (line.contains("\"bloomStrength\"")) {
      {
        settings_.bloomStrength = parseFloat(value);
      }
    } else if (line.contains("\"bloomIterations\"")) {
      {
        settings_.bloomIterations = parseInt(value);
      }
    } else if (line.contains("\"backgroundEnabled\"")) {
      {
        settings_.backgroundEnabled = parseBool(value);
      }
    } else if (line.contains("\"backgroundId\"")) {
      {
        settings_.backgroundId = value;
      }
    } else if (line.contains("\"backgroundIntensity\"")) {
      {
        settings_.backgroundIntensity = parseFloat(value);
      }
    } else if (line.contains("\"backgroundParallaxStrength\"")) {
      {
        settings_.backgroundParallaxStrength = parseFloat(value);
      }
    } else if (line.contains("\"backgroundDriftStrength\"")) {
      {
        settings_.backgroundDriftStrength = parseFloat(value);

        // Camera
      }
    } else if (line.contains("\"cameraYaw\"")) {
      {
        settings_.cameraYaw = parseFloat(value);
      }
    } else if (line.contains("\"cameraPitch\"")) {
      {
        settings_.cameraPitch = parseFloat(value);
      }
    } else if (line.contains("\"cameraRoll\"")) {
      {
        settings_.cameraRoll = parseFloat(value);
      }
    } else if (line.contains("\"cameraDistance\"")) {
      {
        settings_.cameraDistance = parseFloat(value);
      }
    } else if (line.contains("\"cameraMode\"")) {
      {
        settings_.cameraMode = parseInt(value);
      }
    } else if (line.contains("\"orbitRadius\"")) {
      {
        settings_.orbitRadius = parseFloat(value);
      }
    } else if (line.contains("\"orbitSpeed\"")) {
      {
        settings_.orbitSpeed = parseFloat(value);

        // Black hole parameters
      }
    } else if (line.contains("\"gravitationalLensing\"")) {
      {
        settings_.gravitationalLensing = parseBool(value);
      }
    } else if (line.contains("\"renderBlackHole\"")) {
      {
        settings_.renderBlackHole = parseBool(value);
      }
    } else if (line.contains("\"adiskEnabled\"")) {
      {
        settings_.adiskEnabled = parseBool(value);
      }
    } else if (line.contains("\"adiskParticle\"")) {
      {
        settings_.adiskParticle = parseBool(value);
      }
    } else if (line.contains("\"adiskDensityV\"")) {
      {
        settings_.adiskDensityV = parseFloat(value);
      }
    } else if (line.contains("\"adiskDensityH\"")) {
      {
        settings_.adiskDensityH = parseFloat(value);
      }
    } else if (line.contains("\"adiskHeight\"")) {
      {
        settings_.adiskHeight = parseFloat(value);
      }
    } else if (line.contains("\"adiskLit\"")) {
      {
        settings_.adiskLit = parseFloat(value);
      }
    } else if (line.contains("\"adiskNoiseLOD\"")) {
      {
        settings_.adiskNoiseLOD = parseFloat(value);
      }
    } else if (line.contains("\"adiskNoiseScale\"")) {
      {
        settings_.adiskNoiseScale = parseFloat(value);
      }
    } else if (line.contains("\"adiskSpeed\"")) {
      {
        settings_.adiskSpeed = parseFloat(value);
      }
    }
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
