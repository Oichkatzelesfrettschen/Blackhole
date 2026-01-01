#include "settings.h"

#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>

static std::string trim(const std::string &s) {
  size_t start = s.find_first_not_of(" \t\n\r");
  if (start == std::string::npos)
    return "";
  size_t end = s.find_last_not_of(" \t\n\r");
  return s.substr(start, end - start + 1);
}

static std::string extractValue(const std::string &line) {
  size_t colonPos = line.find(':');
  if (colonPos == std::string::npos)
    return "";
  std::string value = line.substr(colonPos + 1);
  value = trim(value);
  if (!value.empty() && value.back() == ',')
    value.pop_back();
  if (value.size() >= 2 && value.front() == '"' && value.back() == '"') {
    value = value.substr(1, value.size() - 2);
  }
  return value;
}

static bool parseBool(const std::string &value) {
  return value == "true" || value == "1";
}

static int parseInt(const std::string &value) { return std::stoi(value); }

static float parseFloat(const std::string &value) { return std::stof(value); }

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
  while (std::getline(file, line)) {
    line = trim(line);
    if (line.empty() || line[0] == '{' || line[0] == '}')
      continue;

    std::string value = extractValue(line);
    if (value.empty())
      continue;

    // Display settings
    if (line.find("\"windowWidth\"") != std::string::npos)
      settings_.windowWidth = parseInt(value);
    else if (line.find("\"windowHeight\"") != std::string::npos)
      settings_.windowHeight = parseInt(value);
    else if (line.find("\"fullscreen\"") != std::string::npos)
      settings_.fullscreen = parseBool(value);
    else if (line.find("\"swapInterval\"") != std::string::npos) {
      settings_.swapInterval = parseInt(value);
      swapIntervalParsed = true;
    } else if (line.find("\"vsync\"") != std::string::npos && !swapIntervalParsed) {
      settings_.swapInterval = parseBool(value) ? 1 : 0;
    }
    else if (line.find("\"renderScale\"") != std::string::npos)
      settings_.renderScale = parseFloat(value);
    else if (line.find("\"gamma\"") != std::string::npos)
      settings_.gamma = parseFloat(value);

    // Controls
    else if (line.find("\"mouseSensitivity\"") != std::string::npos)
      settings_.mouseSensitivity = parseFloat(value);
    else if (line.find("\"keyboardSensitivity\"") != std::string::npos)
      settings_.keyboardSensitivity = parseFloat(value);
    else if (line.find("\"scrollSensitivity\"") != std::string::npos)
      settings_.scrollSensitivity = parseFloat(value);
    else if (line.find("\"invertMouseX\"") != std::string::npos)
      settings_.invertMouseX = parseBool(value);
    else if (line.find("\"invertMouseY\"") != std::string::npos)
      settings_.invertMouseY = parseBool(value);
    else if (line.find("\"invertKeyboardX\"") != std::string::npos)
      settings_.invertKeyboardX = parseBool(value);
    else if (line.find("\"invertKeyboardY\"") != std::string::npos)
      settings_.invertKeyboardY = parseBool(value);
    else if (line.find("\"holdToToggleCamera\"") != std::string::npos)
      settings_.holdToToggleCamera = parseBool(value);
    else if (line.find("\"timeScale\"") != std::string::npos)
      settings_.timeScale = parseFloat(value);

    // Key bindings
    else if (line.find("\"keyQuit\"") != std::string::npos)
      settings_.keyQuit = parseInt(value);
    else if (line.find("\"keyToggleUI\"") != std::string::npos)
      settings_.keyToggleUI = parseInt(value);
    else if (line.find("\"keyToggleFullscreen\"") != std::string::npos)
      settings_.keyToggleFullscreen = parseInt(value);
    else if (line.find("\"keyResetCamera\"") != std::string::npos)
      settings_.keyResetCamera = parseInt(value);
    else if (line.find("\"keyResetSettings\"") != std::string::npos)
      settings_.keyResetSettings = parseInt(value);
    else if (line.find("\"keyPause\"") != std::string::npos)
      settings_.keyPause = parseInt(value);
    else if (line.find("\"keyCameraForward\"") != std::string::npos)
      settings_.keyCameraForward = parseInt(value);
    else if (line.find("\"keyCameraBackward\"") != std::string::npos)
      settings_.keyCameraBackward = parseInt(value);
    else if (line.find("\"keyCameraLeft\"") != std::string::npos)
      settings_.keyCameraLeft = parseInt(value);
    else if (line.find("\"keyCameraRight\"") != std::string::npos)
      settings_.keyCameraRight = parseInt(value);
    else if (line.find("\"keyCameraUp\"") != std::string::npos)
      settings_.keyCameraUp = parseInt(value);
    else if (line.find("\"keyCameraDown\"") != std::string::npos)
      settings_.keyCameraDown = parseInt(value);
    else if (line.find("\"keyCameraRollLeft\"") != std::string::npos)
      settings_.keyCameraRollLeft = parseInt(value);
    else if (line.find("\"keyCameraRollRight\"") != std::string::npos)
      settings_.keyCameraRollRight = parseInt(value);
    else if (line.find("\"keyZoomIn\"") != std::string::npos)
      settings_.keyZoomIn = parseInt(value);
    else if (line.find("\"keyZoomOut\"") != std::string::npos)
      settings_.keyZoomOut = parseInt(value);
    else if (line.find("\"keyIncreaseFontSize\"") != std::string::npos)
      settings_.keyIncreaseFontSize = parseInt(value);
    else if (line.find("\"keyDecreaseFontSize\"") != std::string::npos)
      settings_.keyDecreaseFontSize = parseInt(value);
    else if (line.find("\"keyIncreaseTimeScale\"") != std::string::npos)
      settings_.keyIncreaseTimeScale = parseInt(value);
    else if (line.find("\"keyDecreaseTimeScale\"") != std::string::npos)
      settings_.keyDecreaseTimeScale = parseInt(value);

    // Gamepad
    else if (line.find("\"gamepadEnabled\"") != std::string::npos)
      settings_.gamepadEnabled = parseBool(value);
    else if (line.find("\"gamepadDeadzone\"") != std::string::npos)
      settings_.gamepadDeadzone = parseFloat(value);
    else if (line.find("\"gamepadLookSensitivity\"") != std::string::npos)
      settings_.gamepadLookSensitivity = parseFloat(value);
    else if (line.find("\"gamepadRollSensitivity\"") != std::string::npos)
      settings_.gamepadRollSensitivity = parseFloat(value);
    else if (line.find("\"gamepadZoomSensitivity\"") != std::string::npos)
      settings_.gamepadZoomSensitivity = parseFloat(value);
    else if (line.find("\"gamepadTriggerZoomSensitivity\"") != std::string::npos)
      settings_.gamepadTriggerZoomSensitivity = parseFloat(value);
    else if (line.find("\"gamepadInvertX\"") != std::string::npos)
      settings_.gamepadInvertX = parseBool(value);
    else if (line.find("\"gamepadInvertY\"") != std::string::npos)
      settings_.gamepadInvertY = parseBool(value);
    else if (line.find("\"gamepadInvertRoll\"") != std::string::npos)
      settings_.gamepadInvertRoll = parseBool(value);
    else if (line.find("\"gamepadInvertZoom\"") != std::string::npos)
      settings_.gamepadInvertZoom = parseBool(value);
    else if (line.find("\"gamepadYawAxis\"") != std::string::npos)
      settings_.gamepadYawAxis = parseInt(value);
    else if (line.find("\"gamepadPitchAxis\"") != std::string::npos)
      settings_.gamepadPitchAxis = parseInt(value);
    else if (line.find("\"gamepadRollAxis\"") != std::string::npos)
      settings_.gamepadRollAxis = parseInt(value);
    else if (line.find("\"gamepadZoomAxis\"") != std::string::npos)
      settings_.gamepadZoomAxis = parseInt(value);
    else if (line.find("\"gamepadZoomInAxis\"") != std::string::npos)
      settings_.gamepadZoomInAxis = parseInt(value);
    else if (line.find("\"gamepadZoomOutAxis\"") != std::string::npos)
      settings_.gamepadZoomOutAxis = parseInt(value);
    else if (line.find("\"gamepadResetButton\"") != std::string::npos)
      settings_.gamepadResetButton = parseInt(value);
    else if (line.find("\"gamepadPauseButton\"") != std::string::npos)
      settings_.gamepadPauseButton = parseInt(value);
    else if (line.find("\"gamepadToggleUIButton\"") != std::string::npos)
      settings_.gamepadToggleUIButton = parseInt(value);

    // Rendering
    else if (line.find("\"tonemappingEnabled\"") != std::string::npos)
      settings_.tonemappingEnabled = parseBool(value);
    else if (line.find("\"bloomStrength\"") != std::string::npos)
      settings_.bloomStrength = parseFloat(value);
    else if (line.find("\"bloomIterations\"") != std::string::npos)
      settings_.bloomIterations = parseInt(value);
    else if (line.find("\"backgroundEnabled\"") != std::string::npos)
      settings_.backgroundEnabled = parseBool(value);
    else if (line.find("\"backgroundId\"") != std::string::npos)
      settings_.backgroundId = value;
    else if (line.find("\"backgroundIntensity\"") != std::string::npos)
      settings_.backgroundIntensity = parseFloat(value);
    else if (line.find("\"backgroundParallaxStrength\"") != std::string::npos)
      settings_.backgroundParallaxStrength = parseFloat(value);
    else if (line.find("\"backgroundDriftStrength\"") != std::string::npos)
      settings_.backgroundDriftStrength = parseFloat(value);

    // Camera
    else if (line.find("\"cameraYaw\"") != std::string::npos)
      settings_.cameraYaw = parseFloat(value);
    else if (line.find("\"cameraPitch\"") != std::string::npos)
      settings_.cameraPitch = parseFloat(value);
    else if (line.find("\"cameraRoll\"") != std::string::npos)
      settings_.cameraRoll = parseFloat(value);
    else if (line.find("\"cameraDistance\"") != std::string::npos)
      settings_.cameraDistance = parseFloat(value);
    else if (line.find("\"cameraMode\"") != std::string::npos)
      settings_.cameraMode = parseInt(value);
    else if (line.find("\"orbitRadius\"") != std::string::npos)
      settings_.orbitRadius = parseFloat(value);
    else if (line.find("\"orbitSpeed\"") != std::string::npos)
      settings_.orbitSpeed = parseFloat(value);

    // Black hole parameters
    else if (line.find("\"gravitationalLensing\"") != std::string::npos)
      settings_.gravitationalLensing = parseBool(value);
    else if (line.find("\"renderBlackHole\"") != std::string::npos)
      settings_.renderBlackHole = parseBool(value);
    else if (line.find("\"adiskEnabled\"") != std::string::npos)
      settings_.adiskEnabled = parseBool(value);
    else if (line.find("\"adiskParticle\"") != std::string::npos)
      settings_.adiskParticle = parseBool(value);
    else if (line.find("\"adiskDensityV\"") != std::string::npos)
      settings_.adiskDensityV = parseFloat(value);
    else if (line.find("\"adiskDensityH\"") != std::string::npos)
      settings_.adiskDensityH = parseFloat(value);
    else if (line.find("\"adiskHeight\"") != std::string::npos)
      settings_.adiskHeight = parseFloat(value);
    else if (line.find("\"adiskLit\"") != std::string::npos)
      settings_.adiskLit = parseFloat(value);
    else if (line.find("\"adiskNoiseLOD\"") != std::string::npos)
      settings_.adiskNoiseLOD = parseFloat(value);
    else if (line.find("\"adiskNoiseScale\"") != std::string::npos)
      settings_.adiskNoiseScale = parseFloat(value);
    else if (line.find("\"adiskSpeed\"") != std::string::npos)
      settings_.adiskSpeed = parseFloat(value);
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
  file << "  \"backgroundId\": \"" << settings_.backgroundId << "\",\n";
  file << "  \"backgroundIntensity\": " << settings_.backgroundIntensity << ",\n";
  file << "  \"backgroundParallaxStrength\": " << settings_.backgroundParallaxStrength
       << ",\n";
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

void SettingsManager::resetToDefaults() { settings_ = Settings(); }
