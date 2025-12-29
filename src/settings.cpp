#include "settings.h"

#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>

// Simple JSON parsing without external dependencies
// For production, consider nlohmann/json: https://github.com/nlohmann/json

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
  // Remove trailing comma if present
  if (!value.empty() && value.back() == ',')
    value.pop_back();
  // Remove quotes for strings
  if (value.size() >= 2 && value.front() == '"' && value.back() == '"') {
    value = value.substr(1, value.size() - 2);
  }
  return value;
}

static bool parseBool(const std::string &value) {
  return value == "true" || value == "1";
}

static int parseInt(const std::string &value) {
  return std::stoi(value);
}

static float parseFloat(const std::string &value) {
  return std::stof(value);
}

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
    else if (line.find("\"vsync\"") != std::string::npos)
      settings_.vsync = parseBool(value);
    else if (line.find("\"gamma\"") != std::string::npos)
      settings_.gamma = parseFloat(value);

    // Vision accessibility
    else if (line.find("\"colorblindMode\"") != std::string::npos)
      settings_.colorblindMode = stringToColorblindMode(value);
    else if (line.find("\"colorblindStrength\"") != std::string::npos)
      settings_.colorblindStrength = parseFloat(value);
    else if (line.find("\"highContrastUI\"") != std::string::npos)
      settings_.highContrastUI = parseBool(value);
    else if (line.find("\"invertColors\"") != std::string::npos)
      settings_.invertColors = parseBool(value);
    else if (line.find("\"uiFontScale\"") != std::string::npos)
      settings_.uiFontScale = parseFloat(value);

    // Photosensitivity
    else if (line.find("\"photosensitivityLevel\"") != std::string::npos)
      settings_.photosensitivityLevel = stringToPhotosensitivityLevel(value);
    else if (line.find("\"photosensitivityWarningShown\"") != std::string::npos)
      settings_.photosensitivityWarningShown = parseBool(value);
    else if (line.find("\"maxBloomIntensity\"") != std::string::npos)
      settings_.maxBloomIntensity = parseFloat(value);
    else if (line.find("\"maxFlashFrequency\"") != std::string::npos)
      settings_.maxFlashFrequency = parseFloat(value);
    else if (line.find("\"reduceMotion\"") != std::string::npos)
      settings_.reduceMotion = parseBool(value);

    // Motor accessibility
    else if (line.find("\"holdToToggleCamera\"") != std::string::npos)
      settings_.holdToToggleCamera = parseBool(value);
    else if (line.find("\"holdToToggleUI\"") != std::string::npos)
      settings_.holdToToggleUI = parseBool(value);
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

    // Cognitive accessibility
    else if (line.find("\"showControlHints\"") != std::string::npos)
      settings_.showControlHints = parseBool(value);
    else if (line.find("\"animationSpeed\"") != std::string::npos)
      settings_.animationSpeed = parseFloat(value);
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
    else if (line.find("\"keyAccessibilityMenu\"") != std::string::npos)
      settings_.keyAccessibilityMenu = parseInt(value);

    // Rendering
    else if (line.find("\"tonemappingEnabled\"") != std::string::npos)
      settings_.tonemappingEnabled = parseBool(value);
    else if (line.find("\"bloomStrength\"") != std::string::npos)
      settings_.bloomStrength = parseFloat(value);
    else if (line.find("\"bloomIterations\"") != std::string::npos)
      settings_.bloomIterations = parseInt(value);

    // Camera
    else if (line.find("\"cameraYaw\"") != std::string::npos)
      settings_.cameraYaw = parseFloat(value);
    else if (line.find("\"cameraPitch\"") != std::string::npos)
      settings_.cameraPitch = parseFloat(value);
    else if (line.find("\"cameraRoll\"") != std::string::npos)
      settings_.cameraRoll = parseFloat(value);
    else if (line.find("\"cameraDistance\"") != std::string::npos)
      settings_.cameraDistance = parseFloat(value);

    // Black hole parameters
    else if (line.find("\"gravitationalLensing\"") != std::string::npos)
      settings_.gravitationalLensing = parseBool(value);
    else if (line.find("\"renderBlackHole\"") != std::string::npos)
      settings_.renderBlackHole = parseBool(value);
    else if (line.find("\"mouseControl\"") != std::string::npos)
      settings_.mouseControl = parseBool(value);
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
  file << "  \"vsync\": " << writeBool(settings_.vsync) << ",\n";
  file << "  \"gamma\": " << settings_.gamma << ",\n";

  // Vision accessibility
  file << "  \"colorblindMode\": \"" << colorblindModeToString(settings_.colorblindMode) << "\",\n";
  file << "  \"colorblindStrength\": " << settings_.colorblindStrength << ",\n";
  file << "  \"highContrastUI\": " << writeBool(settings_.highContrastUI) << ",\n";
  file << "  \"invertColors\": " << writeBool(settings_.invertColors) << ",\n";
  file << "  \"uiFontScale\": " << settings_.uiFontScale << ",\n";

  // Photosensitivity
  file << "  \"photosensitivityLevel\": \""
       << photosensitivityLevelToString(settings_.photosensitivityLevel) << "\",\n";
  file << "  \"photosensitivityWarningShown\": "
       << writeBool(settings_.photosensitivityWarningShown) << ",\n";
  file << "  \"maxBloomIntensity\": " << settings_.maxBloomIntensity << ",\n";
  file << "  \"maxFlashFrequency\": " << settings_.maxFlashFrequency << ",\n";
  file << "  \"reduceMotion\": " << writeBool(settings_.reduceMotion) << ",\n";

  // Motor accessibility
  file << "  \"holdToToggleCamera\": " << writeBool(settings_.holdToToggleCamera) << ",\n";
  file << "  \"holdToToggleUI\": " << writeBool(settings_.holdToToggleUI) << ",\n";
  file << "  \"mouseSensitivity\": " << settings_.mouseSensitivity << ",\n";
  file << "  \"keyboardSensitivity\": " << settings_.keyboardSensitivity << ",\n";
  file << "  \"scrollSensitivity\": " << settings_.scrollSensitivity << ",\n";
  file << "  \"invertMouseX\": " << writeBool(settings_.invertMouseX) << ",\n";
  file << "  \"invertMouseY\": " << writeBool(settings_.invertMouseY) << ",\n";
  file << "  \"invertKeyboardX\": " << writeBool(settings_.invertKeyboardX) << ",\n";
  file << "  \"invertKeyboardY\": " << writeBool(settings_.invertKeyboardY) << ",\n";

  // Cognitive accessibility
  file << "  \"showControlHints\": " << writeBool(settings_.showControlHints) << ",\n";
  file << "  \"animationSpeed\": " << settings_.animationSpeed << ",\n";
  file << "  \"timeScale\": " << settings_.timeScale << ",\n";

  // Key bindings
  file << "  \"keyQuit\": " << settings_.keyQuit << ",\n";
  file << "  \"keyToggleUI\": " << settings_.keyToggleUI << ",\n";
  file << "  \"keyToggleFullscreen\": " << settings_.keyToggleFullscreen << ",\n";
  file << "  \"keyResetCamera\": " << settings_.keyResetCamera << ",\n";
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
  file << "  \"keyAccessibilityMenu\": " << settings_.keyAccessibilityMenu << ",\n";

  // Rendering
  file << "  \"tonemappingEnabled\": " << writeBool(settings_.tonemappingEnabled) << ",\n";
  file << "  \"bloomStrength\": " << settings_.bloomStrength << ",\n";
  file << "  \"bloomIterations\": " << settings_.bloomIterations << ",\n";

  // Camera
  file << "  \"cameraYaw\": " << settings_.cameraYaw << ",\n";
  file << "  \"cameraPitch\": " << settings_.cameraPitch << ",\n";
  file << "  \"cameraRoll\": " << settings_.cameraRoll << ",\n";
  file << "  \"cameraDistance\": " << settings_.cameraDistance << ",\n";

  // Black hole parameters
  file << "  \"gravitationalLensing\": " << writeBool(settings_.gravitationalLensing) << ",\n";
  file << "  \"renderBlackHole\": " << writeBool(settings_.renderBlackHole) << ",\n";
  file << "  \"mouseControl\": " << writeBool(settings_.mouseControl) << ",\n";
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

float SettingsManager::getEffectiveBloomStrength() const {
  float base = settings_.bloomStrength;

  switch (settings_.photosensitivityLevel) {
  case PhotosensitivityLevel::None:
    return base;
  case PhotosensitivityLevel::Low:
    return base * settings_.maxBloomIntensity;
  case PhotosensitivityLevel::Medium:
    return base * settings_.maxBloomIntensity * 0.5f;
  case PhotosensitivityLevel::High:
    return base * settings_.maxBloomIntensity * 0.25f;
  case PhotosensitivityLevel::Maximum:
    return 0.0f;
  }
  return base;
}

float SettingsManager::getEffectiveAnimationSpeed() const {
  if (settings_.reduceMotion) {
    return settings_.animationSpeed * 0.1f;
  }
  return settings_.animationSpeed;
}

const char *colorblindModeToString(ColorblindMode mode) {
  switch (mode) {
  case ColorblindMode::None:
    return "none";
  case ColorblindMode::Protanopia:
    return "protanopia";
  case ColorblindMode::Deuteranopia:
    return "deuteranopia";
  case ColorblindMode::Tritanopia:
    return "tritanopia";
  case ColorblindMode::Achromatopsia:
    return "achromatopsia";
  default:
    return "none";
  }
}

ColorblindMode stringToColorblindMode(const std::string &str) {
  if (str == "protanopia")
    return ColorblindMode::Protanopia;
  if (str == "deuteranopia")
    return ColorblindMode::Deuteranopia;
  if (str == "tritanopia")
    return ColorblindMode::Tritanopia;
  if (str == "achromatopsia")
    return ColorblindMode::Achromatopsia;
  return ColorblindMode::None;
}

const char *photosensitivityLevelToString(PhotosensitivityLevel level) {
  switch (level) {
  case PhotosensitivityLevel::None:
    return "none";
  case PhotosensitivityLevel::Low:
    return "low";
  case PhotosensitivityLevel::Medium:
    return "medium";
  case PhotosensitivityLevel::High:
    return "high";
  case PhotosensitivityLevel::Maximum:
    return "maximum";
  default:
    return "medium";
  }
}

PhotosensitivityLevel stringToPhotosensitivityLevel(const std::string &str) {
  if (str == "none")
    return PhotosensitivityLevel::None;
  if (str == "low")
    return PhotosensitivityLevel::Low;
  if (str == "medium")
    return PhotosensitivityLevel::Medium;
  if (str == "high")
    return PhotosensitivityLevel::High;
  if (str == "maximum")
    return PhotosensitivityLevel::Maximum;
  return PhotosensitivityLevel::Medium;
}
