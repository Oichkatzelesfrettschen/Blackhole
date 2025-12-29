#ifndef SETTINGS_H
#define SETTINGS_H

#include <string>

// Colorblind filter types based on research from:
// https://www.inf.ufrgs.br/~oliveira/pubs_files/CVD_Simulation/CVD_Simulation.html
enum class ColorblindMode {
  None = 0,
  Protanopia,    // Red-blind (~1% of males)
  Deuteranopia,  // Green-blind (~1% of males)
  Tritanopia,    // Blue-blind (~0.003% of population)
  Achromatopsia, // Complete color blindness (monochromacy)
  COUNT
};

// Photosensitivity protection levels per WCAG 2.3.1
// https://www.w3.org/TR/WCAG22/#seizures-and-physical-reactions
enum class PhotosensitivityLevel {
  None = 0,        // No protection (user acknowledged warning)
  Low,             // Reduce bloom intensity by 50%
  Medium,          // Reduce bloom intensity by 75%, limit flash frequency
  High,            // Minimal bloom, aggressive flash limiting
  Maximum          // Disable all flashing effects entirely
};

// All user-configurable settings
struct Settings {
  // === DISPLAY ===
  int windowWidth = 1920;
  int windowHeight = 1080;
  bool fullscreen = false;
  bool vsync = true;
  float gamma = 2.5f;

  // === ACCESSIBILITY - VISION ===
  ColorblindMode colorblindMode = ColorblindMode::None;
  float colorblindStrength = 1.0f;  // 0.0 = off, 1.0 = full simulation/correction
  bool highContrastUI = false;
  bool invertColors = false;
  float uiFontScale = 1.0f;         // 0.75 - 2.0

  // === ACCESSIBILITY - PHOTOSENSITIVITY ===
  PhotosensitivityLevel photosensitivityLevel = PhotosensitivityLevel::Medium;
  bool photosensitivityWarningShown = false;
  float maxBloomIntensity = 0.5f;   // 0.0 - 1.0, clamped in shader
  float maxFlashFrequency = 2.0f;   // Max flashes per second (WCAG says <3)
  bool reduceMotion = false;        // Slows/disables animations

  // === ACCESSIBILITY - STEREOBLINDNESS (Depth Perception) ===
  // For users who cannot perceive stereoscopic depth (~4-7% of population)
  bool stereoblindModeEnabled = false;  // Master toggle for depth cue enhancements
  bool depthFogEnabled = false;         // Atmospheric perspective fog
  float depthFogDensity = 0.3f;         // 0.0 - 1.0
  float depthFogR = 0.1f;               // Fog color RGB
  float depthFogG = 0.1f;
  float depthFogB = 0.15f;
  bool depthEdgeOutlines = false;       // Edge detection outlines
  float depthEdgeThreshold = 0.5f;      // 0.0 - 1.0
  float depthEdgeR = 1.0f;              // Edge color RGB
  float depthEdgeG = 1.0f;
  float depthEdgeB = 1.0f;
  bool depthDesaturation = false;       // Distant objects desaturate
  float depthDesatStrength = 0.5f;      // 0.0 - 1.0
  bool chromaDepthEnabled = false;      // Warm near, cool far color shift

  // === ACCESSIBILITY - MOTOR ===
  bool holdToToggleCamera = false;  // Toggle instead of hold for camera controls
  bool holdToToggleUI = false;      // Toggle instead of hold for UI interactions
  float mouseSensitivity = 1.0f;    // 0.1 - 3.0
  float keyboardSensitivity = 1.0f; // 0.1 - 3.0
  float scrollSensitivity = 1.0f;   // 0.1 - 3.0
  bool invertMouseX = false;
  bool invertMouseY = false;
  bool invertKeyboardX = false;
  bool invertKeyboardY = false;

  // === ACCESSIBILITY - COGNITIVE ===
  bool showControlHints = true;     // Show keyboard shortcuts on screen
  float animationSpeed = 1.0f;      // Global animation speed multiplier
  float timeScale = 1.0f;           // Simulation time scale (for pause: 0.0)

  // === CONTROLS - KEY BINDINGS ===
  int keyQuit = 256;                // GLFW_KEY_ESCAPE
  int keyToggleUI = 72;             // GLFW_KEY_H
  int keyToggleFullscreen = 300;    // GLFW_KEY_F11
  int keyResetCamera = 82;          // GLFW_KEY_R
  int keyPause = 80;                // GLFW_KEY_P
  int keyCameraForward = 87;        // GLFW_KEY_W
  int keyCameraBackward = 83;       // GLFW_KEY_S
  int keyCameraLeft = 65;           // GLFW_KEY_A
  int keyCameraRight = 68;          // GLFW_KEY_D
  int keyCameraUp = 69;             // GLFW_KEY_E
  int keyCameraDown = 81;           // GLFW_KEY_Q
  int keyCameraRollLeft = 90;       // GLFW_KEY_Z
  int keyCameraRollRight = 67;      // GLFW_KEY_C
  int keyZoomIn = 61;               // GLFW_KEY_EQUAL (+)
  int keyZoomOut = 45;              // GLFW_KEY_MINUS (-)
  int keyAccessibilityMenu = 290;   // GLFW_KEY_F1

  // === RENDERING ===
  bool tonemappingEnabled = true;
  float bloomStrength = 0.1f;
  int bloomIterations = 8;

  // === CAMERA ===
  float cameraYaw = 0.0f;
  float cameraPitch = 0.0f;
  float cameraRoll = 0.0f;
  float cameraDistance = 5.0f;

  // === BLACK HOLE PARAMETERS ===
  bool gravitationalLensing = true;
  bool renderBlackHole = true;
  bool mouseControl = true;
  bool adiskEnabled = true;
  bool adiskParticle = true;
  float adiskDensityV = 2.0f;
  float adiskDensityH = 4.0f;
  float adiskHeight = 0.55f;
  float adiskLit = 0.25f;
  float adiskNoiseLOD = 5.0f;
  float adiskNoiseScale = 0.8f;
  float adiskSpeed = 0.5f;
};

class SettingsManager {
public:
  static SettingsManager &instance();

  // Load settings from file (returns false if file doesn't exist)
  bool load(const std::string &filepath = "settings.json");

  // Save settings to file
  bool save(const std::string &filepath = "settings.json");

  // Reset to defaults
  void resetToDefaults();

  // Access settings
  Settings &get() { return settings_; }
  const Settings &get() const { return settings_; }

  // Convenience accessors
  bool isPhotosensitivityProtectionEnabled() const {
    return settings_.photosensitivityLevel != PhotosensitivityLevel::None;
  }

  bool isColorblindFilterEnabled() const {
    return settings_.colorblindMode != ColorblindMode::None;
  }

  float getEffectiveBloomStrength() const;
  float getEffectiveAnimationSpeed() const;

private:
  SettingsManager() = default;
  ~SettingsManager() = default;
  SettingsManager(const SettingsManager &) = delete;
  SettingsManager &operator=(const SettingsManager &) = delete;

  Settings settings_;
  std::string lastFilepath_;
};

// String conversion utilities for enums
const char *colorblindModeToString(ColorblindMode mode);
ColorblindMode stringToColorblindMode(const std::string &str);
const char *photosensitivityLevelToString(PhotosensitivityLevel level);
PhotosensitivityLevel stringToPhotosensitivityLevel(const std::string &str);

#endif // SETTINGS_H
