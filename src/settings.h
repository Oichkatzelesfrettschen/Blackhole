#ifndef SETTINGS_H
#define SETTINGS_H

#include <string>

// User-configurable settings (core simulation only)
struct Settings {
  // === DISPLAY ===
  int windowWidth = 1920;
  int windowHeight = 1080;
  bool fullscreen = false;
  int swapInterval = 1;         // 0=off, 1=vsync, 2=triple (driver dependent)
  float renderScale = 1.0f;
  float gamma = 2.5f;

  // === CONTROLS ===
  float mouseSensitivity = 1.0f;
  float keyboardSensitivity = 1.0f;
  float scrollSensitivity = 1.0f;
  bool invertMouseX = false;
  bool invertMouseY = false;
  bool invertKeyboardX = false;
  bool invertKeyboardY = false;
  bool holdToToggleCamera = false;
  float timeScale = 1.0f;

  // === KEY BINDINGS ===
  int keyQuit = 256;             // GLFW_KEY_ESCAPE
  int keyToggleUI = 72;          // GLFW_KEY_H
  int keyToggleFullscreen = 300; // GLFW_KEY_F11
  int keyResetCamera = 82;       // GLFW_KEY_R
  int keyResetSettings = 259;    // GLFW_KEY_BACKSPACE
  int keyPause = 80;             // GLFW_KEY_P
  int keyCameraForward = 87;     // GLFW_KEY_W
  int keyCameraBackward = 83;    // GLFW_KEY_S
  int keyCameraLeft = 65;        // GLFW_KEY_A
  int keyCameraRight = 68;       // GLFW_KEY_D
  int keyCameraUp = 69;          // GLFW_KEY_E
  int keyCameraDown = 81;        // GLFW_KEY_Q
  int keyCameraRollLeft = 90;    // GLFW_KEY_Z
  int keyCameraRollRight = 67;   // GLFW_KEY_C
  int keyZoomIn = 61;            // GLFW_KEY_EQUAL (+)
  int keyZoomOut = 45;           // GLFW_KEY_MINUS (-)
  int keyIncreaseFontSize = 293; // GLFW_KEY_F4
  int keyDecreaseFontSize = 294; // GLFW_KEY_F5
  int keyIncreaseTimeScale = 93; // GLFW_KEY_RIGHT_BRACKET
  int keyDecreaseTimeScale = 91; // GLFW_KEY_LEFT_BRACKET

  // === GAMEPAD CONTROLS ===
  bool gamepadEnabled = true;
  float gamepadDeadzone = 0.15f;
  float gamepadLookSensitivity = 90.0f;
  float gamepadRollSensitivity = 90.0f;
  float gamepadZoomSensitivity = 6.0f;
  float gamepadTriggerZoomSensitivity = 8.0f;
  bool gamepadInvertX = false;
  bool gamepadInvertY = false;
  bool gamepadInvertRoll = false;
  bool gamepadInvertZoom = false;
  int gamepadYawAxis = 2;         // GLFW_GAMEPAD_AXIS_RIGHT_X
  int gamepadPitchAxis = 3;       // GLFW_GAMEPAD_AXIS_RIGHT_Y
  int gamepadRollAxis = 0;        // GLFW_GAMEPAD_AXIS_LEFT_X
  int gamepadZoomAxis = 1;        // GLFW_GAMEPAD_AXIS_LEFT_Y
  int gamepadZoomInAxis = 5;      // GLFW_GAMEPAD_AXIS_RIGHT_TRIGGER
  int gamepadZoomOutAxis = 4;     // GLFW_GAMEPAD_AXIS_LEFT_TRIGGER
  int gamepadResetButton = 3;     // GLFW_GAMEPAD_BUTTON_Y
  int gamepadPauseButton = 7;     // GLFW_GAMEPAD_BUTTON_START
  int gamepadToggleUIButton = 6;  // GLFW_GAMEPAD_BUTTON_BACK

  // === RENDERING ===
  bool tonemappingEnabled = true;
  float bloomStrength = 0.1f;
  int bloomIterations = 8;

  // === BACKGROUND ===
  bool backgroundEnabled = true;
  std::string backgroundId = "nasa_pia22085";
  float backgroundIntensity = 1.0f;
  float backgroundParallaxStrength = 0.0006f;
  float backgroundDriftStrength = 0.01f;

  // === CAMERA ===
  float cameraYaw = 0.0f;
  float cameraPitch = 0.0f;
  float cameraRoll = 0.0f;
  float cameraDistance = 15.0f;
  int cameraMode = 0;          // 0=Input, 1=Front, 2=Top, 3=Orbit
  float orbitRadius = 15.0f;
  float orbitSpeed = 6.0f;     // Degrees per second

  // === BLACK HOLE PARAMETERS ===
  bool gravitationalLensing = true;
  bool renderBlackHole = true;
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

private:
  SettingsManager() = default;
  ~SettingsManager() = default;
  SettingsManager(const SettingsManager &) = delete;
  SettingsManager &operator=(const SettingsManager &) = delete;

  Settings settings_;
  std::string lastFilepath_;
};

#endif // SETTINGS_H
