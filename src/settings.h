/**
 * @file settings.h
 * @brief Persistent user settings and singleton manager for the black hole renderer.
 */

#ifndef SETTINGS_H
#define SETTINGS_H

#include <string>

/**
 * @brief User-configurable settings for the core simulation and renderer.
 *
 * All fields correspond to JSON keys written and read by SettingsManager.
 * Defaults represent a sensible out-of-the-box experience at 1920x1080.
 */
/// Default camera pose: 75 r_s from the hole (scene units, r_s = 2), outside
/// the disk's BH_DISK_OUTER_RADIUS_RS = 20 r_s outer edge, and 5 degrees above
/// the disk plane, where the thin disk reads as a band across the shadow, its
/// far side lenses into an arc over the shadow and its underside into an arc
/// below it, and the lensed star field rings the hole. A settings file at the
/// current K_PRESENTATION_SCHEMA_VERSION keeps its saved camera.
inline constexpr float K_DEFAULT_CAMERA_DISTANCE = 150.0f;
inline constexpr float K_DEFAULT_CAMERA_PITCH_DEG = 5.0f;

/// Tone-map exposure of fresh settings at the default camera, the volumetric
/// disk (RendererContract), diskBrightness 0.25, and gamma 2.5. The raw disk's
/// 99th-percentile luminance L99 there is 0.70 on NVIDIA GL, so the record
/// exposure rule (render/record_mode.h) would give ACES^-1(0.9^2.5) / 0.70 =
/// 1.2. Exposure 2.5 instead puts L99 at display 0.96 and keeps the Doppler
/// asymmetry visible: the 90th-percentile disk luminance of the approaching
/// third of the frame displays 1.21 times that of the receding third (raw
/// ratio 1.77). Above about 4 the ACES shoulder compresses the display ratio
/// toward 1.1 and the inner disk clips to white.
inline constexpr float K_DEFAULT_TONE_EXPOSURE = 2.5f;

/// Version of the presentation defaults: camera pose, sky, and exposure. A
/// settings file written at an older version (or with no
/// presentationSchemaVersion key) takes those fields from fresh Settings once
/// on load and keeps every other saved field. Bump it whenever a default below
/// changes how a fresh frame looks.
inline constexpr int K_PRESENTATION_SCHEMA_VERSION = 2;

/// Background intensity of fresh settings: the rule's sky target at
/// K_DEFAULT_TONE_EXPOSURE for the default backdrop (jwst_carina_cosmic_cliffs,
/// off by default so the star-field cubemap shows). Its raw 99th-percentile
/// luminance is 0.347 at intensity 1 above the disk from the default camera,
/// linear in the intensity, and ACES^-1(0.8^2.5) / (2.5 * 0.347) =
/// 0.438 / 0.868 = 0.50 puts it at display 0.8.
inline constexpr float K_DEFAULT_BACKGROUND_INTENSITY = 0.5f;

struct Settings {
  int workspaceSchemaVersion = 0;
  int presentationSchemaVersion = K_PRESENTATION_SCHEMA_VERSION;
  int workspaceKind = 0;
  bool advancedControls = false;
  // === DISPLAY ===
  int windowWidth = 1920;
  int windowHeight = 1080;
  bool fullscreen = false;
  int swapInterval = 1; // 0=off, 1=vsync, 2=triple (driver dependent)
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
  int gamepadYawAxis = 2;        // GLFW_GAMEPAD_AXIS_RIGHT_X
  int gamepadPitchAxis = 3;      // GLFW_GAMEPAD_AXIS_RIGHT_Y
  int gamepadRollAxis = 0;       // GLFW_GAMEPAD_AXIS_LEFT_X
  int gamepadZoomAxis = 1;       // GLFW_GAMEPAD_AXIS_LEFT_Y
  int gamepadZoomInAxis = 5;     // GLFW_GAMEPAD_AXIS_RIGHT_TRIGGER
  int gamepadZoomOutAxis = 4;    // GLFW_GAMEPAD_AXIS_LEFT_TRIGGER
  int gamepadResetButton = 3;    // GLFW_GAMEPAD_BUTTON_Y
  int gamepadPauseButton = 7;    // GLFW_GAMEPAD_BUTTON_START
  int gamepadToggleUIButton = 6; // GLFW_GAMEPAD_BUTTON_BACK

  // === RENDERING ===
  bool tonemappingEnabled = true;
  float toneExposure = K_DEFAULT_TONE_EXPOSURE;
  float bloomStrength = 0.1f;
  int bloomIterations = 8;

  // === BACKGROUND ===
  // The equirect backdrop is off by default: the star-field cubemap is the sky.
  // A sky at infinity has no parallax, so parallax and drift start at zero.
  bool backgroundEnabled = false;
  std::string backgroundId = "jwst_carina_cosmic_cliffs";
  float backgroundIntensity = K_DEFAULT_BACKGROUND_INTENSITY;
  float backgroundParallaxStrength = 0.0f;
  float backgroundDriftStrength = 0.0f;

  // === CAMERA ===
  float cameraYaw = 0.0f;
  float cameraPitch = K_DEFAULT_CAMERA_PITCH_DEG;
  float cameraRoll = 0.0f;
  float cameraDistance = K_DEFAULT_CAMERA_DISTANCE;
  int cameraMode = 0; // 0=Input, 1=Front, 2=Top, 3=Orbit
  float orbitRadius = 15.0f;
  float orbitSpeed = 6.0f; // Degrees per second

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

/**
 * @brief Singleton that owns the active Settings instance and handles JSON persistence.
 *
 * Use SettingsManager::instance() to obtain the global object.  Call load() once
 * at startup and save() before exit (or whenever a setting changes) to persist
 * user preferences across sessions.
 */
class SettingsManager {
public:
  /** @brief Returns the process-wide singleton instance. */
  static SettingsManager &instance();

  /**
   * @brief Loads settings from a JSON file, leaving defaults for missing keys.
   * @param filepath Path to the JSON settings file.
   * @return true on success; false if the file could not be opened.
   */
  bool load(const std::string &filepath = "settings.json");

  /**
   * @brief Serialises the current settings to a JSON file.
   * @param filepath Destination path for the JSON settings file.
   * @return true on success; false if the file could not be created.
   */
  bool save(const std::string &filepath = "settings.json");

  /** @brief Prevents settings file writes during isolated captures. */
  void setPersistenceEnabled(bool enabled) { persistenceEnabled_ = enabled; }

  /** @brief Resets all settings to their compiled-in defaults. */
  void resetToDefaults();

  /** @brief Returns a mutable reference to the active settings. */
  Settings &get() { return settings_; }
  /** @brief Returns a read-only reference to the active settings. */
  [[nodiscard]] const Settings &get() const { return settings_; }

  SettingsManager(const SettingsManager &) = delete;
  SettingsManager &operator=(const SettingsManager &) = delete;

private:
  SettingsManager() = default;
  ~SettingsManager() = default;

  Settings settings_;
  std::string lastFilepath_;
  bool persistenceEnabled_ = true;
};

#endif // SETTINGS_H
