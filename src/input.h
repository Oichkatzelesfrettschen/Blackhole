#ifndef INPUT_H
#define INPUT_H

#include <GLFW/glfw3.h>
#include <functional>
#include <map>
#include <string>

// Forward declaration
struct Settings;

// Key action identifiers for remapping
enum class KeyAction {
  Quit,
  ToggleUI,
  ToggleFullscreen,
  ResetCamera,
  ResetSettings,
  Pause,
  CameraMoveForward,
  CameraMoveBackward,
  CameraMoveLeft,
  CameraMoveRight,
  CameraMoveUp,
  CameraMoveDown,
  CameraRollLeft,
  CameraRollRight,
  ZoomIn,
  ZoomOut,
  IncreaseFontSize,
  DecreaseFontSize,
  IncreaseTimeScale,
  DecreaseTimeScale,
  COUNT
};

struct CameraState {
  float yaw = 0.0f;
  float pitch = 0.0f;
  float roll = 0.0f;
  float distance = 15.0f;
  float fov = 45.0f;

  void reset() {
    yaw = 0.0f;
    pitch = 0.0f;
    roll = 0.0f;
    distance = 15.0f;
    fov = 45.0f;
  }
};

// Hold-to-toggle state for each camera action
struct HoldToggleState {
  bool forward = false;
  bool backward = false;
  bool left = false;
  bool right = false;
  bool up = false;
  bool down = false;
  bool rollLeft = false;
  bool rollRight = false;
  bool zoomIn = false;
  bool zoomOut = false;

  void reset() {
    forward = backward = left = right = false;
    up = down = rollLeft = rollRight = false;
    zoomIn = zoomOut = false;
  }
};

class InputManager {
public:
  static InputManager &instance();

  void init(GLFWwindow *window);
  void update(float deltaTime);
  void shutdown();

  // Sync with settings
  void syncFromSettings();
  void syncToSettings();

  // Keyboard state
  [[nodiscard]] bool isKeyPressed(int key) const;
  [[nodiscard]] bool isKeyJustPressed(int key) const;
  [[nodiscard]] bool isKeyJustReleased(int key) const;

  // Mouse state
  [[nodiscard]] bool isMouseButtonPressed(int button) const;
  [[nodiscard]] bool isMouseButtonJustPressed(int button) const;
  [[nodiscard]] float getMouseX() const { return mouseX_; }
  [[nodiscard]] float getMouseY() const { return mouseY_; }
  [[nodiscard]] float getMouseDeltaX() const { return mouseDeltaX_; }
  [[nodiscard]] float getMouseDeltaY() const { return mouseDeltaY_; }
  [[nodiscard]] float getScrollDelta() const { return scrollDelta_; }

  // Action bindings
  [[nodiscard]] bool isActionPressed(KeyAction action) const;
  [[nodiscard]] bool isActionJustPressed(KeyAction action) const;
  [[nodiscard]] int getKeyForAction(KeyAction action) const;
  void setKeyForAction(KeyAction action, int key);
  [[nodiscard]] static std::string getKeyName(int key);
  [[nodiscard]] static const char *getActionName(KeyAction action);

  // UI state
  [[nodiscard]] bool isUIVisible() const { return uiVisible_; }
  void setUIVisible(bool visible) { uiVisible_ = visible; }
  void toggleUI() { uiVisible_ = !uiVisible_; }

  // Fullscreen
  [[nodiscard]] bool isFullscreen() const { return fullscreen_; }
  void toggleFullscreen();

  // Pause state
  [[nodiscard]] bool isPaused() const { return paused_; }
  void setPaused(bool paused) { paused_ = paused; }
  void togglePause() { paused_ = !paused_; }

  // Time scale (0.0 = frozen, 1.0 = normal, 2.0 = 2x speed)
  [[nodiscard]] float getTimeScale() const { return timeScale_; }
  void setTimeScale(float scale) { timeScale_ = scale; }

  // Camera
  CameraState &camera() { return camera_; }
  [[nodiscard]] const CameraState &camera() const { return camera_; }

  // Sensitivity settings
  [[nodiscard]] float getMouseSensitivity() const { return mouseSensitivity_; }
  void setMouseSensitivity(float sens) { mouseSensitivity_ = sens; }
  [[nodiscard]] float getKeyboardSensitivity() const { return keyboardSensitivity_; }
  void setKeyboardSensitivity(float sens) { keyboardSensitivity_ = sens; }
  [[nodiscard]] float getScrollSensitivity() const { return scrollSensitivity_; }
  void setScrollSensitivity(float sens) { scrollSensitivity_ = sens; }

  // Axis inversion
  [[nodiscard]] bool isMouseXInverted() const { return invertMouseX_; }
  void setMouseXInverted(bool inv) { invertMouseX_ = inv; }
  [[nodiscard]] bool isMouseYInverted() const { return invertMouseY_; }
  void setMouseYInverted(bool inv) { invertMouseY_ = inv; }
  [[nodiscard]] bool isKeyboardXInverted() const { return invertKeyboardX_; }
  void setKeyboardXInverted(bool inv) { invertKeyboardX_ = inv; }
  [[nodiscard]] bool isKeyboardYInverted() const { return invertKeyboardY_; }
  void setKeyboardYInverted(bool inv) { invertKeyboardY_ = inv; }

  // Hold-to-toggle mode
  [[nodiscard]] bool isHoldToToggleCamera() const { return holdToToggleCamera_; }
  void setHoldToToggleCamera(bool enabled) { holdToToggleCamera_ = enabled; }
  HoldToggleState &holdToggleState() { return holdToggleState_; }

  // Gamepad settings
  [[nodiscard]] bool isGamepadEnabled() const { return gamepadEnabled_; }
  void setGamepadEnabled(bool enabled) { gamepadEnabled_ = enabled; }
  [[nodiscard]] float getGamepadDeadzone() const { return gamepadDeadzone_; }
  void setGamepadDeadzone(float deadzone) { gamepadDeadzone_ = deadzone; }
  [[nodiscard]] float getGamepadLookSensitivity() const { return gamepadLookSensitivity_; }
  void setGamepadLookSensitivity(float sens) { gamepadLookSensitivity_ = sens; }
  [[nodiscard]] float getGamepadRollSensitivity() const { return gamepadRollSensitivity_; }
  void setGamepadRollSensitivity(float sens) { gamepadRollSensitivity_ = sens; }
  [[nodiscard]] float getGamepadZoomSensitivity() const { return gamepadZoomSensitivity_; }
  void setGamepadZoomSensitivity(float sens) { gamepadZoomSensitivity_ = sens; }
  [[nodiscard]] float getGamepadTriggerZoomSensitivity() const {
    return gamepadTriggerZoomSensitivity_;
  }
  void setGamepadTriggerZoomSensitivity(float sens) { gamepadTriggerZoomSensitivity_ = sens; }
  [[nodiscard]] bool isGamepadXInverted() const { return gamepadInvertX_; }
  void setGamepadXInverted(bool inv) { gamepadInvertX_ = inv; }
  [[nodiscard]] bool isGamepadYInverted() const { return gamepadInvertY_; }
  void setGamepadYInverted(bool inv) { gamepadInvertY_ = inv; }
  [[nodiscard]] bool isGamepadRollInverted() const { return gamepadInvertRoll_; }
  void setGamepadRollInverted(bool inv) { gamepadInvertRoll_ = inv; }
  [[nodiscard]] bool isGamepadZoomInverted() const { return gamepadInvertZoom_; }
  void setGamepadZoomInverted(bool inv) { gamepadInvertZoom_ = inv; }
  [[nodiscard]] int getGamepadYawAxis() const { return gamepadYawAxis_; }
  void setGamepadYawAxis(int axis) { gamepadYawAxis_ = axis; }
  [[nodiscard]] int getGamepadPitchAxis() const { return gamepadPitchAxis_; }
  void setGamepadPitchAxis(int axis) { gamepadPitchAxis_ = axis; }
  [[nodiscard]] int getGamepadRollAxis() const { return gamepadRollAxis_; }
  void setGamepadRollAxis(int axis) { gamepadRollAxis_ = axis; }
  [[nodiscard]] int getGamepadZoomAxis() const { return gamepadZoomAxis_; }
  void setGamepadZoomAxis(int axis) { gamepadZoomAxis_ = axis; }
  [[nodiscard]] int getGamepadZoomInAxis() const { return gamepadZoomInAxis_; }
  void setGamepadZoomInAxis(int axis) { gamepadZoomInAxis_ = axis; }
  [[nodiscard]] int getGamepadZoomOutAxis() const { return gamepadZoomOutAxis_; }
  void setGamepadZoomOutAxis(int axis) { gamepadZoomOutAxis_ = axis; }
  [[nodiscard]] int getGamepadResetButton() const { return gamepadResetButton_; }
  void setGamepadResetButton(int button) { gamepadResetButton_ = button; }
  [[nodiscard]] int getGamepadPauseButton() const { return gamepadPauseButton_; }
  void setGamepadPauseButton(int button) { gamepadPauseButton_ = button; }
  [[nodiscard]] int getGamepadToggleUIButton() const { return gamepadToggleUIButton_; }
  void setGamepadToggleUIButton(int button) { gamepadToggleUIButton_ = button; }
  [[nodiscard]] float getGamepadAxisRaw(int axis) const;
  [[nodiscard]] float getGamepadAxisFiltered(int axis) const;
  [[nodiscard]] static bool isGamepadConnected();

  // Key remapping mode
  [[nodiscard]] bool isRemappingKey() const { return remappingAction_ != KeyAction::COUNT; }
  [[nodiscard]] KeyAction getRemappingAction() const { return remappingAction_; }
  void startKeyRemapping(KeyAction action) { remappingAction_ = action; }
  void cancelKeyRemapping() { remappingAction_ = KeyAction::COUNT; }

  // Callbacks (called from GLFW callbacks)
  void onKey(int key, int scancode, int action, int mods);
  void onMouseButton(int button, int action, int mods);
  void onMouseMove(double x, double y);
  void onScroll(double xoffset, double yoffset);

  // Effective delta time (accounts for pause and time scale)
  [[nodiscard]] float getEffectiveDeltaTime(float rawDeltaTime) const;

  // Override GUI capture (for Viewport interaction)
  void setIgnoreGuiCapture(bool ignore) { ignoreGuiCapture_ = ignore; }

  InputManager(const InputManager &) = delete;
  InputManager &operator=(const InputManager &) = delete;

private:
  InputManager() = default;
  ~InputManager() = default;

  void initDefaultBindings();
  void updateCamera(float deltaTime);
  void handleHoldToToggle(KeyAction action, bool justPressed, bool justReleased);
  void updateGamepad(float deltaTime);
  [[nodiscard]] bool isGamepadButtonJustPressed(int button) const;

  GLFWwindow *window_ = nullptr;

  // Keyboard state
  bool keyState_[GLFW_KEY_LAST + 1] = {};
  bool prevKeyState_[GLFW_KEY_LAST + 1] = {};

  // Mouse state
  bool mouseButtonState_[GLFW_MOUSE_BUTTON_LAST + 1] = {};
  bool prevMouseButtonState_[GLFW_MOUSE_BUTTON_LAST + 1] = {};
  float mouseX_ = 0.0f;
  float mouseY_ = 0.0f;
  float prevMouseX_ = 0.0f;
  float prevMouseY_ = 0.0f;
  float mouseDeltaX_ = 0.0f;
  float mouseDeltaY_ = 0.0f;
  float scrollDelta_ = 0.0f;
  bool firstMouse_ = true;

  // Key bindings
  std::map<KeyAction, int> keyBindings_;

  // Key remapping
  KeyAction remappingAction_ = KeyAction::COUNT;

  // State
  bool ignoreGuiCapture_ = false;  // Ignore GUI input capture (for debugging)
  bool uiVisible_ = true;          // UI visible on startup (set false for perf benchmarking)
  bool fullscreen_ = false;
  bool paused_ = false;
  float timeScale_ = 1.0f;
  int windowedX_ = 0;
  int windowedY_ = 0;
  int windowedWidth_ = 0;
  int windowedHeight_ = 0;

  // Camera
  CameraState camera_;
  float cameraMoveSpeed_ = 2.0f;
  float cameraRotateSpeed_ = 60.0f;

  // Sensitivity (base values, multiplied by settings)
  float mouseSensitivity_ = 1.0f;
  float keyboardSensitivity_ = 1.0f;
  float scrollSensitivity_ = 1.0f;

  // Axis inversion
  bool invertMouseX_ = false;
  bool invertMouseY_ = false;
  bool invertKeyboardX_ = false;
  bool invertKeyboardY_ = false;

  // Hold-to-toggle
  bool holdToToggleCamera_ = false;
  HoldToggleState holdToggleState_;

  // Gamepad config
  bool gamepadEnabled_ = true;
  float gamepadDeadzone_ = 0.15f;
  float gamepadLookSensitivity_ = 90.0f;
  float gamepadRollSensitivity_ = 90.0f;
  float gamepadZoomSensitivity_ = 6.0f;
  float gamepadTriggerZoomSensitivity_ = 8.0f;
  bool gamepadInvertX_ = false;
  bool gamepadInvertY_ = false;
  bool gamepadInvertRoll_ = false;
  bool gamepadInvertZoom_ = false;
  int gamepadYawAxis_ = 2;     // GLFW_GAMEPAD_AXIS_RIGHT_X
  int gamepadPitchAxis_ = 3;   // GLFW_GAMEPAD_AXIS_RIGHT_Y
  int gamepadRollAxis_ = 0;    // GLFW_GAMEPAD_AXIS_LEFT_X
  int gamepadZoomAxis_ = 1;    // GLFW_GAMEPAD_AXIS_LEFT_Y
  int gamepadZoomInAxis_ = 5;  // GLFW_GAMEPAD_AXIS_RIGHT_TRIGGER
  int gamepadZoomOutAxis_ = 4; // GLFW_GAMEPAD_AXIS_LEFT_TRIGGER
  int gamepadResetButton_ = 3;   // GLFW_GAMEPAD_BUTTON_Y
  int gamepadPauseButton_ = 7;   // GLFW_GAMEPAD_BUTTON_START
  int gamepadToggleUIButton_ = 6; // GLFW_GAMEPAD_BUTTON_BACK
  float gamepadAxisRaw_[GLFW_GAMEPAD_AXIS_LAST + 1] = {};
  float gamepadAxisFiltered_[GLFW_GAMEPAD_AXIS_LAST + 1] = {};
  bool gamepadButtonState_[GLFW_GAMEPAD_BUTTON_LAST + 1] = {};
  bool prevGamepadButtonState_[GLFW_GAMEPAD_BUTTON_LAST + 1] = {};
};

#endif // INPUT_H
