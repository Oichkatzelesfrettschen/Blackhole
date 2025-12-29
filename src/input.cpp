#include "input.h"
#include "settings.h"

#include <algorithm>
#include <cmath>

#include <imgui.h>

InputManager &InputManager::instance() {
  static InputManager instance;
  return instance;
}

void InputManager::init(GLFWwindow *window) {
  window_ = window;
  initDefaultBindings();

  // Store initial window position/size for fullscreen toggle
  glfwGetWindowPos(window_, &windowedX_, &windowedY_);
  glfwGetWindowSize(window_, &windowedWidth_, &windowedHeight_);

  // Initialize mouse position
  double mx, my;
  glfwGetCursorPos(window_, &mx, &my);
  mouseX_ = static_cast<float>(mx);
  mouseY_ = static_cast<float>(my);
  prevMouseX_ = mouseX_;
  prevMouseY_ = mouseY_;

  // Sync from settings if available
  syncFromSettings();
}

void InputManager::initDefaultBindings() {
  // Core controls
  keyBindings_[KeyAction::Quit] = GLFW_KEY_ESCAPE;
  keyBindings_[KeyAction::ToggleUI] = GLFW_KEY_H;
  keyBindings_[KeyAction::ToggleFullscreen] = GLFW_KEY_F11;
  keyBindings_[KeyAction::ResetCamera] = GLFW_KEY_R;
  keyBindings_[KeyAction::ResetSettings] = GLFW_KEY_BACKSPACE;
  keyBindings_[KeyAction::Pause] = GLFW_KEY_P;

  // Camera movement (WASD + QE for up/down)
  keyBindings_[KeyAction::CameraMoveForward] = GLFW_KEY_W;
  keyBindings_[KeyAction::CameraMoveBackward] = GLFW_KEY_S;
  keyBindings_[KeyAction::CameraMoveLeft] = GLFW_KEY_A;
  keyBindings_[KeyAction::CameraMoveRight] = GLFW_KEY_D;
  keyBindings_[KeyAction::CameraMoveUp] = GLFW_KEY_E;
  keyBindings_[KeyAction::CameraMoveDown] = GLFW_KEY_Q;

  // Camera roll
  keyBindings_[KeyAction::CameraRollLeft] = GLFW_KEY_Z;
  keyBindings_[KeyAction::CameraRollRight] = GLFW_KEY_C;

  // Zoom
  keyBindings_[KeyAction::ZoomIn] = GLFW_KEY_EQUAL;  // +/=
  keyBindings_[KeyAction::ZoomOut] = GLFW_KEY_MINUS; // -

  // Accessibility
  keyBindings_[KeyAction::ToggleAccessibility] = GLFW_KEY_F1;
  keyBindings_[KeyAction::ToggleHighContrast] = GLFW_KEY_F2;
  keyBindings_[KeyAction::ToggleReducedMotion] = GLFW_KEY_F3;
  keyBindings_[KeyAction::IncreaseFontSize] = GLFW_KEY_F4;
  keyBindings_[KeyAction::DecreaseFontSize] = GLFW_KEY_F5;
  keyBindings_[KeyAction::CycleColorblindMode] = GLFW_KEY_F6;

  // Time control
  keyBindings_[KeyAction::IncreaseTimeScale] = GLFW_KEY_RIGHT_BRACKET;
  keyBindings_[KeyAction::DecreaseTimeScale] = GLFW_KEY_LEFT_BRACKET;
}

void InputManager::syncFromSettings() {
  auto &settings = SettingsManager::instance().get();

  // Key bindings
  keyBindings_[KeyAction::Quit] = settings.keyQuit;
  keyBindings_[KeyAction::ToggleUI] = settings.keyToggleUI;
  keyBindings_[KeyAction::ToggleFullscreen] = settings.keyToggleFullscreen;
  keyBindings_[KeyAction::ResetCamera] = settings.keyResetCamera;
  keyBindings_[KeyAction::Pause] = settings.keyPause;
  keyBindings_[KeyAction::CameraMoveForward] = settings.keyCameraForward;
  keyBindings_[KeyAction::CameraMoveBackward] = settings.keyCameraBackward;
  keyBindings_[KeyAction::CameraMoveLeft] = settings.keyCameraLeft;
  keyBindings_[KeyAction::CameraMoveRight] = settings.keyCameraRight;
  keyBindings_[KeyAction::CameraMoveUp] = settings.keyCameraUp;
  keyBindings_[KeyAction::CameraMoveDown] = settings.keyCameraDown;
  keyBindings_[KeyAction::CameraRollLeft] = settings.keyCameraRollLeft;
  keyBindings_[KeyAction::CameraRollRight] = settings.keyCameraRollRight;
  keyBindings_[KeyAction::ZoomIn] = settings.keyZoomIn;
  keyBindings_[KeyAction::ZoomOut] = settings.keyZoomOut;
  keyBindings_[KeyAction::ToggleAccessibility] = settings.keyAccessibilityMenu;

  // Motor accessibility
  holdToToggleCamera_ = settings.holdToToggleCamera;
  mouseSensitivity_ = settings.mouseSensitivity;
  keyboardSensitivity_ = settings.keyboardSensitivity;
  scrollSensitivity_ = settings.scrollSensitivity;
  invertMouseX_ = settings.invertMouseX;
  invertMouseY_ = settings.invertMouseY;
  invertKeyboardX_ = settings.invertKeyboardX;
  invertKeyboardY_ = settings.invertKeyboardY;

  // Time
  timeScale_ = settings.timeScale;

  // Camera state
  camera_.yaw = settings.cameraYaw;
  camera_.pitch = settings.cameraPitch;
  camera_.roll = settings.cameraRoll;
  camera_.distance = settings.cameraDistance;
}

void InputManager::syncToSettings() {
  auto &settings = SettingsManager::instance().get();

  // Key bindings
  settings.keyQuit = keyBindings_[KeyAction::Quit];
  settings.keyToggleUI = keyBindings_[KeyAction::ToggleUI];
  settings.keyToggleFullscreen = keyBindings_[KeyAction::ToggleFullscreen];
  settings.keyResetCamera = keyBindings_[KeyAction::ResetCamera];
  settings.keyPause = keyBindings_[KeyAction::Pause];
  settings.keyCameraForward = keyBindings_[KeyAction::CameraMoveForward];
  settings.keyCameraBackward = keyBindings_[KeyAction::CameraMoveBackward];
  settings.keyCameraLeft = keyBindings_[KeyAction::CameraMoveLeft];
  settings.keyCameraRight = keyBindings_[KeyAction::CameraMoveRight];
  settings.keyCameraUp = keyBindings_[KeyAction::CameraMoveUp];
  settings.keyCameraDown = keyBindings_[KeyAction::CameraMoveDown];
  settings.keyCameraRollLeft = keyBindings_[KeyAction::CameraRollLeft];
  settings.keyCameraRollRight = keyBindings_[KeyAction::CameraRollRight];
  settings.keyZoomIn = keyBindings_[KeyAction::ZoomIn];
  settings.keyZoomOut = keyBindings_[KeyAction::ZoomOut];
  settings.keyAccessibilityMenu = keyBindings_[KeyAction::ToggleAccessibility];

  // Motor accessibility
  settings.holdToToggleCamera = holdToToggleCamera_;
  settings.mouseSensitivity = mouseSensitivity_;
  settings.keyboardSensitivity = keyboardSensitivity_;
  settings.scrollSensitivity = scrollSensitivity_;
  settings.invertMouseX = invertMouseX_;
  settings.invertMouseY = invertMouseY_;
  settings.invertKeyboardX = invertKeyboardX_;
  settings.invertKeyboardY = invertKeyboardY_;

  // Time
  settings.timeScale = timeScale_;

  // Camera state
  settings.cameraYaw = camera_.yaw;
  settings.cameraPitch = camera_.pitch;
  settings.cameraRoll = camera_.roll;
  settings.cameraDistance = camera_.distance;
}

void InputManager::update(float deltaTime) {
  // Update previous state
  std::copy(std::begin(keyState_), std::end(keyState_), std::begin(prevKeyState_));
  std::copy(std::begin(mouseButtonState_), std::end(mouseButtonState_),
            std::begin(prevMouseButtonState_));

  // Calculate mouse delta with sensitivity and inversion
  float rawDeltaX = mouseX_ - prevMouseX_;
  float rawDeltaY = mouseY_ - prevMouseY_;

  mouseDeltaX_ = rawDeltaX * mouseSensitivity_ * (invertMouseX_ ? -1.0f : 1.0f);
  mouseDeltaY_ = rawDeltaY * mouseSensitivity_ * (invertMouseY_ ? -1.0f : 1.0f);

  prevMouseX_ = mouseX_;
  prevMouseY_ = mouseY_;

  // Handle single-press actions
  if (isActionJustPressed(KeyAction::Quit)) {
    glfwSetWindowShouldClose(window_, GLFW_TRUE);
  }

  if (isActionJustPressed(KeyAction::ToggleUI)) {
    toggleUI();
  }

  if (isActionJustPressed(KeyAction::ToggleFullscreen)) {
    toggleFullscreen();
  }

  if (isActionJustPressed(KeyAction::ResetCamera)) {
    camera_.reset();
    holdToggleState_.reset();
  }

  if (isActionJustPressed(KeyAction::Pause)) {
    togglePause();
  }

  // Time scale adjustment
  if (isActionJustPressed(KeyAction::IncreaseTimeScale)) {
    timeScale_ = std::min(timeScale_ + 0.25f, 4.0f);
  }
  if (isActionJustPressed(KeyAction::DecreaseTimeScale)) {
    timeScale_ = std::max(timeScale_ - 0.25f, 0.0f);
  }

  // Colorblind mode cycling
  if (isActionJustPressed(KeyAction::CycleColorblindMode)) {
    auto &settings = SettingsManager::instance().get();
    int mode = static_cast<int>(settings.colorblindMode);
    mode = (mode + 1) % static_cast<int>(ColorblindMode::COUNT);
    settings.colorblindMode = static_cast<ColorblindMode>(mode);
  }

  // Hold-to-toggle handling for camera actions
  if (holdToToggleCamera_) {
    handleHoldToToggle(KeyAction::CameraMoveForward, isActionJustPressed(KeyAction::CameraMoveForward),
                       isActionJustPressed(KeyAction::CameraMoveForward));
    handleHoldToToggle(KeyAction::CameraMoveBackward, isActionJustPressed(KeyAction::CameraMoveBackward),
                       isActionJustPressed(KeyAction::CameraMoveBackward));
    handleHoldToToggle(KeyAction::CameraMoveLeft, isActionJustPressed(KeyAction::CameraMoveLeft),
                       isActionJustPressed(KeyAction::CameraMoveLeft));
    handleHoldToToggle(KeyAction::CameraMoveRight, isActionJustPressed(KeyAction::CameraMoveRight),
                       isActionJustPressed(KeyAction::CameraMoveRight));
    handleHoldToToggle(KeyAction::CameraMoveUp, isActionJustPressed(KeyAction::CameraMoveUp),
                       isActionJustPressed(KeyAction::CameraMoveUp));
    handleHoldToToggle(KeyAction::CameraMoveDown, isActionJustPressed(KeyAction::CameraMoveDown),
                       isActionJustPressed(KeyAction::CameraMoveDown));
    handleHoldToToggle(KeyAction::CameraRollLeft, isActionJustPressed(KeyAction::CameraRollLeft),
                       isActionJustPressed(KeyAction::CameraRollLeft));
    handleHoldToToggle(KeyAction::CameraRollRight, isActionJustPressed(KeyAction::CameraRollRight),
                       isActionJustPressed(KeyAction::CameraRollRight));
    handleHoldToToggle(KeyAction::ZoomIn, isActionJustPressed(KeyAction::ZoomIn),
                       isActionJustPressed(KeyAction::ZoomIn));
    handleHoldToToggle(KeyAction::ZoomOut, isActionJustPressed(KeyAction::ZoomOut),
                       isActionJustPressed(KeyAction::ZoomOut));
  }

  // Update camera (only if not paused)
  if (!paused_) {
    updateCamera(deltaTime * timeScale_);
  }

  // Reset scroll delta after processing
  scrollDelta_ = 0.0f;
}

void InputManager::handleHoldToToggle(KeyAction action, bool justPressed, bool /*justReleased*/) {
  if (!justPressed)
    return;

  // Toggle the corresponding state
  switch (action) {
  case KeyAction::CameraMoveForward:
    holdToggleState_.forward = !holdToggleState_.forward;
    break;
  case KeyAction::CameraMoveBackward:
    holdToggleState_.backward = !holdToggleState_.backward;
    break;
  case KeyAction::CameraMoveLeft:
    holdToggleState_.left = !holdToggleState_.left;
    break;
  case KeyAction::CameraMoveRight:
    holdToggleState_.right = !holdToggleState_.right;
    break;
  case KeyAction::CameraMoveUp:
    holdToggleState_.up = !holdToggleState_.up;
    break;
  case KeyAction::CameraMoveDown:
    holdToggleState_.down = !holdToggleState_.down;
    break;
  case KeyAction::CameraRollLeft:
    holdToggleState_.rollLeft = !holdToggleState_.rollLeft;
    break;
  case KeyAction::CameraRollRight:
    holdToggleState_.rollRight = !holdToggleState_.rollRight;
    break;
  case KeyAction::ZoomIn:
    holdToggleState_.zoomIn = !holdToggleState_.zoomIn;
    break;
  case KeyAction::ZoomOut:
    holdToggleState_.zoomOut = !holdToggleState_.zoomOut;
    break;
  default:
    break;
  }
}

void InputManager::updateCamera(float deltaTime) {
  float moveSpeed = cameraMoveSpeed_ * deltaTime * keyboardSensitivity_;
  float rotateSpeed = cameraRotateSpeed_ * deltaTime * keyboardSensitivity_;

  // Apply keyboard axis inversion
  float keyXMult = invertKeyboardX_ ? -1.0f : 1.0f;
  float keyYMult = invertKeyboardY_ ? -1.0f : 1.0f;

  // Determine if action is active (either held or toggled on)
  auto isActive = [this](KeyAction action) {
    if (holdToToggleCamera_) {
      // In toggle mode, check toggle state
      switch (action) {
      case KeyAction::CameraMoveForward:
        return holdToggleState_.forward;
      case KeyAction::CameraMoveBackward:
        return holdToggleState_.backward;
      case KeyAction::CameraMoveLeft:
        return holdToggleState_.left;
      case KeyAction::CameraMoveRight:
        return holdToggleState_.right;
      case KeyAction::CameraMoveUp:
        return holdToggleState_.up;
      case KeyAction::CameraMoveDown:
        return holdToggleState_.down;
      case KeyAction::CameraRollLeft:
        return holdToggleState_.rollLeft;
      case KeyAction::CameraRollRight:
        return holdToggleState_.rollRight;
      case KeyAction::ZoomIn:
        return holdToggleState_.zoomIn;
      case KeyAction::ZoomOut:
        return holdToggleState_.zoomOut;
      default:
        return false;
      }
    } else {
      // In hold mode, check if key is currently pressed
      return isActionPressed(action);
    }
  };

  // Keyboard camera controls (only when UI is not capturing input)
  if (!ImGui::GetIO().WantCaptureKeyboard) {
    // Orbit controls via keyboard
    if (isActive(KeyAction::CameraMoveLeft)) {
      camera_.yaw -= rotateSpeed * keyXMult;
    }
    if (isActive(KeyAction::CameraMoveRight)) {
      camera_.yaw += rotateSpeed * keyXMult;
    }
    if (isActive(KeyAction::CameraMoveForward)) {
      camera_.pitch += rotateSpeed * keyYMult;
    }
    if (isActive(KeyAction::CameraMoveBackward)) {
      camera_.pitch -= rotateSpeed * keyYMult;
    }
    if (isActive(KeyAction::CameraMoveUp)) {
      camera_.distance -= moveSpeed;
    }
    if (isActive(KeyAction::CameraMoveDown)) {
      camera_.distance += moveSpeed;
    }

    // Roll controls
    if (isActive(KeyAction::CameraRollLeft)) {
      camera_.roll -= rotateSpeed;
    }
    if (isActive(KeyAction::CameraRollRight)) {
      camera_.roll += rotateSpeed;
    }

    // Zoom via keyboard
    if (isActive(KeyAction::ZoomIn)) {
      camera_.distance -= moveSpeed;
    }
    if (isActive(KeyAction::ZoomOut)) {
      camera_.distance += moveSpeed;
    }
  }

  // Mouse orbit (right-click drag)
  if (!ImGui::GetIO().WantCaptureMouse) {
    if (isMouseButtonPressed(GLFW_MOUSE_BUTTON_RIGHT)) {
      camera_.yaw += mouseDeltaX_ * 0.3f;
      camera_.pitch -= mouseDeltaY_ * 0.3f;
    }

    // Middle mouse button for roll
    if (isMouseButtonPressed(GLFW_MOUSE_BUTTON_MIDDLE)) {
      camera_.roll += mouseDeltaX_ * 0.3f;
    }

    // Scroll wheel zoom with sensitivity
    if (std::abs(scrollDelta_) > 0.0f) {
      camera_.distance -= scrollDelta_ * scrollSensitivity_ * 0.5f;
    }
  }

  // Clamp values
  camera_.pitch = std::clamp(camera_.pitch, -89.0f, 89.0f);
  camera_.distance = std::clamp(camera_.distance, 0.5f, 50.0f);

  // Normalize angles
  while (camera_.yaw > 180.0f)
    camera_.yaw -= 360.0f;
  while (camera_.yaw < -180.0f)
    camera_.yaw += 360.0f;
  while (camera_.roll > 180.0f)
    camera_.roll -= 360.0f;
  while (camera_.roll < -180.0f)
    camera_.roll += 360.0f;
}

void InputManager::shutdown() { window_ = nullptr; }

bool InputManager::isKeyPressed(int key) const {
  if (key < 0 || key > GLFW_KEY_LAST)
    return false;
  return keyState_[key];
}

bool InputManager::isKeyJustPressed(int key) const {
  if (key < 0 || key > GLFW_KEY_LAST)
    return false;
  return keyState_[key] && !prevKeyState_[key];
}

bool InputManager::isKeyJustReleased(int key) const {
  if (key < 0 || key > GLFW_KEY_LAST)
    return false;
  return !keyState_[key] && prevKeyState_[key];
}

bool InputManager::isMouseButtonPressed(int button) const {
  if (button < 0 || button > GLFW_MOUSE_BUTTON_LAST)
    return false;
  return mouseButtonState_[button];
}

bool InputManager::isMouseButtonJustPressed(int button) const {
  if (button < 0 || button > GLFW_MOUSE_BUTTON_LAST)
    return false;
  return mouseButtonState_[button] && !prevMouseButtonState_[button];
}

bool InputManager::isActionPressed(KeyAction action) const {
  auto it = keyBindings_.find(action);
  if (it == keyBindings_.end())
    return false;
  return isKeyPressed(it->second);
}

bool InputManager::isActionJustPressed(KeyAction action) const {
  auto it = keyBindings_.find(action);
  if (it == keyBindings_.end())
    return false;
  return isKeyJustPressed(it->second);
}

int InputManager::getKeyForAction(KeyAction action) const {
  auto it = keyBindings_.find(action);
  if (it == keyBindings_.end())
    return GLFW_KEY_UNKNOWN;
  return it->second;
}

void InputManager::setKeyForAction(KeyAction action, int key) { keyBindings_[action] = key; }

std::string InputManager::getKeyName(int key) const {
  const char *name = glfwGetKeyName(key, 0);
  if (name)
    return std::string(name);

  // Handle special keys
  switch (key) {
  case GLFW_KEY_ESCAPE:
    return "ESC";
  case GLFW_KEY_ENTER:
    return "Enter";
  case GLFW_KEY_TAB:
    return "Tab";
  case GLFW_KEY_BACKSPACE:
    return "Backspace";
  case GLFW_KEY_SPACE:
    return "Space";
  case GLFW_KEY_F1:
    return "F1";
  case GLFW_KEY_F2:
    return "F2";
  case GLFW_KEY_F3:
    return "F3";
  case GLFW_KEY_F4:
    return "F4";
  case GLFW_KEY_F5:
    return "F5";
  case GLFW_KEY_F6:
    return "F6";
  case GLFW_KEY_F11:
    return "F11";
  case GLFW_KEY_UP:
    return "Up";
  case GLFW_KEY_DOWN:
    return "Down";
  case GLFW_KEY_LEFT:
    return "Left";
  case GLFW_KEY_RIGHT:
    return "Right";
  case GLFW_KEY_LEFT_BRACKET:
    return "[";
  case GLFW_KEY_RIGHT_BRACKET:
    return "]";
  default:
    return "Unknown";
  }
}

const char *InputManager::getActionName(KeyAction action) const {
  switch (action) {
  case KeyAction::Quit:
    return "Quit";
  case KeyAction::ToggleUI:
    return "Toggle UI";
  case KeyAction::ToggleFullscreen:
    return "Fullscreen";
  case KeyAction::ResetCamera:
    return "Reset Camera";
  case KeyAction::ResetSettings:
    return "Reset Settings";
  case KeyAction::Pause:
    return "Pause";
  case KeyAction::CameraMoveForward:
    return "Camera Forward";
  case KeyAction::CameraMoveBackward:
    return "Camera Backward";
  case KeyAction::CameraMoveLeft:
    return "Camera Left";
  case KeyAction::CameraMoveRight:
    return "Camera Right";
  case KeyAction::CameraMoveUp:
    return "Camera Up";
  case KeyAction::CameraMoveDown:
    return "Camera Down";
  case KeyAction::CameraRollLeft:
    return "Roll Left";
  case KeyAction::CameraRollRight:
    return "Roll Right";
  case KeyAction::ZoomIn:
    return "Zoom In";
  case KeyAction::ZoomOut:
    return "Zoom Out";
  case KeyAction::ToggleAccessibility:
    return "Accessibility Menu";
  case KeyAction::ToggleHighContrast:
    return "High Contrast";
  case KeyAction::ToggleReducedMotion:
    return "Reduced Motion";
  case KeyAction::IncreaseFontSize:
    return "Increase Font";
  case KeyAction::DecreaseFontSize:
    return "Decrease Font";
  case KeyAction::CycleColorblindMode:
    return "Cycle Colorblind";
  case KeyAction::IncreaseTimeScale:
    return "Speed Up";
  case KeyAction::DecreaseTimeScale:
    return "Slow Down";
  default:
    return "Unknown";
  }
}

void InputManager::toggleFullscreen() {
  if (fullscreen_) {
    // Restore windowed mode
    glfwSetWindowMonitor(window_, nullptr, windowedX_, windowedY_, windowedWidth_, windowedHeight_,
                         GLFW_DONT_CARE);
    fullscreen_ = false;
  } else {
    // Store current window position/size
    glfwGetWindowPos(window_, &windowedX_, &windowedY_);
    glfwGetWindowSize(window_, &windowedWidth_, &windowedHeight_);

    // Go fullscreen on primary monitor
    GLFWmonitor *monitor = glfwGetPrimaryMonitor();
    const GLFWvidmode *mode = glfwGetVideoMode(monitor);
    glfwSetWindowMonitor(window_, monitor, 0, 0, mode->width, mode->height, mode->refreshRate);
    fullscreen_ = true;
  }
}

void InputManager::onKey(int key, int /*scancode*/, int action, int /*mods*/) {
  // Handle key remapping mode
  if (remappingAction_ != KeyAction::COUNT && action == GLFW_PRESS) {
    if (key != GLFW_KEY_ESCAPE) {
      keyBindings_[remappingAction_] = key;
    }
    remappingAction_ = KeyAction::COUNT;
    return;
  }

  if (key >= 0 && key <= GLFW_KEY_LAST) {
    keyState_[key] = (action != GLFW_RELEASE);
  }
}

void InputManager::onMouseButton(int button, int action, int /*mods*/) {
  if (button >= 0 && button <= GLFW_MOUSE_BUTTON_LAST) {
    mouseButtonState_[button] = (action != GLFW_RELEASE);
  }
}

void InputManager::onMouseMove(double x, double y) {
  mouseX_ = static_cast<float>(x);
  mouseY_ = static_cast<float>(y);

  if (firstMouse_) {
    prevMouseX_ = mouseX_;
    prevMouseY_ = mouseY_;
    firstMouse_ = false;
  }
}

void InputManager::onScroll(double /*xoffset*/, double yoffset) {
  scrollDelta_ = static_cast<float>(yoffset);
}

float InputManager::getShaderMouseX() const { return mouseX_; }

float InputManager::getShaderMouseY() const { return mouseY_; }

float InputManager::getEffectiveDeltaTime(float rawDeltaTime) const {
  if (paused_) {
    return 0.0f;
  }
  return rawDeltaTime * timeScale_;
}
