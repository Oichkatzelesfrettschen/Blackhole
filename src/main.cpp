/**
 * @file main.cpp
 * @author Ross Ning (rossning92@gmail.com)
 * @brief Real-time black hole rendering in OpenGL.
 * @version 0.2
 * @date 2020-08-29
 *
 * @copyright Copyright (c) 2020
 *
 */

// C system headers
#include <cassert>
#include <cstdio>

// C++ system headers
#include <map>
#include <string>
#include <vector>

// Third-party library headers
#include <GL/glew.h>
#include <GLFW/glfw3.h>
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>
#include <imgui.h>

// Local headers
#include "GLDebugMessageCallback.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include "input.h"
#include "render.h"
#include "settings.h"
#include "shader.h"
#include "shader_manager.h"
#include "texture.h"

static const int SCR_WIDTH = 1920;
static const int SCR_HEIGHT = 1080;

#define IMGUI_TOGGLE(NAME, DEFAULT)                                                                \
  static bool NAME = DEFAULT;                                                                      \
  ImGui::Checkbox(#NAME, &NAME);                                                                   \
  rtti.floatUniforms[#NAME] = NAME ? 1.0f : 0.0f;

#define IMGUI_SLIDER(NAME, DEFAULT, MIN, MAX)                                                      \
  static float NAME = DEFAULT;                                                                     \
  ImGui::SliderFloat(#NAME, &NAME, MIN, MAX);                                                      \
  rtti.floatUniforms[#NAME] = NAME;

enum class CameraMode { Input = 0, Front, Top, Orbit };

static glm::vec3 cameraPositionFromYawPitch(float yawDeg, float pitchDeg, float radius) {
  float yawRad = glm::radians(yawDeg);
  float pitchRad = glm::radians(pitchDeg);
  return glm::vec3(radius * std::cos(pitchRad) * std::sin(yawRad),
                   radius * std::sin(pitchRad),
                   radius * std::cos(pitchRad) * std::cos(yawRad));
}

static glm::mat3 buildCameraBasis(const glm::vec3 &cameraPos, const glm::vec3 &target,
                                  float rollDeg) {
  glm::vec3 forward = glm::normalize(target - cameraPos);
  glm::vec3 worldUp(0.0f, 1.0f, 0.0f);
  if (std::abs(glm::dot(forward, worldUp)) > 0.99f) {
    worldUp = glm::vec3(0.0f, 0.0f, 1.0f);
  }

  glm::vec3 right = glm::normalize(glm::cross(forward, worldUp));
  glm::vec3 up = glm::normalize(glm::cross(right, forward));

  if (std::abs(rollDeg) > 0.001f) {
    float rollRad = glm::radians(rollDeg);
    float cosRoll = std::cos(rollRad);
    float sinRoll = std::sin(rollRad);
    glm::vec3 rolledRight = right * cosRoll + up * sinRoll;
    glm::vec3 rolledUp = -right * sinRoll + up * cosRoll;
    right = rolledRight;
    up = rolledUp;
  }

  return glm::mat3(right, up, forward);
}

static void glfwErrorCallback(int error, const char *description) {
  fprintf(stderr, "Glfw Error %d: %s\n", error, description);
}

// GLFW callbacks that delegate to InputManager
static void keyCallback(GLFWwindow * /*window*/, int key, int scancode, int action, int mods) {
  InputManager::instance().onKey(key, scancode, action, mods);
}

static void mouseButtonCallback(GLFWwindow * /*window*/, int button, int action, int mods) {
  InputManager::instance().onMouseButton(button, action, mods);
}

static void cursorPosCallback(GLFWwindow * /*window*/, double x, double y) {
  InputManager::instance().onMouseMove(x, y);
}

static void scrollCallback(GLFWwindow * /*window*/, double xoffset, double yoffset) {
  InputManager::instance().onScroll(xoffset, yoffset);
}

// Initialize OpenGL debug context (call after GLEW init)
static void initializeGLDebugContext() {
#ifdef ENABLE_GL_DEBUG_CONTEXT
  // Check if debug context is available (OpenGL 4.3+ or KHR_debug extension)
  GLint contextFlags = 0;
  glGetIntegerv(GL_CONTEXT_FLAGS, &contextFlags);

  if (contextFlags & GL_CONTEXT_FLAG_DEBUG_BIT) {
    std::printf("[GL Debug] Debug context active\n");

    // Enable debug output
    glEnable(GL_DEBUG_OUTPUT);
    glEnable(GL_DEBUG_OUTPUT_SYNCHRONOUS);

    // Set debug callback
    glDebugMessageCallback(GLDebugMessageCallback, nullptr);

    // Enable all messages by default
    glDebugMessageControl(GL_DONT_CARE, GL_DONT_CARE, GL_DONT_CARE, 0, nullptr, GL_TRUE);

    // Optionally disable notification-level messages (very verbose)
    glDebugMessageControl(GL_DONT_CARE, GL_DONT_CARE, GL_DEBUG_SEVERITY_NOTIFICATION, 0, nullptr,
                          GL_FALSE);

    std::printf("[GL Debug] Debug message callback registered\n");
  } else {
    std::printf("[GL Debug] Debug context not available (need OpenGL 4.3+ or KHR_debug)\n");
  }
#endif
}

// Initialize GLFW and create window
static GLFWwindow *initializeWindow() {
  glfwSetErrorCallback(glfwErrorCallback);
  if (!glfwInit()) {
    return nullptr;
  }

  glfwWindowHint(GLFW_DECORATED, GLFW_TRUE);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
  glfwWindowHint(GLFW_OPENGL_FORWARD_COMPAT, GL_TRUE);

#ifdef ENABLE_GL_DEBUG_CONTEXT
  // Request debug context for OpenGL error reporting
  glfwWindowHint(GLFW_OPENGL_DEBUG_CONTEXT, GLFW_TRUE);
#endif

  GLFWwindow *window = glfwCreateWindow(SCR_WIDTH, SCR_HEIGHT, "Blackhole", nullptr, nullptr);
  if (window == nullptr) {
    return nullptr;
  }

  glfwMakeContextCurrent(window);
  glfwSwapInterval(1); // Enable vsync

  // Set up input callbacks
  glfwSetKeyCallback(window, keyCallback);
  glfwSetMouseButtonCallback(window, mouseButtonCallback);
  glfwSetCursorPosCallback(window, cursorPosCallback);
  glfwSetScrollCallback(window, scrollCallback);

  glfwSetWindowPos(window, 0, 0);

  glewExperimental = GL_TRUE;
  if (glewInit() != GLEW_OK) {
    std::fprintf(stderr, "Failed to initialize OpenGL loader!\n");
    glfwDestroyWindow(window);
    return nullptr;
  }

  GLint glMajor = 0;
  GLint glMinor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &glMajor);
  glGetIntegerv(GL_MINOR_VERSION, &glMinor);
  if (glMajor < 4 || (glMajor == 4 && glMinor < 6)) {
    std::fprintf(stderr, "OpenGL 4.6 required, found %d.%d\n", glMajor, glMinor);
    glfwDestroyWindow(window);
    return nullptr;
  }

  // Initialize GL debug context after GLEW
  initializeGLDebugContext();

  return window;
}

// Initialize ImGui context and backends
static void initializeImGui(GLFWwindow *window) {
  const char *glsl_version = "#version 460";

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard; // Enable keyboard navigation

  ImGui::StyleColorsDark();

  ImGui_ImplGlfw_InitForOpenGL(window, true);
  ImGui_ImplOpenGL3_Init(glsl_version);
}

// Render controls help panel
static void renderControlsHelpPanel() {
  ImGui::SetNextWindowPos(ImVec2(10, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 280), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls Help", nullptr, ImGuiWindowFlags_NoCollapse)) {
    auto &input = InputManager::instance();

    auto keyLabel = [&](KeyAction action) {
      return input.getKeyName(input.getKeyForAction(action));
    };

    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Keyboard Shortcuts");
    ImGui::Separator();

    ImGui::Text("%s - Quit", keyLabel(KeyAction::Quit).c_str());
    ImGui::Text("%s - Toggle UI", keyLabel(KeyAction::ToggleUI).c_str());
    ImGui::Text("%s - Toggle Fullscreen", keyLabel(KeyAction::ToggleFullscreen).c_str());
    ImGui::Text("%s - Reset Camera", keyLabel(KeyAction::ResetCamera).c_str());
    ImGui::Text("%s - Pause", keyLabel(KeyAction::Pause).c_str());
    ImGui::Text("%s - Reset Settings", keyLabel(KeyAction::ResetSettings).c_str());

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Camera Controls");
    ImGui::Separator();

    ImGui::Text("%s/%s - Pitch Up/Down", keyLabel(KeyAction::CameraMoveForward).c_str(),
                keyLabel(KeyAction::CameraMoveBackward).c_str());
    ImGui::Text("%s/%s - Yaw Left/Right", keyLabel(KeyAction::CameraMoveLeft).c_str(),
                keyLabel(KeyAction::CameraMoveRight).c_str());
    ImGui::Text("%s/%s - Zoom In/Out", keyLabel(KeyAction::CameraMoveUp).c_str(),
                keyLabel(KeyAction::CameraMoveDown).c_str());
    ImGui::Text("%s/%s - Roll Left/Right", keyLabel(KeyAction::CameraRollLeft).c_str(),
                keyLabel(KeyAction::CameraRollRight).c_str());
    ImGui::Text("%s/%s - Zoom In/Out", keyLabel(KeyAction::ZoomIn).c_str(),
                keyLabel(KeyAction::ZoomOut).c_str());

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Mouse Controls");
    ImGui::Separator();

    ImGui::Text("Right-drag - Orbit Camera");
    ImGui::Text("Mid-drag   - Roll Camera");
    ImGui::Text("Scroll     - Zoom");

    ImGui::Spacing();
    ImGui::Separator();

    // Show current camera state
    const auto &cam = input.camera();
    ImGui::Text("Camera: Y%.1f P%.1f R%.1f D%.1f", static_cast<double>(cam.yaw),
                static_cast<double>(cam.pitch), static_cast<double>(cam.roll),
                static_cast<double>(cam.distance));
  }
  ImGui::End();
}

static void renderControlsSettingsPanel(int &cameraModeIndex) {
  auto &input = InputManager::instance();

  ImGui::SetNextWindowPos(ImVec2(320, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(360, 520), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Sensitivity");
    ImGui::Separator();

    float mouseSensitivity = input.getMouseSensitivity();
    if (ImGui::SliderFloat("Mouse Sensitivity", &mouseSensitivity, 0.1f, 3.0f)) {
      input.setMouseSensitivity(mouseSensitivity);
    }

    float keyboardSensitivity = input.getKeyboardSensitivity();
    if (ImGui::SliderFloat("Keyboard Sensitivity", &keyboardSensitivity, 0.1f, 3.0f)) {
      input.setKeyboardSensitivity(keyboardSensitivity);
    }

    float scrollSensitivity = input.getScrollSensitivity();
    if (ImGui::SliderFloat("Scroll Sensitivity", &scrollSensitivity, 0.1f, 3.0f)) {
      input.setScrollSensitivity(scrollSensitivity);
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Inversion");
    ImGui::Separator();

    bool invertMouseX = input.isMouseXInverted();
    if (ImGui::Checkbox("Invert Mouse X", &invertMouseX)) {
      input.setMouseXInverted(invertMouseX);
    }
    bool invertMouseY = input.isMouseYInverted();
    if (ImGui::Checkbox("Invert Mouse Y", &invertMouseY)) {
      input.setMouseYInverted(invertMouseY);
    }
    bool invertKeyboardX = input.isKeyboardXInverted();
    if (ImGui::Checkbox("Invert Keyboard X", &invertKeyboardX)) {
      input.setKeyboardXInverted(invertKeyboardX);
    }
    bool invertKeyboardY = input.isKeyboardYInverted();
    if (ImGui::Checkbox("Invert Keyboard Y", &invertKeyboardY)) {
      input.setKeyboardYInverted(invertKeyboardY);
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Camera Control");
    ImGui::Separator();

    const char *cameraModeLabels[] = {"Input", "Front", "Top", "Orbit"};
    ImGui::Combo("Camera Mode", &cameraModeIndex, cameraModeLabels,
                 IM_ARRAYSIZE(cameraModeLabels));

    bool holdToToggle = input.isHoldToToggleCamera();
    if (ImGui::Checkbox("Hold-to-Toggle Camera", &holdToToggle)) {
      input.setHoldToToggleCamera(holdToToggle);
    }

    float timeScale = input.getTimeScale();
    if (ImGui::SliderFloat("Time Scale", &timeScale, 0.0f, 4.0f)) {
      input.setTimeScale(timeScale);
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Gamepad");
    ImGui::Separator();

    ImGui::Text("Status: %s", input.isGamepadConnected() ? "Connected" : "Not detected");

    bool gamepadEnabled = input.isGamepadEnabled();
    if (ImGui::Checkbox("Enable Gamepad", &gamepadEnabled)) {
      input.setGamepadEnabled(gamepadEnabled);
    }

    float gamepadDeadzone = input.getGamepadDeadzone();
    if (ImGui::SliderFloat("Deadzone", &gamepadDeadzone, 0.0f, 0.5f)) {
      input.setGamepadDeadzone(gamepadDeadzone);
    }

    float gamepadLookSensitivity = input.getGamepadLookSensitivity();
    if (ImGui::SliderFloat("Look Sensitivity", &gamepadLookSensitivity, 10.0f, 180.0f)) {
      input.setGamepadLookSensitivity(gamepadLookSensitivity);
    }

    float gamepadRollSensitivity = input.getGamepadRollSensitivity();
    if (ImGui::SliderFloat("Roll Sensitivity", &gamepadRollSensitivity, 10.0f, 180.0f)) {
      input.setGamepadRollSensitivity(gamepadRollSensitivity);
    }

    float gamepadZoomSensitivity = input.getGamepadZoomSensitivity();
    if (ImGui::SliderFloat("Zoom Sensitivity", &gamepadZoomSensitivity, 1.0f, 20.0f)) {
      input.setGamepadZoomSensitivity(gamepadZoomSensitivity);
    }

    float gamepadTriggerZoomSensitivity = input.getGamepadTriggerZoomSensitivity();
    if (ImGui::SliderFloat("Trigger Zoom Sensitivity", &gamepadTriggerZoomSensitivity, 1.0f,
                           20.0f)) {
      input.setGamepadTriggerZoomSensitivity(gamepadTriggerZoomSensitivity);
    }

    bool gamepadInvertX = input.isGamepadXInverted();
    if (ImGui::Checkbox("Invert Gamepad X", &gamepadInvertX)) {
      input.setGamepadXInverted(gamepadInvertX);
    }
    bool gamepadInvertY = input.isGamepadYInverted();
    if (ImGui::Checkbox("Invert Gamepad Y", &gamepadInvertY)) {
      input.setGamepadYInverted(gamepadInvertY);
    }
    bool gamepadInvertRoll = input.isGamepadRollInverted();
    if (ImGui::Checkbox("Invert Gamepad Roll", &gamepadInvertRoll)) {
      input.setGamepadRollInverted(gamepadInvertRoll);
    }
    bool gamepadInvertZoom = input.isGamepadZoomInverted();
    if (ImGui::Checkbox("Invert Gamepad Zoom", &gamepadInvertZoom)) {
      input.setGamepadZoomInverted(gamepadInvertZoom);
    }

    if (ImGui::CollapsingHeader("Gamepad Axis Mapping")) {
      int yawAxis = input.getGamepadYawAxis();
      if (ImGui::SliderInt("Yaw Axis", &yawAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadYawAxis(yawAxis);
      }
      int pitchAxis = input.getGamepadPitchAxis();
      if (ImGui::SliderInt("Pitch Axis", &pitchAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadPitchAxis(pitchAxis);
      }
      int rollAxis = input.getGamepadRollAxis();
      if (ImGui::SliderInt("Roll Axis", &rollAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadRollAxis(rollAxis);
      }
      int zoomAxis = input.getGamepadZoomAxis();
      if (ImGui::SliderInt("Zoom Axis", &zoomAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomAxis(zoomAxis);
      }
      int zoomInAxis = input.getGamepadZoomInAxis();
      if (ImGui::SliderInt("Zoom In Trigger", &zoomInAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomInAxis(zoomInAxis);
      }
      int zoomOutAxis = input.getGamepadZoomOutAxis();
      if (ImGui::SliderInt("Zoom Out Trigger", &zoomOutAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomOutAxis(zoomOutAxis);
      }
    }

    if (ImGui::CollapsingHeader("Key Bindings", ImGuiTreeNodeFlags_DefaultOpen)) {
      if (input.isRemappingKey()) {
        ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.0f, 1.0f),
                           "Press a key to bind to: %s",
                           input.getActionName(input.getRemappingAction()));
        if (ImGui::Button("Cancel")) {
          input.cancelKeyRemapping();
        }
      } else {
        if (ImGui::BeginTable("KeyBindings", 2, ImGuiTableFlags_SizingStretchProp)) {
          for (int i = 0; i < static_cast<int>(KeyAction::COUNT); i++) {
            KeyAction action = static_cast<KeyAction>(i);
            const char *actionName = input.getActionName(action);
            int currentKey = input.getKeyForAction(action);
            std::string keyName = input.getKeyName(currentKey);

            ImGui::TableNextRow();
            ImGui::TableNextColumn();
            ImGui::Text("%s", actionName);
            ImGui::TableNextColumn();

            ImGui::PushID(i);
            char buttonLabel[64];
            std::snprintf(buttonLabel, sizeof(buttonLabel), "[%s]##%d", keyName.c_str(), i);
            if (ImGui::Button(buttonLabel)) {
              input.startKeyRemapping(action);
            }
            ImGui::PopID();
          }
          ImGui::EndTable();
        }
      }
    }

    ImGui::Spacing();
    if (ImGui::Button("Save Settings")) {
      input.syncToSettings();
      SettingsManager::instance().save();
    }
    ImGui::SameLine();
    if (ImGui::Button("Reset Defaults")) {
      SettingsManager::instance().resetToDefaults();
      input.syncFromSettings();
      SettingsManager::instance().save();
    }
  }
  ImGui::End();
}

// Cleanup resources
static void cleanup(GLFWwindow *window) {
  // Sync and save settings before shutdown
  InputManager::instance().syncToSettings();
  SettingsManager::instance().save();

  InputManager::instance().shutdown();
  ImGui_ImplOpenGL3_Shutdown();
  ImGui_ImplGlfw_Shutdown();
  ImGui::DestroyContext();
  glfwDestroyWindow(window);
  glfwTerminate();
}

class PostProcessPass {
private:
  GLuint program;

public:
  explicit PostProcessPass(const std::string &fragShader) {
    this->program = createShaderProgram("shader/simple.vert", fragShader);

    glUseProgram(this->program);
    glUniform1i(glGetUniformLocation(program, "texture0"), 0);
    glUseProgram(0);
  }

  void render(GLuint inputColorTexture, GLuint destFramebuffer = 0) {
    glBindFramebuffer(GL_FRAMEBUFFER, destFramebuffer);

    glDisable(GL_DEPTH_TEST);

    glClearColor(1.0f, 0.0f, 0.0f, 1.0f);
    glClear(GL_COLOR_BUFFER_BIT);

    glUseProgram(this->program);

    glUniform2f(glGetUniformLocation(this->program, "resolution"), static_cast<float>(SCR_WIDTH),
                static_cast<float>(SCR_HEIGHT));

    glUniform1f(glGetUniformLocation(this->program, "time"), static_cast<float>(glfwGetTime()));

    glActiveTexture(GL_TEXTURE0);
    glBindTexture(GL_TEXTURE_2D, inputColorTexture);

    glDrawArrays(GL_TRIANGLES, 0, 6);

    glUseProgram(0);
  }
};

int main(int, char **) {
  // Load settings first
  SettingsManager::instance().load();

  // Initialize window and OpenGL context
  GLFWwindow *window = initializeWindow();
  if (window == nullptr) {
    return 1;
  }

  // Initialize shader manager (must be after OpenGL context)
  ShaderManager::instance().init();

  // Initialize input manager and sync with settings
  InputManager::instance().init(window);
  InputManager::instance().syncFromSettings();

  // Initialize ImGui
  initializeImGui(window);

  // Create fullscreen quad for rendering
  GLuint quadVAO = createQuadVAO();
  glBindVertexArray(quadVAO);

  // Main loop
  PostProcessPass passthrough("shader/passthrough.frag");

  double lastTime = glfwGetTime();

  while (!glfwWindowShouldClose(window)) {
    // Calculate delta time
    double currentTime = glfwGetTime();
    float deltaTime = static_cast<float>(currentTime - lastTime);
    lastTime = currentTime;

    glfwPollEvents();

    // Update input manager
    InputManager::instance().update(deltaTime);
    auto &input = InputManager::instance();

    ImGui_ImplOpenGL3_NewFrame();
    ImGui_ImplGlfw_NewFrame();
    ImGui::NewFrame();

    int width, height;
    glfwGetFramebufferSize(window, &width, &height);
    glViewport(0, 0, width, height);

    static GLuint galaxy = loadCubemap("assets/skybox_nebula_dark");
    static GLuint colorMap = loadTexture2D("assets/color_map.png");
    static float depthFar = 50.0f;
    static int cameraModeIndex = static_cast<int>(CameraMode::Input);
    static float orbitTime = 0.0f;

    // Get camera state for shader
    const auto &cam = input.camera();
    if (cameraModeIndex < 0 || cameraModeIndex > 3) {
      cameraModeIndex = static_cast<int>(CameraMode::Input);
    }

    orbitTime += input.getEffectiveDeltaTime(deltaTime);
    glm::vec3 cameraPos;
    CameraMode cameraMode = static_cast<CameraMode>(cameraModeIndex);
    switch (cameraMode) {
    case CameraMode::Front:
      cameraPos = glm::vec3(10.0f, 1.0f, 10.0f);
      break;
    case CameraMode::Top:
      cameraPos = glm::vec3(15.0f, 15.0f, 0.0f);
      break;
    case CameraMode::Orbit: {
      float angle = orbitTime * 0.1f;
      float radius = cam.distance > 0.0f ? cam.distance : 15.0f;
      cameraPos = glm::vec3(-std::cos(angle) * radius,
                            std::sin(angle) * radius,
                            std::sin(angle) * radius);
      break;
    }
    case CameraMode::Input:
    default:
      cameraPos = cameraPositionFromYawPitch(cam.yaw, cam.pitch, cam.distance);
      break;
    }

    glm::mat3 cameraBasis = buildCameraBasis(cameraPos, glm::vec3(0.0f), cam.roll);

    static GLuint texBlackhole = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/blackhole_main.frag";
      rtti.cubemapUniforms["galaxy"] = galaxy;
      rtti.textureUniforms["colorMap"] = colorMap;
      rtti.textureUniforms["uSynchLUT"] = colorMap;

      // Pass camera state to shader
      rtti.vec3Uniforms["cameraPos"] = cameraPos;
      rtti.mat3Uniforms["cameraBasis"] = cameraBasis;
      rtti.floatUniforms["depthFar"] = depthFar;

      rtti.targetTexture = texBlackhole;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;

      // Render UI controls only if visible
      if (input.isUIVisible()) {
        ImGui::Begin("Black Hole Parameters", nullptr, ImGuiWindowFlags_NoCollapse);
        IMGUI_TOGGLE(gravatationalLensing, true);
        IMGUI_TOGGLE(renderBlackHole, true);
        IMGUI_TOGGLE(adiskEnabled, true);
        IMGUI_TOGGLE(adiskParticle, true);
        IMGUI_SLIDER(adiskDensityV, 2.0f, 0.0f, 10.0f);
        IMGUI_SLIDER(adiskDensityH, 4.0f, 0.0f, 10.0f);
        IMGUI_SLIDER(adiskHeight, 0.55f, 0.0f, 1.0f);
        IMGUI_SLIDER(adiskLit, 0.25f, 0.0f, 4.0f);
        IMGUI_SLIDER(adiskNoiseLOD, 5.0f, 1.0f, 12.0f);
        IMGUI_SLIDER(adiskNoiseScale, 0.8f, 0.0f, 10.0f);

        static float adiskSpeed = 0.5f;
        ImGui::SliderFloat("adiskSpeed", &adiskSpeed, 0.0f, 1.0f);
        rtti.floatUniforms["adiskSpeed"] = adiskSpeed;

        ImGui::Separator();
        ImGui::Text("Physics Parameters");

        // Black hole mass in solar masses (scaled for visualization)
        static float blackHoleMass = 1.0f;
        ImGui::SliderFloat("blackHoleMass", &blackHoleMass, 0.1f, 10.0f);
        // Kerr spin parameter a (|a|<M)
        static float kerrSpin = 0.0f;
        ImGui::SliderFloat("kerrSpin(a/M)", &kerrSpin, -0.99f, 0.99f);
        rtti.floatUniforms["kerrSpin"] = kerrSpin;

        // Schwarzschild radius: r_s = 2GM/c² (in geometric units where M=1 gives r_s=2)
        float schwarzschildRadius = 2.0f * blackHoleMass;
        rtti.floatUniforms["schwarzschildRadius"] = schwarzschildRadius;

        // Photon sphere radius: r_ph = 1.5 * r_s (unstable photon orbits)
        float photonSphereRadius = 1.5f * schwarzschildRadius;
        rtti.floatUniforms["photonSphereRadius"] = photonSphereRadius;

        // ISCO radius: r_ISCO = 3 * r_s (innermost stable circular orbit)
        float iscoRadius = 3.0f * schwarzschildRadius;
        rtti.floatUniforms["iscoRadius"] = iscoRadius;

        // Physics visualization toggles
        IMGUI_TOGGLE(enablePhotonSphere, false);
        IMGUI_TOGGLE(enableRedshift, false);

        // Display computed radii for reference
        ImGui::Text("r_s = %.2f, r_ph = %.2f, r_ISCO = %.2f",
                    static_cast<double>(schwarzschildRadius),
                    static_cast<double>(photonSphereRadius),
                    static_cast<double>(iscoRadius));

        ImGui::End();
      } else {
        // When UI is hidden, still need to set uniforms
        rtti.floatUniforms["gravatationalLensing"] = 1.0f;
        rtti.floatUniforms["renderBlackHole"] = 1.0f;
        rtti.floatUniforms["adiskEnabled"] = 1.0f;
        rtti.floatUniforms["adiskParticle"] = 1.0f;
        rtti.floatUniforms["adiskDensityV"] = 2.0f;
        rtti.floatUniforms["adiskDensityH"] = 4.0f;
        rtti.floatUniforms["adiskHeight"] = 0.55f;
        rtti.floatUniforms["adiskLit"] = 0.25f;
        rtti.floatUniforms["adiskNoiseLOD"] = 5.0f;
        rtti.floatUniforms["adiskNoiseScale"] = 0.8f;
        rtti.floatUniforms["adiskSpeed"] = 0.5f;

        // Default physics parameters
        rtti.floatUniforms["schwarzschildRadius"] = 2.0f;
        rtti.floatUniforms["photonSphereRadius"] = 3.0f;
        rtti.floatUniforms["iscoRadius"] = 6.0f;
        rtti.floatUniforms["enablePhotonSphere"] = 0.0f;
        rtti.floatUniforms["enableRedshift"] = 0.0f;
        rtti.floatUniforms["kerrSpin"] = 0.0f;
      }

      renderToTexture(rtti);
    }

    static GLuint texBrightness = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_brightness_pass.frag";
      rtti.textureUniforms["texture0"] = texBlackhole;
      rtti.targetTexture = texBrightness;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;
      renderToTexture(rtti);
    }

    const int MAX_BLOOM_ITER = 8;
    static GLuint texDownsampled[MAX_BLOOM_ITER];
    static GLuint texUpsampled[MAX_BLOOM_ITER];
    if (texDownsampled[0] == 0) {
      for (int i = 0; i < MAX_BLOOM_ITER; i++) {
        texDownsampled[i] = createColorTexture(SCR_WIDTH >> (i + 1), SCR_HEIGHT >> (i + 1));
        texUpsampled[i] = createColorTexture(SCR_WIDTH >> i, SCR_HEIGHT >> i);
      }
    }

    static int bloomIterations = MAX_BLOOM_ITER;
    if (input.isUIVisible()) {
      ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
      ImGui::SliderInt("bloomIterations", &bloomIterations, 1, 8);
      ImGui::End();
    }

    for (int level = 0; level < bloomIterations; level++) {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_downsample.frag";
      rtti.textureUniforms["texture0"] = level == 0 ? texBrightness : texDownsampled[level - 1];
      rtti.targetTexture = texDownsampled[level];
      rtti.width = SCR_WIDTH >> (level + 1);
      rtti.height = SCR_HEIGHT >> (level + 1);
      renderToTexture(rtti);
    }

    for (int level = bloomIterations - 1; level >= 0; level--) {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_upsample.frag";
      rtti.textureUniforms["texture0"] =
          level == bloomIterations - 1 ? texDownsampled[level] : texUpsampled[level + 1];
      rtti.textureUniforms["texture1"] = level == 0 ? texBrightness : texDownsampled[level - 1];
      rtti.targetTexture = texUpsampled[level];
      rtti.width = SCR_WIDTH >> level;
      rtti.height = SCR_HEIGHT >> level;
      renderToTexture(rtti);
    }

    static GLuint texBloomFinal = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/bloom_composite.frag";
      rtti.textureUniforms["texture0"] = texBlackhole;
      rtti.textureUniforms["texture1"] = texUpsampled[0];
      rtti.targetTexture = texBloomFinal;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;

      if (input.isUIVisible()) {
        ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
        IMGUI_SLIDER(bloomStrength, 0.1f, 0.0f, 1.0f);
        ImGui::End();
      } else {
        rtti.floatUniforms["bloomStrength"] = 0.1f;
      }

      renderToTexture(rtti);
    }

    static GLuint texTonemapped = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/tonemapping.frag";
      rtti.textureUniforms["texture0"] = texBloomFinal;
      rtti.targetTexture = texTonemapped;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;

      if (input.isUIVisible()) {
        ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
        IMGUI_TOGGLE(tonemappingEnabled, true);
        IMGUI_SLIDER(gamma, 2.5f, 1.0f, 4.0f);
        ImGui::End();
      } else {
        rtti.floatUniforms["tonemappingEnabled"] = 1.0f;
        rtti.floatUniforms["gamma"] = 2.5f;
      }

      renderToTexture(rtti);
    }

    static GLuint texDepthEffects = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    static bool depthEffectsEnabled = false;
    static bool fogEnabled = true;
    static float fogDensity = 0.35f;
    static float fogStart = 0.2f;
    static float fogEnd = 0.9f;
    static float fogColor[3] = {0.08f, 0.08f, 0.12f};
    static bool edgeOutlinesEnabled = false;
    static float edgeThreshold = 0.5f;
    static float edgeWidth = 1.0f;
    static float edgeColor[3] = {1.0f, 1.0f, 1.0f};
    static bool depthDesatEnabled = false;
    static float desatStrength = 0.5f;
    static bool chromaDepthEnabled = false;
    static bool motionParallaxHint = false;
    static bool dofEnabled = false;
    static float dofFocusNear = 0.2f;
    static float dofFocusFar = 0.9f;
    static float dofMaxRadius = 6.0f;

    if (input.isUIVisible()) {
      ImGui::Begin("Depth Effects", nullptr, ImGuiWindowFlags_NoCollapse);
      ImGui::Checkbox("Enable Depth Effects", &depthEffectsEnabled);
      ImGui::SliderFloat("Depth Far", &depthFar, 10.0f, 200.0f);
      ImGui::Separator();

      ImGui::Checkbox("Fog", &fogEnabled);
      ImGui::SliderFloat("Fog Density", &fogDensity, 0.0f, 1.0f);
      ImGui::SliderFloat("Fog Start", &fogStart, 0.0f, 1.0f);
      ImGui::SliderFloat("Fog End", &fogEnd, 0.0f, 1.0f);
      if (fogStart > fogEnd) {
        fogStart = fogEnd;
      }
      ImGui::ColorEdit3("Fog Color", fogColor);

      ImGui::Separator();
      ImGui::Checkbox("Edge Outlines", &edgeOutlinesEnabled);
      ImGui::SliderFloat("Edge Threshold", &edgeThreshold, 0.0f, 1.0f);
      ImGui::SliderFloat("Edge Width", &edgeWidth, 0.5f, 3.0f);
      ImGui::ColorEdit3("Edge Color", edgeColor);

      ImGui::Separator();
      ImGui::Checkbox("Depth Desaturation", &depthDesatEnabled);
      ImGui::SliderFloat("Desaturation", &desatStrength, 0.0f, 1.0f);
      ImGui::Checkbox("Chroma Depth", &chromaDepthEnabled);
      ImGui::Checkbox("Motion Parallax Hint", &motionParallaxHint);

      ImGui::Separator();
      ImGui::Checkbox("Depth of Field", &dofEnabled);
      ImGui::SliderFloat("DoF Focus Near", &dofFocusNear, 0.0f, 1.0f);
      ImGui::SliderFloat("DoF Focus Far", &dofFocusFar, 0.0f, 1.0f);
      if (dofFocusNear > dofFocusFar) {
        dofFocusNear = dofFocusFar;
      }
      ImGui::SliderFloat("DoF Max Radius", &dofMaxRadius, 0.0f, 12.0f);
      ImGui::End();
    }

    GLuint finalTexture = texTonemapped;
    if (depthEffectsEnabled) {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/depth_cues.frag";
      rtti.textureUniforms["texture0"] = texTonemapped;
      rtti.textureUniforms["depthTexture"] = texBlackhole;
      rtti.targetTexture = texDepthEffects;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;
      rtti.floatUniforms["depthEffectsEnabled"] = 1.0f;
      rtti.floatUniforms["fogEnabled"] = fogEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["fogDensity"] = fogDensity;
      rtti.floatUniforms["fogStart"] = fogStart;
      rtti.floatUniforms["fogEnd"] = fogEnd;
      rtti.floatUniforms["fogColorR"] = fogColor[0];
      rtti.floatUniforms["fogColorG"] = fogColor[1];
      rtti.floatUniforms["fogColorB"] = fogColor[2];
      rtti.floatUniforms["edgeOutlinesEnabled"] = edgeOutlinesEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["edgeThreshold"] = edgeThreshold;
      rtti.floatUniforms["edgeWidth"] = edgeWidth;
      rtti.floatUniforms["edgeColorR"] = edgeColor[0];
      rtti.floatUniforms["edgeColorG"] = edgeColor[1];
      rtti.floatUniforms["edgeColorB"] = edgeColor[2];
      rtti.floatUniforms["depthDesatEnabled"] = depthDesatEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["desatStrength"] = desatStrength;
      rtti.floatUniforms["chromaDepthEnabled"] = chromaDepthEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["motionParallaxHint"] = motionParallaxHint ? 1.0f : 0.0f;
      rtti.floatUniforms["dofEnabled"] = dofEnabled ? 1.0f : 0.0f;
      rtti.floatUniforms["dofFocusNear"] = dofFocusNear;
      rtti.floatUniforms["dofFocusFar"] = dofFocusFar;
      rtti.floatUniforms["dofMaxRadius"] = dofMaxRadius;
      renderToTexture(rtti);
      finalTexture = texDepthEffects;
    }

    // Final passthrough to screen
    passthrough.render(finalTexture);

    // Render UI panels (before popup modal for proper window ordering)
    if (input.isUIVisible()) {
      renderControlsHelpPanel();
      renderControlsSettingsPanel(cameraModeIndex);
    }

    ImGui::Render();
    ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());

    glfwSwapBuffers(window);
  }

  cleanup(window);
  return 0;
}
