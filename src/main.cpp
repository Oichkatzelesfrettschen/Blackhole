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
#include <vector>

// Third-party library headers
#include <GL/glew.h>
#include <GLFW/glfw3.h>
#include <glm/glm.hpp>
#include <glm/gtc/matrix_transform.hpp>
#include <glm/gtc/type_ptr.hpp>
#include <glm/gtx/euler_angles.hpp>
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

  if (glewInit() != GLEW_OK) {
    std::fprintf(stderr, "Failed to initialize OpenGL loader!\n");
    glfwDestroyWindow(window);
    return nullptr;
  }

  // Initialize GL debug context after GLEW
  initializeGLDebugContext();

  return window;
}

// Initialize ImGui context and backends
static void initializeImGui(GLFWwindow *window) {
#if defined(__APPLE__)
  const char *glsl_version = "#version 150";
  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 2);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
  glfwWindowHint(GLFW_OPENGL_FORWARD_COMPAT, GL_TRUE);
#else
  const char *glsl_version = "#version 130";
  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 3);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 0);
#endif

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard; // Enable keyboard navigation

  ImGui::StyleColorsDark();

  ImGui_ImplGlfw_InitForOpenGL(window, true);
  ImGui_ImplOpenGL3_Init(glsl_version);
}

// Render controls help panel
static void renderControlsPanel() {
  ImGui::SetNextWindowPos(ImVec2(10, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(280, 320), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls", nullptr, ImGuiWindowFlags_NoCollapse)) {
    auto &input = InputManager::instance();

    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Keyboard Shortcuts");
    ImGui::Separator();

    ImGui::Text("ESC        - Quit");
    ImGui::Text("H          - Toggle UI");
    ImGui::Text("F11        - Toggle Fullscreen");
    ImGui::Text("R          - Reset Camera");
    ImGui::Text("Backspace  - Reset Settings");

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Camera Controls");
    ImGui::Separator();

    ImGui::Text("W/S        - Pitch Up/Down");
    ImGui::Text("A/D        - Yaw Left/Right");
    ImGui::Text("Q/E        - Zoom In/Out");
    ImGui::Text("Z/C        - Roll Left/Right");
    ImGui::Text("+/-        - Zoom In/Out");

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Mouse Controls");
    ImGui::Separator();

    ImGui::Text("Right-drag - Orbit Camera");
    ImGui::Text("Mid-drag   - Roll Camera");
    ImGui::Text("Scroll     - Zoom");

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Accessibility");
    ImGui::Separator();

    ImGui::Text("F1         - Toggle A11y Mode");
    ImGui::Text("F2         - High Contrast");
    ImGui::Text("F3         - Reduced Motion");
    ImGui::Text("F4/F5      - Font Size +/-");

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

// Render photosensitivity warning modal (shown once on first launch)
static bool showPhotosensitivityWarning = false;

static void checkPhotosensitivityWarning() {
  auto &settings = SettingsManager::instance().get();
  if (!settings.photosensitivityWarningShown) {
    showPhotosensitivityWarning = true;
  }
}

static void renderPhotosensitivityWarning() {
  if (!showPhotosensitivityWarning)
    return;

  auto &settings = SettingsManager::instance().get();

  ImGui::OpenPopup("Photosensitivity Warning");

  ImVec2 center = ImGui::GetMainViewport()->GetCenter();
  ImGui::SetNextWindowPos(center, ImGuiCond_Appearing, ImVec2(0.5f, 0.5f));
  ImGui::SetNextWindowSize(ImVec2(500, 350), ImGuiCond_Appearing);

  if (ImGui::BeginPopupModal("Photosensitivity Warning", nullptr,
                              ImGuiWindowFlags_AlwaysAutoResize)) {
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.0f, 1.0f), "PHOTOSENSITIVITY WARNING");
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::TextWrapped(
        "This application contains flashing lights, rapid brightness changes, "
        "and high-contrast visual effects that may trigger seizures in people "
        "with photosensitive epilepsy.");

    ImGui::Spacing();
    ImGui::TextWrapped(
        "A small percentage of people may experience seizures when exposed to "
        "certain light patterns or flashing lights, even if they have no prior "
        "history of epilepsy or seizures.");

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    ImGui::TextColored(ImVec4(0.2f, 1.0f, 0.2f, 1.0f), "Protection Level:");
    ImGui::Spacing();

    const char *levels[] = {"None (I accept the risk)", "Low (50% bloom reduction)",
                            "Medium (75% reduction + flash limiting)",
                            "High (Minimal effects)", "Maximum (All effects disabled)"};

    int currentLevel = static_cast<int>(settings.photosensitivityLevel);
    for (int i = 0; i < 5; i++) {
      if (ImGui::RadioButton(levels[i], currentLevel == i)) {
        settings.photosensitivityLevel = static_cast<PhotosensitivityLevel>(i);
      }
    }

    ImGui::Spacing();
    ImGui::Separator();
    ImGui::Spacing();

    if (ImGui::Button("I Understand - Continue", ImVec2(220, 30))) {
      settings.photosensitivityWarningShown = true;
      showPhotosensitivityWarning = false;
      SettingsManager::instance().save();
      ImGui::CloseCurrentPopup();
    }

    ImGui::EndPopup();
  }
}

// Render accessibility settings panel
static void renderAccessibilityPanel() {
  auto &settings = SettingsManager::instance().get();

  ImGui::SetNextWindowPos(ImVec2(10, 340), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(320, 400), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Accessibility", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::TextColored(ImVec4(0.2f, 1.0f, 0.2f, 1.0f), "Vision");
    ImGui::Separator();

    ImGui::Checkbox("High Contrast UI", &settings.highContrastUI);
    ImGui::Checkbox("Invert Colors", &settings.invertColors);

    // Colorblind mode selector
    const char *cbModes[] = {"None", "Protanopia", "Deuteranopia", "Tritanopia", "Achromatopsia"};
    int cbMode = static_cast<int>(settings.colorblindMode);
    if (ImGui::Combo("Colorblind Filter", &cbMode, cbModes, 5)) {
      settings.colorblindMode = static_cast<ColorblindMode>(cbMode);
    }

    if (settings.colorblindMode != ColorblindMode::None) {
      ImGui::SliderFloat("Filter Strength", &settings.colorblindStrength, 0.0f, 1.0f);
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 1.0f, 0.2f, 1.0f), "Photosensitivity");
    ImGui::Separator();

    const char *psLevels[] = {"None", "Low", "Medium", "High", "Maximum"};
    int psLevel = static_cast<int>(settings.photosensitivityLevel);
    if (ImGui::Combo("Protection Level", &psLevel, psLevels, 5)) {
      settings.photosensitivityLevel = static_cast<PhotosensitivityLevel>(psLevel);
    }

    ImGui::Checkbox("Reduce Motion", &settings.reduceMotion);

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 1.0f, 0.2f, 1.0f), "Stereoblindness (Depth Cues)");
    ImGui::Separator();

    ImGui::Checkbox("Enable Depth Cue Enhancements", &settings.stereoblindModeEnabled);

    if (settings.stereoblindModeEnabled) {
      ImGui::Indent();

      ImGui::Checkbox("Distance Fog", &settings.depthFogEnabled);
      if (settings.depthFogEnabled) {
        ImGui::SliderFloat("Fog Density", &settings.depthFogDensity, 0.0f, 1.0f);
      }

      ImGui::Checkbox("Edge Outlines", &settings.depthEdgeOutlines);
      if (settings.depthEdgeOutlines) {
        ImGui::SliderFloat("Edge Threshold", &settings.depthEdgeThreshold, 0.0f, 1.0f);
      }

      ImGui::Checkbox("Depth Desaturation", &settings.depthDesaturation);
      if (settings.depthDesaturation) {
        ImGui::SliderFloat("Desaturation", &settings.depthDesatStrength, 0.0f, 1.0f);
      }

      ImGui::Checkbox("Chromatic Depth (Warm/Cool)", &settings.chromaDepthEnabled);

      ImGui::Unindent();
    }

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 1.0f, 0.2f, 1.0f), "Motor");
    ImGui::Separator();

    ImGui::Checkbox("Hold-to-Toggle Camera", &settings.holdToToggleCamera);
    ImGui::SliderFloat("Mouse Sensitivity", &settings.mouseSensitivity, 0.1f, 3.0f);
    ImGui::SliderFloat("Keyboard Sensitivity", &settings.keyboardSensitivity, 0.1f, 3.0f);
    ImGui::Checkbox("Invert Mouse X", &settings.invertMouseX);
    ImGui::Checkbox("Invert Mouse Y", &settings.invertMouseY);

    ImGui::Spacing();
    ImGui::TextColored(ImVec4(0.2f, 1.0f, 0.2f, 1.0f), "Cognitive");
    ImGui::Separator();

    ImGui::SliderFloat("UI Font Scale", &settings.uiFontScale, 0.75f, 2.0f, "%.2f");
    if (ImGui::Button("Apply Font Scale")) {
      ImGui::GetIO().FontGlobalScale = settings.uiFontScale;
    }

    ImGui::Checkbox("Show Control Hints", &settings.showControlHints);
    ImGui::SliderFloat("Time Scale", &settings.timeScale, 0.0f, 2.0f, "%.2f");

    ImGui::Spacing();
    ImGui::Separator();

    if (ImGui::Button("Save Settings")) {
      SettingsManager::instance().save();
    }
    ImGui::SameLine();
    if (ImGui::Button("Reset Defaults")) {
      SettingsManager::instance().resetToDefaults();
    }
  }
  ImGui::End();
}

// Render key remapping panel
static void renderKeyRemappingPanel() {
  auto &input = InputManager::instance();

  ImGui::SetNextWindowPos(ImVec2(340, 340), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 400), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Key Bindings", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::TextColored(ImVec4(1.0f, 0.8f, 0.2f, 1.0f), "Key Remapping");
    ImGui::Separator();

    if (input.isRemappingKey()) {
      ImGui::TextColored(ImVec4(1.0f, 1.0f, 0.0f, 1.0f),
                          "Press a key to bind to: %s",
                          input.getActionName(input.getRemappingAction()));
      if (ImGui::Button("Cancel")) {
        input.cancelKeyRemapping();
      }
    } else {
      ImGui::Text("Click a button to remap that action");
      ImGui::Spacing();

      // List all remappable actions
      for (int i = 0; i < static_cast<int>(KeyAction::COUNT); i++) {
        KeyAction action = static_cast<KeyAction>(i);
        const char *actionName = input.getActionName(action);
        int currentKey = input.getKeyForAction(action);
        std::string keyName = input.getKeyName(currentKey);

        ImGui::PushID(i);

        // Show action name and current binding
        ImGui::Text("%-20s", actionName);
        ImGui::SameLine();

        char buttonLabel[64];
        snprintf(buttonLabel, sizeof(buttonLabel), "[%s]##%d", keyName.c_str(), i);

        if (ImGui::Button(buttonLabel, ImVec2(100, 0))) {
          input.startKeyRemapping(action);
        }

        ImGui::PopID();
      }
    }

    ImGui::Spacing();
    ImGui::Separator();

    if (ImGui::Button("Reset to Defaults")) {
      // Reset key bindings to defaults
      SettingsManager::instance().resetToDefaults();
      input.syncFromSettings();
    }
  }
  ImGui::End();
}

// Apply accessibility styles
static void applyAccessibilityStyles() {
  auto &settings = SettingsManager::instance().get();

  if (settings.highContrastUI) {
    ImGuiStyle &style = ImGui::GetStyle();
    style.Colors[ImGuiCol_WindowBg] = ImVec4(0.0f, 0.0f, 0.0f, 1.0f);
    style.Colors[ImGuiCol_Text] = ImVec4(1.0f, 1.0f, 1.0f, 1.0f);
    style.Colors[ImGuiCol_Border] = ImVec4(1.0f, 1.0f, 1.0f, 1.0f);
    style.Colors[ImGuiCol_FrameBg] = ImVec4(0.2f, 0.2f, 0.2f, 1.0f);
    style.Colors[ImGuiCol_FrameBgHovered] = ImVec4(0.4f, 0.4f, 0.4f, 1.0f);
    style.Colors[ImGuiCol_FrameBgActive] = ImVec4(0.6f, 0.6f, 0.6f, 1.0f);
    style.Colors[ImGuiCol_Button] = ImVec4(0.3f, 0.3f, 0.3f, 1.0f);
    style.Colors[ImGuiCol_ButtonHovered] = ImVec4(0.5f, 0.5f, 0.5f, 1.0f);
    style.Colors[ImGuiCol_ButtonActive] = ImVec4(0.7f, 0.7f, 0.7f, 1.0f);
    style.FrameBorderSize = 1.0f;
  }
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

  // Check if photosensitivity warning needs to be shown
  checkPhotosensitivityWarning();

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

    // Apply accessibility styles if needed
    auto &settings = SettingsManager::instance().get();
    static bool lastHighContrast = false;
    if (settings.highContrastUI != lastHighContrast) {
      if (settings.highContrastUI) {
        applyAccessibilityStyles();
      } else {
        ImGui::StyleColorsDark(); // Reset to default
      }
      lastHighContrast = settings.highContrastUI;
    }

    int width, height;
    glfwGetFramebufferSize(window, &width, &height);
    glViewport(0, 0, width, height);

    static GLuint galaxy = loadCubemap("assets/skybox_nebula_dark");
    static GLuint colorMap = loadTexture2D("assets/color_map.png");

    // Get camera state for shader
    const auto &cam = input.camera();

    static GLuint texBlackhole = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/blackhole_main.frag";
      rtti.cubemapUniforms["galaxy"] = galaxy;
      rtti.textureUniforms["colorMap"] = colorMap;

      // Use InputManager for mouse position
      rtti.floatUniforms["mouseX"] = input.getShaderMouseX();
      rtti.floatUniforms["mouseY"] = input.getShaderMouseY();

      // Pass camera state to shader
      rtti.floatUniforms["cameraYaw"] = cam.yaw;
      rtti.floatUniforms["cameraPitch"] = cam.pitch;
      rtti.floatUniforms["cameraDistance"] = cam.distance;

      rtti.targetTexture = texBlackhole;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;

      // Render UI controls only if visible
      if (input.isUIVisible()) {
        IMGUI_TOGGLE(gravatationalLensing, true);
        IMGUI_TOGGLE(renderBlackHole, true);
        IMGUI_TOGGLE(mouseControl, true);

        // Use camera roll from InputManager
        static float cameraRoll = 0.0f;
        cameraRoll = cam.roll;
        ImGui::SliderFloat("cameraRoll", &cameraRoll, -180.0f, 180.0f);
        rtti.floatUniforms["cameraRoll"] = cameraRoll;

        IMGUI_TOGGLE(frontView, false);
        IMGUI_TOGGLE(topView, false);
        IMGUI_TOGGLE(adiskEnabled, true);
        IMGUI_TOGGLE(adiskParticle, true);
        IMGUI_SLIDER(adiskDensityV, 2.0f, 0.0f, 10.0f);
        IMGUI_SLIDER(adiskDensityH, 4.0f, 0.0f, 10.0f);
        IMGUI_SLIDER(adiskHeight, 0.55f, 0.0f, 1.0f);
        IMGUI_SLIDER(adiskLit, 0.25f, 0.0f, 4.0f);
        IMGUI_SLIDER(adiskNoiseLOD, 5.0f, 1.0f, 12.0f);
        IMGUI_SLIDER(adiskNoiseScale, 0.8f, 0.0f, 10.0f);

        // Reduce animation speed if reduced motion is enabled
        static float adiskSpeed = 0.5f;
        float speedMult = settings.reduceMotion ? 0.1f : 1.0f;
        ImGui::SliderFloat("adiskSpeed", &adiskSpeed, 0.0f, 1.0f);
        rtti.floatUniforms["adiskSpeed"] = adiskSpeed * speedMult;

        ImGui::Separator();
        ImGui::Text("Physics Parameters");

        // Black hole mass in solar masses (scaled for visualization)
        static float blackHoleMass = 1.0f;
        ImGui::SliderFloat("blackHoleMass", &blackHoleMass, 0.1f, 10.0f);
        rtti.floatUniforms["blackHoleMass"] = blackHoleMass;

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

      } else {
        // When UI is hidden, still need to set uniforms
        rtti.floatUniforms["gravatationalLensing"] = 1.0f;
        rtti.floatUniforms["renderBlackHole"] = 1.0f;
        rtti.floatUniforms["mouseControl"] = 1.0f;
        rtti.floatUniforms["cameraRoll"] = cam.roll;
        rtti.floatUniforms["frontView"] = 0.0f;
        rtti.floatUniforms["topView"] = 0.0f;
        rtti.floatUniforms["adiskEnabled"] = 1.0f;
        rtti.floatUniforms["adiskParticle"] = 1.0f;
        rtti.floatUniforms["adiskDensityV"] = 2.0f;
        rtti.floatUniforms["adiskDensityH"] = 4.0f;
        rtti.floatUniforms["adiskHeight"] = 0.55f;
        rtti.floatUniforms["adiskLit"] = 0.25f;
        rtti.floatUniforms["adiskNoiseLOD"] = 5.0f;
        rtti.floatUniforms["adiskNoiseScale"] = 0.8f;
        float speedMult = settings.reduceMotion ? 0.1f : 1.0f;
        rtti.floatUniforms["adiskSpeed"] = 0.5f * speedMult;

        // Default physics parameters
        rtti.floatUniforms["blackHoleMass"] = 1.0f;
        rtti.floatUniforms["schwarzschildRadius"] = 2.0f;
        rtti.floatUniforms["photonSphereRadius"] = 3.0f;
        rtti.floatUniforms["iscoRadius"] = 6.0f;
        rtti.floatUniforms["enablePhotonSphere"] = 0.0f;
        rtti.floatUniforms["enableRedshift"] = 0.0f;
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
      ImGui::SliderInt("bloomIterations", &bloomIterations, 1, 8);
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
        IMGUI_SLIDER(bloomStrength, 0.1f, 0.0f, 1.0f);
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
        IMGUI_TOGGLE(tonemappingEnabled, true);
        IMGUI_SLIDER(gamma, 2.5f, 1.0f, 4.0f);
      } else {
        rtti.floatUniforms["tonemappingEnabled"] = 1.0f;
        rtti.floatUniforms["gamma"] = 2.5f;
      }

      renderToTexture(rtti);
    }

    // Accessibility post-processing pass
    static GLuint texAccessibility = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    static GLuint texPreviousFrame = createColorTexture(SCR_WIDTH, SCR_HEIGHT);
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/accessibility.frag";
      rtti.textureUniforms["texture0"] = texTonemapped;
      rtti.textureUniforms["previousFrame"] = texPreviousFrame;
      rtti.targetTexture = texAccessibility;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;

      // Pass accessibility settings as floats (shader casts to int)
      rtti.floatUniforms["colorblindMode"] =
          static_cast<float>(settings.colorblindMode);
      rtti.floatUniforms["colorblindStrength"] = settings.colorblindStrength;
      rtti.floatUniforms["photosensitivityLevel"] =
          static_cast<float>(settings.photosensitivityLevel);
      rtti.floatUniforms["maxBloomIntensity"] =
          SettingsManager::instance().getEffectiveBloomStrength();
      rtti.floatUniforms["maxFlashFrequency"] = settings.maxFlashFrequency;
      rtti.floatUniforms["invertColors"] = settings.invertColors ? 1.0f : 0.0f;
      rtti.floatUniforms["highContrast"] = settings.highContrastUI ? 1.0f : 0.0f;

      renderToTexture(rtti);
    }

    // Copy current frame to previous frame for next iteration's flash detection
    {
      RenderToTextureInfo rtti;
      rtti.fragShader = "shader/passthrough.frag";
      rtti.textureUniforms["texture0"] = texAccessibility;
      rtti.targetTexture = texPreviousFrame;
      rtti.width = SCR_WIDTH;
      rtti.height = SCR_HEIGHT;
      renderToTexture(rtti);
    }

    passthrough.render(texAccessibility);

    // Render photosensitivity warning modal (takes priority)
    renderPhotosensitivityWarning();

    // Render UI panels
    if (input.isUIVisible()) {
      renderControlsPanel();
      renderAccessibilityPanel();
      renderKeyRemappingPanel();
    }

    ImGui::Render();
    ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());

    glfwSwapBuffers(window);
  }

  cleanup(window);
  return 0;
}
