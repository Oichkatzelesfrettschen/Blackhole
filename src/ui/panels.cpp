/**
 * @file panels.cpp
 * @brief ImGui context setup, dockspace layout, and the standalone control
 *        panels (controls, gizmo, display, background, wiregrid, RmlUi,
 *        performance).
 */

#include "panels.h"

#include <algorithm>
#include <array>
#include <cstdio>
#include <filesystem>
#include <string>
#include <vector>

#include <GLFW/glfw3.h>
#include <imgui.h>
#include <imgui_internal.h>
#include <ImGuizmo.h>
#include <implot.h>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/gtc/type_ptr.hpp>

#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include "input.h"
#include "platform/resource_paths.h"
#include "render/render_state.h"
#include "settings.h"

namespace ui {

using blackhole::BackgroundAsset;
using blackhole::GpuTimerSet;
using blackhole::K_BACKGROUND_LAYERS;
using blackhole::RenderState;
using blackhole::TimingHistory;
using blackhole::WiregridParams;

void applyWiregridModeProfile(WiregridParams::Mode mode, WiregridParams &params,
                              glm::vec4 &color) {
  params.mode = mode;
  params.showErgosphere = true;
  if (mode == WiregridParams::Mode::Diagnostic) {
    params.gridScale = 1.24f;
    params.motionScale = 1.18f;
    params.infallScale = 0.58f;
    params.strength = 1.26f;
    params.scenePreserve = 0.24f;
    color = glm::vec4(0.28f, 0.82f, 0.99f, 0.36f);
    return;
  }

  params.gridScale = 0.92f;
  params.motionScale = 0.62f;
  params.infallScale = 0.24f;
  params.strength = 0.84f;
  params.scenePreserve = 1.0f;
  color = glm::vec4(0.21f, 0.62f, 0.92f, 0.16f);
}

void setupImGuiStyle() {
  ImGuiStyle &style = ImGui::GetStyle();
  ImVec4 *colors = style.Colors;

  // Voxel/Retro Geometry: Sharp corners, distinct borders
  style.WindowRounding = 0.0f;
  style.FrameRounding = 0.0f;
  style.PopupRounding = 0.0f;
  style.ScrollbarRounding = 0.0f;
  style.GrabRounding = 0.0f;
  style.TabRounding = 0.0f;
  style.FrameBorderSize = 1.0f;
  style.WindowBorderSize = 1.0f;
  style.PopupBorderSize = 1.0f;
  style.WindowPadding = ImVec2(8, 8);
  style.FramePadding = ImVec2(6, 4);
  style.ItemSpacing = ImVec2(8, 6);

  // Retro Palette: Deep Blue/Black bg, Cyan/Orange accents
  colors[ImGuiCol_Text] = ImVec4(0.90f, 0.90f, 0.90f, 1.00f);
  colors[ImGuiCol_TextDisabled] = ImVec4(0.50f, 0.50f, 0.50f, 1.00f);
  colors[ImGuiCol_WindowBg] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_ChildBg] = ImVec4(0.08f, 0.08f, 0.12f, 1.00f);
  colors[ImGuiCol_PopupBg] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_Border] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_BorderShadow] = ImVec4(0.00f, 0.00f, 0.00f, 0.00f);
  colors[ImGuiCol_FrameBg] = ImVec4(0.15f, 0.15f, 0.20f, 1.00f);
  colors[ImGuiCol_FrameBgHovered] = ImVec4(0.25f, 0.25f, 0.35f, 1.00f);
  colors[ImGuiCol_FrameBgActive] = ImVec4(0.30f, 0.30f, 0.45f, 1.00f);
  colors[ImGuiCol_TitleBg] = ImVec4(0.10f, 0.10f, 0.15f, 1.00f);
  colors[ImGuiCol_TitleBgActive] = ImVec4(0.15f, 0.15f, 0.25f, 1.00f);
  colors[ImGuiCol_TitleBgCollapsed] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_MenuBarBg] = ImVec4(0.10f, 0.10f, 0.15f, 1.00f);
  colors[ImGuiCol_ScrollbarBg] = ImVec4(0.05f, 0.05f, 0.08f, 1.00f);
  colors[ImGuiCol_ScrollbarGrab] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_ScrollbarGrabHovered] = ImVec4(0.40f, 0.40f, 0.50f, 1.00f);
  colors[ImGuiCol_ScrollbarGrabActive] = ImVec4(0.50f, 0.50f, 0.60f, 1.00f);
  colors[ImGuiCol_CheckMark] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f); // Cyan
  colors[ImGuiCol_SliderGrab] = ImVec4(0.00f, 0.60f, 0.80f, 1.00f);
  colors[ImGuiCol_SliderGrabActive] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_Button] = ImVec4(0.20f, 0.20f, 0.25f, 1.00f);
  colors[ImGuiCol_ButtonHovered] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_ButtonActive] = ImVec4(0.00f, 0.50f, 0.70f, 1.00f);
  colors[ImGuiCol_Header] = ImVec4(0.20f, 0.20f, 0.25f, 1.00f);
  colors[ImGuiCol_HeaderHovered] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_HeaderActive] = ImVec4(0.00f, 0.50f, 0.70f, 1.00f);
  colors[ImGuiCol_Separator] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_SeparatorHovered] = ImVec4(0.40f, 0.40f, 0.50f, 1.00f);
  colors[ImGuiCol_SeparatorActive] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_ResizeGrip] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_ResizeGripHovered] = ImVec4(0.40f, 0.40f, 0.50f, 1.00f);
  colors[ImGuiCol_ResizeGripActive] = ImVec4(0.50f, 0.50f, 0.60f, 1.00f);
  colors[ImGuiCol_Tab] = ImVec4(0.15f, 0.15f, 0.20f, 1.00f);
  colors[ImGuiCol_TabHovered] = ImVec4(0.30f, 0.30f, 0.40f, 1.00f);
  colors[ImGuiCol_TabActive] = ImVec4(0.20f, 0.20f, 0.25f, 1.00f);
  colors[ImGuiCol_TabUnfocused] = ImVec4(0.10f, 0.10f, 0.15f, 1.00f);
  colors[ImGuiCol_TabUnfocusedActive] = ImVec4(0.15f, 0.15f, 0.20f, 1.00f);
  colors[ImGuiCol_DockingPreview] = ImVec4(0.00f, 0.80f, 1.00f, 0.70f);
  colors[ImGuiCol_DockingEmptyBg] = ImVec4(0.10f, 0.10f, 0.10f, 1.00f);
  colors[ImGuiCol_PlotLines] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_PlotLinesHovered] = ImVec4(1.00f, 0.50f, 0.00f, 1.00f);
  colors[ImGuiCol_PlotHistogram] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_PlotHistogramHovered] = ImVec4(1.00f, 0.50f, 0.00f, 1.00f);
  colors[ImGuiCol_TextSelectedBg] = ImVec4(0.00f, 0.50f, 0.80f, 0.35f);
  colors[ImGuiCol_DragDropTarget] = ImVec4(1.00f, 1.00f, 0.00f, 0.90f);
  colors[ImGuiCol_NavHighlight] = ImVec4(0.00f, 0.80f, 1.00f, 1.00f);
  colors[ImGuiCol_NavWindowingHighlight] = ImVec4(1.00f, 1.00f, 1.00f, 0.70f);
  colors[ImGuiCol_NavWindowingDimBg] = ImVec4(0.80f, 0.80f, 0.80f, 0.20f);
  colors[ImGuiCol_ModalWindowDimBg] = ImVec4(0.00f, 0.00f, 0.00f, 0.75f);
}

// Initialize ImGui context and backends
void initializeImGui(GLFWwindow *window) {
  const char *glslVersion = "#version 460";

  IMGUI_CHECKVERSION();
  ImGui::CreateContext();
  ImPlot::CreateContext();
  ImGuiIO &io = ImGui::GetIO();
  io.ConfigFlags |= ImGuiConfigFlags_NavEnableKeyboard; // Enable keyboard navigation
  io.ConfigFlags |= ImGuiConfigFlags_DockingEnable;     // Enable Docking
  // io.ConfigFlags |= ImGuiConfigFlags_ViewportsEnable;   // Disable Multi-Viewport (causes
  // artifacts on Wayland)
  ImGuizmo::SetImGuiContext(ImGui::GetCurrentContext());
  ImGuizmo::SetOrthographic(false);

  // Load the vendored Spline Sans Mono as the primary UI font. If the asset is
  // missing (a stripped install), fall back to the built-in font so the atlas
  // is never empty -- an empty atlas crashes at first render.
  const std::string fontPath =
      platform::resourcePath("assets/fonts/spline-sans-mono/SplineSansMono-Regular.ttf");
  if (std::filesystem::exists(fontPath)) {
    io.Fonts->AddFontFromFileTTF(fontPath.c_str(), 16.0f);
  } else {
    io.Fonts->AddFontDefault();
  }

  setupImGuiStyle();

  ImGui_ImplGlfw_InitForOpenGL(window, true);
  ImGui_ImplOpenGL3_Init(glslVersion);
}

// Render controls help panel
void renderControlsHelpPanel() {
  ImGui::SetNextWindowPos(ImVec2(10, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 280), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls Help", nullptr, ImGuiWindowFlags_NoCollapse)) {
    auto &input = InputManager::instance();

    auto keyLabel = [&](KeyAction action) {
      return InputManager::getKeyName(
          input.getKeyForAction(action)); // NOLINT(readability-static-accessed-through-instance)
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

// NOLINTNEXTLINE(readability-function-cognitive-complexity) -- ImGui panel has many controls
void renderControlsSettingsPanel(RenderState &rs) {
  int &cameraModeIndex = rs.camera.cameraModeIndex;
  float &orbitRadius = rs.camera.orbitRadius;
  float &orbitSpeed = rs.camera.orbitSpeed;
  auto &input = InputManager::instance();

  // Stack on the right side
  ImGui::SetNextWindowPos(ImVec2(1020, 10), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(360, 520), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Controls", nullptr, ImGuiWindowFlags_NoCollapse)) {
    auto gamepadButtonName = [](int button) {
      switch (button) {
      case GLFW_GAMEPAD_BUTTON_A:
        return "A";
      case GLFW_GAMEPAD_BUTTON_B:
        return "B";
      case GLFW_GAMEPAD_BUTTON_X:
        return "X";
      case GLFW_GAMEPAD_BUTTON_Y:
        return "Y";
      case GLFW_GAMEPAD_BUTTON_LEFT_BUMPER:
        return "LB";
      case GLFW_GAMEPAD_BUTTON_RIGHT_BUMPER:
        return "RB";
      case GLFW_GAMEPAD_BUTTON_BACK:
        return "Back";
      case GLFW_GAMEPAD_BUTTON_START:
        return "Start";
      case GLFW_GAMEPAD_BUTTON_GUIDE:
        return "Guide";
      case GLFW_GAMEPAD_BUTTON_LEFT_THUMB:
        return "L3";
      case GLFW_GAMEPAD_BUTTON_RIGHT_THUMB:
        return "R3";
      case GLFW_GAMEPAD_BUTTON_DPAD_UP:
        return "DPad Up";
      case GLFW_GAMEPAD_BUTTON_DPAD_RIGHT:
        return "DPad Right";
      case GLFW_GAMEPAD_BUTTON_DPAD_DOWN:
        return "DPad Down";
      case GLFW_GAMEPAD_BUTTON_DPAD_LEFT:
        return "DPad Left";
      default:
        return "Unknown";
      }
    };
    auto gamepadAxisHint = [](int axis) {
      switch (axis) {
      case GLFW_GAMEPAD_AXIS_LEFT_X:
        return "Left X";
      case GLFW_GAMEPAD_AXIS_LEFT_Y:
        return "Left Y";
      case GLFW_GAMEPAD_AXIS_RIGHT_X:
        return "Right X";
      case GLFW_GAMEPAD_AXIS_RIGHT_Y:
        return "Right Y";
      case GLFW_GAMEPAD_AXIS_LEFT_TRIGGER:
        return "Left Trigger";
      case GLFW_GAMEPAD_AXIS_RIGHT_TRIGGER:
        return "Right Trigger";
      default:
        return "Unknown";
      }
    };
    auto applyControlPreset = [&](float mouseSens, float keySens, float scrollSens, float timeScale,
                                  float padDeadzone, float padLook, float padRoll, float padZoom,
                                  float padTrigger) {
      input.setMouseSensitivity(mouseSens);
      input.setKeyboardSensitivity(keySens);
      input.setScrollSensitivity(scrollSens);
      input.setTimeScale(timeScale);
      input.setGamepadDeadzone(padDeadzone);
      input.setGamepadLookSensitivity(padLook);
      input.setGamepadRollSensitivity(padRoll);
      input.setGamepadZoomSensitivity(padZoom);
      input.setGamepadTriggerZoomSensitivity(padTrigger);
    };
    ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Presets");
    ImGui::Separator();

    if (ImGui::Button("Balanced")) {
      Settings const defaults;
      applyControlPreset(defaults.mouseSensitivity, defaults.keyboardSensitivity,
                         defaults.scrollSensitivity, defaults.timeScale, defaults.gamepadDeadzone,
                         defaults.gamepadLookSensitivity, defaults.gamepadRollSensitivity,
                         defaults.gamepadZoomSensitivity, defaults.gamepadTriggerZoomSensitivity);
    }
    ImGui::SameLine();
    if (ImGui::Button("Precision")) {
      applyControlPreset(0.6f, 0.6f, 0.7f, 0.75f, 0.10f, 70.0f, 70.0f, 5.0f, 7.0f);
    }
    ImGui::SameLine();
    if (ImGui::Button("Fast")) {
      applyControlPreset(1.4f, 1.4f, 1.2f, 1.25f, 0.20f, 120.0f, 120.0f, 8.0f, 12.0f);
    }

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

    const char *const cameraModeLabels[] = {"Input", "Front", "Top", "Orbit"};
    ImGui::Combo("Camera Mode", &cameraModeIndex, cameraModeLabels, IM_ARRAYSIZE(cameraModeLabels));

    if (cameraModeIndex == static_cast<int>(CameraMode::Orbit)) {
      ImGui::SliderFloat("Orbit Radius", &orbitRadius, 2.0f, 50.0f);
      ImGui::SliderFloat("Orbit Speed (deg/s)", &orbitSpeed, 0.0f, 30.0f);
    }

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

    ImGui::Text("Status: %s",
                InputManager::isGamepadConnected()
                    ? "Connected"
                    : "Not detected"); // NOLINT(readability-static-accessed-through-instance)

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

    if (ImGui::Button("Reset Gamepad Mapping to Defaults")) {
      Settings const defaults;
      input.setGamepadYawAxis(defaults.gamepadYawAxis);
      input.setGamepadPitchAxis(defaults.gamepadPitchAxis);
      input.setGamepadRollAxis(defaults.gamepadRollAxis);
      input.setGamepadZoomAxis(defaults.gamepadZoomAxis);
      input.setGamepadZoomInAxis(defaults.gamepadZoomInAxis);
      input.setGamepadZoomOutAxis(defaults.gamepadZoomOutAxis);
      input.setGamepadResetButton(defaults.gamepadResetButton);
      input.setGamepadPauseButton(defaults.gamepadPauseButton);
      input.setGamepadToggleUIButton(defaults.gamepadToggleUIButton);
    }

    if (ImGui::CollapsingHeader("Gamepad Axis Mapping")) {
      int yawAxis = input.getGamepadYawAxis();
      if (ImGui::SliderInt("Yaw Axis", &yawAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadYawAxis(yawAxis);
      }
      ImGui::Text("Yaw uses: %s", gamepadAxisHint(yawAxis));
      int pitchAxis = input.getGamepadPitchAxis();
      if (ImGui::SliderInt("Pitch Axis", &pitchAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadPitchAxis(pitchAxis);
      }
      ImGui::Text("Pitch uses: %s", gamepadAxisHint(pitchAxis));
      int rollAxis = input.getGamepadRollAxis();
      if (ImGui::SliderInt("Roll Axis", &rollAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadRollAxis(rollAxis);
      }
      ImGui::Text("Roll uses: %s", gamepadAxisHint(rollAxis));
      int zoomAxis = input.getGamepadZoomAxis();
      if (ImGui::SliderInt("Zoom Axis", &zoomAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomAxis(zoomAxis);
      }
      ImGui::Text("Zoom uses: %s", gamepadAxisHint(zoomAxis));
      int zoomInAxis = input.getGamepadZoomInAxis();
      if (ImGui::SliderInt("Zoom In Trigger", &zoomInAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomInAxis(zoomInAxis);
      }
      ImGui::Text("Zoom In uses: %s", gamepadAxisHint(zoomInAxis));
      int zoomOutAxis = input.getGamepadZoomOutAxis();
      if (ImGui::SliderInt("Zoom Out Trigger", &zoomOutAxis, 0, GLFW_GAMEPAD_AXIS_LAST)) {
        input.setGamepadZoomOutAxis(zoomOutAxis);
      }
      ImGui::Text("Zoom Out uses: %s", gamepadAxisHint(zoomOutAxis));
    }

    if (ImGui::CollapsingHeader("Gamepad Button Mapping")) {
      int resetButton = input.getGamepadResetButton();
      if (ImGui::SliderInt("Reset Camera Button", &resetButton, 0, GLFW_GAMEPAD_BUTTON_LAST)) {
        input.setGamepadResetButton(resetButton);
      }
      ImGui::Text("Reset Camera: %s", gamepadButtonName(resetButton));

      int pauseButton = input.getGamepadPauseButton();
      if (ImGui::SliderInt("Pause Button", &pauseButton, 0, GLFW_GAMEPAD_BUTTON_LAST)) {
        input.setGamepadPauseButton(pauseButton);
      }
      ImGui::Text("Pause: %s", gamepadButtonName(pauseButton));

      int toggleUIButton = input.getGamepadToggleUIButton();
      if (ImGui::SliderInt("Toggle UI Button", &toggleUIButton, 0, GLFW_GAMEPAD_BUTTON_LAST)) {
        input.setGamepadToggleUIButton(toggleUIButton);
      }
      ImGui::Text("Toggle UI: %s", gamepadButtonName(toggleUIButton));
    }

    if (ImGui::CollapsingHeader("Gamepad Deadzone Monitor")) {
      auto axisBar = [&](const char *label, float value, float rawValue, float minValue,
                         float maxValue) {
        float normalized = (value - minValue) / (maxValue - minValue);
        normalized = std::clamp(normalized, 0.0f, 1.0f);
        ImGui::Text("%s: %.2f (raw %.2f)", label, static_cast<double>(value),
                    static_cast<double>(rawValue));
        ImGui::ProgressBar(normalized, ImVec2(0.0f, 0.0f));
      };

      int const yawAxis = input.getGamepadYawAxis();
      int const pitchAxis = input.getGamepadPitchAxis();
      int const rollAxis = input.getGamepadRollAxis();
      int const zoomAxis = input.getGamepadZoomAxis();
      int const zoomInAxis = input.getGamepadZoomInAxis();
      int const zoomOutAxis = input.getGamepadZoomOutAxis();

      std::string const yawLabel = std::string("Yaw (") + gamepadAxisHint(yawAxis) + ")";
      std::string const pitchLabel = std::string("Pitch (") + gamepadAxisHint(pitchAxis) + ")";
      std::string const rollLabel = std::string("Roll (") + gamepadAxisHint(rollAxis) + ")";
      std::string const zoomLabel = std::string("Zoom (") + gamepadAxisHint(zoomAxis) + ")";
      std::string const zoomInLabel = std::string("Zoom In (") + gamepadAxisHint(zoomInAxis) + ")";
      std::string const zoomOutLabel =
          std::string("Zoom Out (") + gamepadAxisHint(zoomOutAxis) + ")";

      axisBar(yawLabel.c_str(), input.getGamepadAxisFiltered(yawAxis),
              input.getGamepadAxisRaw(yawAxis), -1.0f, 1.0f);
      axisBar(pitchLabel.c_str(), input.getGamepadAxisFiltered(pitchAxis),
              input.getGamepadAxisRaw(pitchAxis), -1.0f, 1.0f);
      axisBar(rollLabel.c_str(), input.getGamepadAxisFiltered(rollAxis),
              input.getGamepadAxisRaw(rollAxis), -1.0f, 1.0f);
      axisBar(zoomLabel.c_str(), input.getGamepadAxisFiltered(zoomAxis),
              input.getGamepadAxisRaw(zoomAxis), -1.0f, 1.0f);
      axisBar(zoomInLabel.c_str(), input.getGamepadAxisRaw(zoomInAxis),
              input.getGamepadAxisRaw(zoomInAxis), 0.0f, 1.0f);
      axisBar(zoomOutLabel.c_str(), input.getGamepadAxisRaw(zoomOutAxis),
              input.getGamepadAxisRaw(zoomOutAxis), 0.0f, 1.0f);
    }

    if (ImGui::CollapsingHeader("Key Bindings", ImGuiTreeNodeFlags_DefaultOpen)) {
      if (input.isRemappingKey()) {
        ImGui::TextColored(
            ImVec4(1.0f, 0.8f, 0.0f, 1.0f), "Press a key to bind to: %s",
            InputManager::getActionName(
                input
                    .getRemappingAction())); // NOLINT(readability-static-accessed-through-instance)
        if (ImGui::Button("Cancel")) {
          input.cancelKeyRemapping();
        }
      } else {
        if (ImGui::BeginTable("KeyBindings", 2, ImGuiTableFlags_SizingStretchProp)) {
          for (int i = 0; i < static_cast<int>(KeyAction::COUNT); i++) {
            auto const action = static_cast<KeyAction>(i);
            const char *actionName = InputManager::getActionName(
                action); // NOLINT(readability-static-accessed-through-instance)
            int const currentKey = input.getKeyForAction(action);
            std::string const keyName = InputManager::getKeyName(
                currentKey); // NOLINT(readability-static-accessed-through-instance)

            ImGui::TableNextRow();
            ImGui::TableNextColumn();
            ImGui::Text("%s", actionName);
            ImGui::TableNextColumn();

            ImGui::PushID(i);
            char buttonLabel[64];
            std::snprintf(buttonLabel, sizeof(buttonLabel), "[%s]##%d", keyName.c_str(),
                          i); // NOLINT(cert-err33-c) -- diagnostic output, return unused
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
      auto &settings = SettingsManager::instance().get();
      settings.cameraMode = cameraModeIndex;
      settings.orbitRadius = orbitRadius;
      settings.orbitSpeed = orbitSpeed;
      SettingsManager::instance().save();
    }
    ImGui::SameLine();
    if (ImGui::Button("Reset Defaults")) {
      SettingsManager::instance().resetToDefaults();
      input.syncFromSettings();
      auto &settings = SettingsManager::instance().get();
      cameraModeIndex = settings.cameraMode;
      orbitRadius = settings.orbitRadius;
      orbitSpeed = settings.orbitSpeed;
      SettingsManager::instance().save();
    }
  }
  ImGui::End();
}

void renderGizmoPanel(RenderState &rs) {
  bool &gizmoEnabled = rs.camera.gizmoEnabled;
  ImGuizmo::OPERATION &operation = rs.camera.gizmoOperation;
  ImGuizmo::MODE &mode = rs.camera.gizmoMode;
  glm::mat4 &gizmoTransform = rs.camera.gizmoTransform;
  ImGui::SetNextWindowPos(ImVec2(1020, 220), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 220), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Gizmo", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable Gizmo Target", &gizmoEnabled);

    const char *const operationLabels[] = {"Translate", "Rotate", "Scale"};
    int operationIndex = 0;
    switch (operation) {
    case ImGuizmo::TRANSLATE:
      operationIndex = 0;
      break;
    case ImGuizmo::ROTATE:
      operationIndex = 1;
      break;
    case ImGuizmo::SCALE:
      operationIndex = 2;
      break;
    default:
      operationIndex = 0;
      break;
    }

    if (ImGui::Combo("Operation", &operationIndex, operationLabels,
                     IM_ARRAYSIZE(operationLabels))) {
      if (operationIndex == 0) {
        operation = ImGuizmo::TRANSLATE;
      } else if (operationIndex == 1) {
        operation = ImGuizmo::ROTATE;
      } else {
        operation = ImGuizmo::SCALE;
      }
    }

    const char *const modeLabels[] = {"World", "Local"};
    int modeIndex = (mode == ImGuizmo::WORLD) ? 0 : 1;
    if (ImGui::Combo("Mode", &modeIndex, modeLabels, IM_ARRAYSIZE(modeLabels))) {
      mode = (modeIndex == 0) ? ImGuizmo::WORLD : ImGuizmo::LOCAL;
    }

    if (ImGui::Button("Reset Target")) {
      gizmoTransform = glm::mat4(1.0f);
    }

    auto const target = glm::vec3(gizmoTransform[3]); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                      // -- glm::mat has no .at()
    ImGui::Text("Target: %.2f %.2f %.2f", static_cast<double>(target.x),
                static_cast<double>(target.y), static_cast<double>(target.z));
  }
  ImGui::End();
}

void renderDisplaySettingsPanel(RenderState &rs, GLFWwindow *window, int windowWidth,
                                int windowHeight) {
  int &swapInterval = rs.display.swapInterval;
  float &renderScale = rs.display.renderScale;
  auto &input = InputManager::instance();
  auto &settings = SettingsManager::instance().get();

  // Stack below Controls
  ImGui::SetNextWindowPos(ImVec2(1020, 540), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(360, 220), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Display", nullptr, ImGuiWindowFlags_NoCollapse)) {
    bool fullscreen = input.isFullscreen();
    if (ImGui::Checkbox("Fullscreen", &fullscreen)) {
      input.toggleFullscreen();
      settings.fullscreen = fullscreen;
      if (!fullscreen) {
        glfwGetWindowSize(window, &settings.windowWidth, &settings.windowHeight);
      }
    }

    const char *const swapModes[] = {"Off (0)", "VSync (1)", "Triple (2)"};
    int interval = std::clamp(swapInterval, 0, 2);
    if (ImGui::Combo("Swap Interval", &interval, swapModes, IM_ARRAYSIZE(swapModes))) {
      swapInterval = interval;
      settings.swapInterval = swapInterval;
      glfwSwapInterval(swapInterval);
    }

    if (ImGui::SliderFloat("Render Scale", &renderScale, 0.25f, 1.5f)) {
      settings.renderScale = renderScale;
    }

    const char *const presets[] = {"Native", "720p",         "1080p",       "1440p",
                                   "4K",     "UW 3440x1440", "UW 5120x2160"};
    static int presetIndex = 0;
    if (ImGui::Combo("Resolution Preset", &presetIndex, presets, IM_ARRAYSIZE(presets))) {
      float targetHeight = 0.0f;
      float targetWidth = 0.0f;
      bool useWidth = false;
      switch (presetIndex) {
      case 0:
        targetHeight = 0.0f;
        break;
      case 1:
        targetHeight = 720.0f;
        break;
      case 2:
        targetHeight = 1080.0f;
        break;
      case 3:
        targetHeight = 1440.0f;
        break;
      case 4:
        targetHeight = 2160.0f;
        break;
      case 5:
        targetWidth = 3440.0f;
        useWidth = true;
        break;
      case 6:
        targetWidth = 5120.0f;
        useWidth = true;
        break;
      default:
        targetHeight = 0.0f;
        break;
      }

      float newScale = 1.0f;
      if (presetIndex != 0 && windowWidth > 0 && windowHeight > 0) {
        if (useWidth) {
          newScale = targetWidth / static_cast<float>(windowWidth);
        } else {
          newScale = targetHeight / static_cast<float>(windowHeight);
        }
      }
      renderScale = newScale;
      settings.renderScale = renderScale;
    }

    float const clampedScale = std::clamp(renderScale, 0.25f, 1.5f);
    int const targetWidth =
        std::max(1, static_cast<int>(static_cast<float>(windowWidth) * clampedScale));
    int const targetHeight =
        std::max(1, static_cast<int>(static_cast<float>(windowHeight) * clampedScale));
    ImGui::Text("Window: %dx%d", windowWidth, windowHeight);
    ImGui::Text("Render: %dx%d", targetWidth, targetHeight);
  }
  ImGui::End();
}

void renderBackgroundPanel(RenderState &rs) {
  auto &settings = SettingsManager::instance().get();
  const std::vector<BackgroundAsset> &assets = rs.background.backgroundAssets;
  int &backgroundIndex = rs.background.backgroundIndex;
  float &parallaxStrength = settings.backgroundParallaxStrength;
  float &driftStrength = settings.backgroundDriftStrength;
  std::array<float, K_BACKGROUND_LAYERS> &layerDepth = rs.background.backgroundLayerDepth;
  std::array<float, K_BACKGROUND_LAYERS> &layerScale = rs.background.backgroundLayerScale;
  std::array<float, K_BACKGROUND_LAYERS> &layerIntensity = rs.background.backgroundLayerIntensity;
  std::array<float, K_BACKGROUND_LAYERS> &layerLodBias = rs.background.backgroundLayerLodBias;

  // Stack on the left side
  ImGui::SetNextWindowPos(ImVec2(10, 300), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 260), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Background", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable Background", &settings.backgroundEnabled);
    ImGui::SliderFloat("Intensity", &settings.backgroundIntensity, 0.0f, 2.0f);

    if (assets.empty()) {
      ImGui::TextDisabled("No manifest assets loaded.");
    } else {
      backgroundIndex = std::clamp(backgroundIndex, 0, static_cast<int>(assets.size() - 1));
      const char *preview = assets.at(static_cast<std::size_t>(backgroundIndex)).title.c_str();
      if (ImGui::BeginCombo("Background Asset", preview)) {
        for (int i = 0; std::cmp_less(i, assets.size()); ++i) {
          bool const selected = (i == backgroundIndex);
          if (ImGui::Selectable(assets.at(static_cast<std::size_t>(i)).title.c_str(), selected)) {
            backgroundIndex = i;
            settings.backgroundId = assets.at(static_cast<std::size_t>(i)).id;
          }
          if (selected) {
            ImGui::SetItemDefaultFocus();
          }
        }
        ImGui::EndCombo();
      }
    }

    ImGui::Separator();
    ImGui::SliderFloat("Parallax Strength", &parallaxStrength, 0.0f, 0.01f, "%.6f");
    ImGui::SliderFloat("Drift Strength", &driftStrength, 0.0f, 0.05f, "%.4f");

    if (ImGui::TreeNode("Layers")) {
      for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
        ImGui::PushID(i);
        ImGui::SliderFloat("Depth", &layerDepth.at(static_cast<std::size_t>(i)), 0.0f, 2.0f);
        ImGui::SliderFloat("Scale", &layerScale.at(static_cast<std::size_t>(i)), 0.5f, 2.0f);
        ImGui::SliderFloat("Weight", &layerIntensity.at(static_cast<std::size_t>(i)), 0.0f, 2.0f);
        ImGui::SliderFloat("LOD Bias", &layerLodBias.at(static_cast<std::size_t>(i)), 0.0f, 6.0f,
                           "%.2f");
        ImGui::Separator();
        ImGui::PopID();
      }
      ImGui::TreePop();
    }
  }
  ImGui::End();
}

void renderWiregridPanel(RenderState &rs) {
  bool &wiregridEnabled = rs.wiregrid.wiregridEnabled;
  WiregridParams &params = rs.wiregrid.wiregridParams;
  glm::vec4 &color = rs.wiregrid.wiregridColor;
  ImGui::SetNextWindowPos(ImVec2(10, 570), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(320, 290), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Wiregrid", nullptr, ImGuiWindowFlags_NoCollapse)) {
    constexpr const char *kModeItems[] = {"Beauty", "Diagnostic"};
    int modeIndex = params.mode == WiregridParams::Mode::Diagnostic ? 1 : 0;
    ImGui::Checkbox("Enable Wiregrid", &wiregridEnabled);
    if (ImGui::Combo("Mode", &modeIndex, kModeItems, IM_ARRAYSIZE(kModeItems))) {
      applyWiregridModeProfile(modeIndex == 1 ? WiregridParams::Mode::Diagnostic
                                              : WiregridParams::Mode::Beauty,
                               params, color);
    }
    ImGui::TextDisabled("%s",
                        params.mode == WiregridParams::Mode::Diagnostic
                            ? "Diagnostic: clearer and stronger for teaching/debug."
                            : "Beauty: subtler and secondary to the scene.");
    ImGui::Checkbox("Show Ergosphere", &params.showErgosphere);
    ImGui::SliderFloat("Grid Scale", &params.gridScale, 0.25f, 4.0f);
    ImGui::SliderFloat("Motion Scale", &params.motionScale, 0.0f, 4.0f);
    ImGui::SliderFloat("Infall Scale", &params.infallScale, 0.0f, 2.0f);
    ImGui::SliderFloat("Strength", &params.strength, 0.1f, 2.0f);
    ImGui::SliderFloat("Scene Preserve", &params.scenePreserve, 0.0f, 1.0f);
    ImGui::Separator();
    ImGui::ColorEdit4("Color", reinterpret_cast<float *>(&color));
  }
  ImGui::End();
}

void renderRmlUiPanel(RenderState &rs) {
  bool &rmluiEnabled = rs.overlays.rmluiEnabled;
  ImGui::SetNextWindowPos(ImVec2(1020, 450), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 140), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("RmlUi", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable RmlUi overlay", &rmluiEnabled);
    ImGui::TextDisabled("Experimental: placeholder only");
  }
  ImGui::End();
}

void renderPerformancePanel(RenderState &rs, float cpuFrameMs) {
  bool &gpuTimingEnabled = rs.timing.gpuTimingEnabled;
  const GpuTimerSet &timers = rs.timing.gpuTimers;
  const TimingHistory &history = rs.timing.timingHistory;
  bool &perfOverlayEnabled = rs.overlays.perfOverlayEnabled;
  float &perfOverlayScale = rs.overlays.perfOverlayScale;
  bool &depthPrepassEnabled = rs.probes.depthPrepassEnabled;
  // Stack below Wiregrid
  ImGui::SetNextWindowPos(ImVec2(10, 800), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 200), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("Performance", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("GPU Timing", &gpuTimingEnabled);
    ImGui::Checkbox("HUD Overlay", &perfOverlayEnabled);
    ImGui::SliderFloat("HUD Scale", &perfOverlayScale, 0.5f, 2.0f);

    // Depth pre-pass (for future mesh-based disk rendering)
    ImGui::BeginDisabled(true); // Disabled until mesh geometry exists
    ImGui::Checkbox("Depth Pre-pass", &depthPrepassEnabled);
    ImGui::EndDisabled();
    if (ImGui::IsItemHovered(ImGuiHoveredFlags_AllowWhenDisabled)) {
      ImGui::SetTooltip("Reduces overdraw for mesh geometry.\nCurrently unused (ray marching has "
                        "zero overdraw).");
    }
    auto const cpuFrameMsD = static_cast<double>(cpuFrameMs);
    double const fps = cpuFrameMs > 0.0f ? 1000.0 / cpuFrameMsD : 0.0;
    ImGui::Text("CPU frame: %.2f ms (%.1f FPS)", cpuFrameMsD, fps);

    if (timers.initialized) {
      ImGui::Separator();
      ImGui::Text("GPU Fragment:  %.2f ms", timers.blackholeFragment.lastMs);
      ImGui::Text("GPU Compute:   %.2f ms", timers.blackholeCompute.lastMs);
      ImGui::Text("GPU Bloom:     %.2f ms", timers.bloom.lastMs);
      ImGui::Text("GPU Tonemap:   %.2f ms", timers.tonemap.lastMs);
      ImGui::Text("GPU Depth:     %.2f ms", timers.depth.lastMs);
      ImGui::Text("GPU GRMHD:     %.2f ms", timers.grmhdSlice.lastMs);
    } else {
      ImGui::TextDisabled("GPU timings inactive");
    }

    if (history.count > 0 && ImPlot::BeginPlot("Frame Times (ms)", ImVec2(-1, 140))) {
      ImPlot::SetupAxes(nullptr, "ms", ImPlotAxisFlags_NoTickLabels, ImPlotAxisFlags_AutoFit);
      ImPlot::PlotLine("CPU", history.cpuMs.data(), history.count, 1.0, 0.0, ImPlotLineFlags_None,
                       history.offset);
      ImPlot::PlotLine("GPU Frag", history.gpuFragmentMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::PlotLine("GPU Comp", history.gpuComputeMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::PlotLine("GPU Depth", history.gpuDepthMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::PlotLine("GPU GRMHD", history.gpuGrmhdSliceMs.data(), history.count, 1.0, 0.0,
                       ImPlotLineFlags_SkipNaN, history.offset);
      ImPlot::EndPlot();
    }

    if (ImGui::Button("Dump Frame CSV")) {
      writeTimingHistoryCsv(history, "logs/perf/frame_times.csv");
    }
    ImGui::SameLine();
    ImGui::TextDisabled("logs/perf/frame_times.csv");
  }
  ImGui::End();
}

void resetLayout(ImGuiID dockspaceId) {
  ImGui::DockBuilderRemoveNode(dockspaceId);
  ImGui::DockBuilderAddNode(dockspaceId, ImGuiDockNodeFlags_DockSpace);
  ImGui::DockBuilderSetNodeSize(dockspaceId, ImGui::GetMainViewport()->Size);

  ImGuiID dockMainId = dockspaceId;
  ImGuiID dockLeftId =
      ImGui::DockBuilderSplitNode(dockMainId, ImGuiDir_Left, 0.30f, nullptr, &dockMainId);
  ImGuiID const dockLeftDownId =
      ImGui::DockBuilderSplitNode(dockLeftId, ImGuiDir_Down, 0.50f, nullptr, &dockLeftId);

  // Dock Windows
  ImGui::DockBuilderDockWindow("Viewport", dockMainId);

  // Left Upper: Main Settings
  ImGui::DockBuilderDockWindow("Settings", dockLeftId);
  ImGui::DockBuilderDockWindow("Display", dockLeftId);
  ImGui::DockBuilderDockWindow("Background", dockLeftId);

  // Left Lower: Controls, Performance, Tools
  ImGui::DockBuilderDockWindow("Controls", dockLeftDownId);
  ImGui::DockBuilderDockWindow("Performance", dockLeftDownId);
  ImGui::DockBuilderDockWindow("Wiregrid", dockLeftDownId);
  ImGui::DockBuilderDockWindow("Depth Effects", dockLeftDownId);
  ImGui::DockBuilderDockWindow("Gizmo", dockLeftDownId);
  ImGui::DockBuilderDockWindow("Controls Help", dockLeftDownId);
  ImGui::DockBuilderDockWindow("RmlUi", dockLeftDownId);

  ImGui::DockBuilderFinish(dockspaceId);
}

} // namespace ui
