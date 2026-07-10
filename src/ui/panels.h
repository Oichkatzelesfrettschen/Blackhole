/**
 * @file panels.h
 * @brief ImGui context setup, dockspace layout, and the standalone control
 *        panels (controls, gizmo, display, background, wiregrid, RmlUi,
 *        performance). Each panel takes references into the RenderState
 *        group it edits.
 */

#ifndef BLACKHOLE_UI_PANELS_H
#define BLACKHOLE_UI_PANELS_H

#include <array>
#include <vector>

#include <imgui.h>
#include <ImGuizmo.h>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/vector_float4.hpp>

#include "render/render_state.h"

struct GLFWwindow;

namespace ui {

/** @brief Applies the Beauty/Diagnostic tuning profile to wiregrid params and color. */
void applyWiregridModeProfile(blackhole::WiregridParams::Mode mode,
                              blackhole::WiregridParams &params, glm::vec4 &color);

/** @brief Creates the ImGui/ImPlot/ImGuizmo context, style, and GLFW/GL3 backends. */
void initializeImGui(GLFWwindow *window);

/** @brief Help window listing keyboard, mouse, and gamepad controls. */
void renderControlsHelpPanel();

/** @brief Camera mode/orbit, sensitivity, gamepad mapping, and key-binding editor. */
void renderControlsSettingsPanel(int &cameraModeIndex, float &orbitRadius, float &orbitSpeed);

/** @brief ImGuizmo target toggle and operation/mode selectors. */
void renderGizmoPanel(bool &gizmoEnabled, ImGuizmo::OPERATION &operation, ImGuizmo::MODE &mode,
                      glm::mat4 &gizmoTransform);

/** @brief Fullscreen, vsync, render-scale, and resolution preset controls. */
void renderDisplaySettingsPanel(GLFWwindow *window, int &swapInterval, float &renderScale,
                                int windowWidth, int windowHeight);

/** @brief Background asset picker and parallax layer controls. */
void renderBackgroundPanel(const std::vector<blackhole::BackgroundAsset> &assets,
                           int &backgroundIndex, float &parallaxStrength, float &driftStrength,
                           std::array<float, blackhole::K_BACKGROUND_LAYERS> &layerDepth,
                           std::array<float, blackhole::K_BACKGROUND_LAYERS> &layerScale,
                           std::array<float, blackhole::K_BACKGROUND_LAYERS> &layerIntensity,
                           std::array<float, blackhole::K_BACKGROUND_LAYERS> &layerLodBias);

/** @brief Boyer-Lindquist wiregrid overlay toggles and tuning sliders. */
void renderWiregridPanel(bool &wiregridEnabled, blackhole::WiregridParams &params,
                         glm::vec4 &color);

/** @brief RmlUi overlay enable toggle. */
void renderRmlUiPanel(bool &rmluiEnabled);

/** @brief GPU timing toggles, HUD overlay controls, and the frame-time plot. */
void renderPerformancePanel(bool &gpuTimingEnabled, const blackhole::GpuTimerSet &timers,
                            const blackhole::TimingHistory &history, float cpuFrameMs,
                            bool &perfOverlayEnabled, float &perfOverlayScale,
                            bool &depthPrepassEnabled);

/** @brief Rebuilds the default dockspace layout for all named windows. */
void resetLayout(ImGuiID dockspaceId);

} // namespace ui

#endif // BLACKHOLE_UI_PANELS_H
