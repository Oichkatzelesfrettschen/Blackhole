/**
 * @file panels.h
 * @brief ImGui context setup, dockspace layout, and the standalone control
 *        panels (controls, gizmo, display, background, wiregrid, RmlUi,
 *        performance). Each panel takes the RenderState it edits, plus any
 *        genuine per-frame transients (window handle, frame time).
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
void renderControlsSettingsPanel(blackhole::RenderState &rs);

/** @brief ImGuizmo target toggle and operation/mode selectors. */
void renderGizmoPanel(blackhole::RenderState &rs);

/** @brief Fullscreen, vsync, render-scale, and resolution preset controls. */
void renderDisplaySettingsPanel(blackhole::RenderState &rs, GLFWwindow *window, int windowWidth,
                                int windowHeight);

/** @brief Background asset picker and parallax layer controls. */
void renderBackgroundPanel(blackhole::RenderState &rs);

/** @brief Boyer-Lindquist wiregrid overlay toggles and tuning sliders. */
void renderWiregridPanel(blackhole::RenderState &rs);

/** @brief RmlUi overlay enable toggle. */
void renderRmlUiPanel(blackhole::RenderState &rs);

/** @brief GPU timing toggles, HUD overlay controls, and the frame-time plot. */
void renderPerformancePanel(blackhole::RenderState &rs, float cpuFrameMs);

/** @brief Rebuilds the default dockspace layout for all named windows. */
void resetLayout(ImGuiID dockspaceId);

} // namespace ui

#endif // BLACKHOLE_UI_PANELS_H
