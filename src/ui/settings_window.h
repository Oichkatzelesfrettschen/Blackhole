/**
 * @file settings_window.h
 * @brief Main Settings tab-bar window (Visuals / GRMHD / Physics / Compute)
 *        and the in-loop overlay panels: curve overlay, bloom, tonemap, and
 *        depth effects. Each takes the RenderState groups it edits; settings
 *        persistence goes through SettingsManager.
 */

#ifndef BLACKHOLE_UI_SETTINGS_WINDOW_H
#define BLACKHOLE_UI_SETTINGS_WINDOW_H

#include <string>

#include "render/render_state.h"

namespace ui {

/** @brief Tab-bar Settings window: disk visuals, GRMHD loading/playback, physics, compute path. */
void renderSettingsWindow(blackhole::RenderState &rs);

/** @brief Curve overlay window plotting the --curve-tsv file; no-op when closed. */
void renderCurveOverlayWindow(blackhole::RenderState &rs, const std::string &curveTsvPath);

/** @brief Bloom composite sliders (strength, threshold, knee, tone). */
void renderBloomPanel(blackhole::RenderState &rs);

/** @brief Tonemap toggles and exposure/gamma sliders. */
void renderTonemapPanel(blackhole::RenderState &rs);

/** @brief Depth cue controls: fog, edge outlines, desaturation, depth of field. */
void renderDepthEffectsPanel(blackhole::RenderState &rs);

} // namespace ui

#endif // BLACKHOLE_UI_SETTINGS_WINDOW_H
