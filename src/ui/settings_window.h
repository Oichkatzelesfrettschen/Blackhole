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

/**
 * @brief True when a Kerr-tracer disk (bhDiskEmission, d_disk_emission)
 *        renders: the fragment path runs the physical tracer, the GLSL compute
 *        path or the compute/fragment comparison runs, or the CUDA backend is
 *        on. The disk transfer mode, peak temperature and brightness controls
 *        affect the image only then; the legacy fragment tracer (adiskColor)
 *        reads none of them.
 */
bool kerrDiskShadingActive(const blackhole::RenderState &rs);

/**
 * @brief True when the displayed image comes from the legacy fragment tracer
 *        (adiskColor), the complement of kerrDiskShadingActive: CUDA bypasses
 *        both GLSL paths, the compute path owns the displayed texture, and
 *        compare mode runs the fragment side through the Kerr branch
 *        (interopParityMode, bindFragmentUniforms) so both sides trace the
 *        same geodesics. The legacy disk and redshift controls affect the
 *        image only then.
 */
bool legacyFragmentTracerActive(const blackhole::RenderState &rs);

} // namespace ui

#endif // BLACKHOLE_UI_SETTINGS_WINDOW_H
