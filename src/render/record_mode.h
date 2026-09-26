/**
 * @file record_mode.h
 * @brief Offline record-mode and frame-export framing, setup, and output.
 *
 * ShowcaseOrbitComposition is the per-composition framing table the
 * showcase-orbit record profile draws from (camera pitch/distance/fov,
 * background asset and orientation, sweep and frame offsets). The lookup and
 * the beauty-wiregrid tuning are shared by the CLI validation in main and the
 * record-mode clusters in the render loop. The setup, per-frame camera drive,
 * frame capture, and one-shot export functions consume the parsed CliOptions
 * and drive the render loop's offline-output paths.
 */

#ifndef BLACKHOLE_RENDER_RECORD_MODE_H
#define BLACKHOLE_RENDER_RECORD_MODE_H

#include <optional>
#include <string>
#include <string_view>

#include <glm/ext/vector_float4.hpp>

#include "render/render_state.h"

struct GLFWwindow;
class InputManager;

namespace platform {
struct CliOptions;
} // namespace platform

namespace blackhole {

struct WiregridParams;

/** @brief Framing preset for one named showcase-orbit composition. */
struct ShowcaseOrbitComposition {
  const char *name;
  const char *backgroundId;
  float frameOffsetX;
  float frameOffsetY;
  float pitchDeg;
  float distance;
  float fovDeg;
  float exposure;
  float backgroundIntensity;
  float backgroundYawDeg;
  float backgroundPitchDeg;
  float backgroundOffsetX;
  float backgroundOffsetY;
  float sweepDeg;
};

/** @brief Returns the composition matching name, or nullptr if none matches. */
const ShowcaseOrbitComposition *findShowcaseOrbitComposition(std::string_view name);

/** @brief Applies per-composition beauty-wiregrid tuning; no-op unless params is
 *         in Beauty mode. */
void applyShowcaseBeautyWiregridTuning(std::string_view compositionName, WiregridParams &params,
                                       glm::vec4 &color);

/** @brief One-time record-mode setup: creates the output directory, resizes the
 *         window to the record resolution, and applies the selected profile's
 *         render/camera/background state. Returns false if the output directory
 *         cannot be created (the caller should abort); the caller invokes this
 *         once, gated on an empty recordFramesDir and recordInitDone. */
bool applyRecordProfileSetup(RenderState &rs, const platform::CliOptions &cli, InputManager &input,
                             GLFWwindow *window);

/** @brief Drives the record camera and spin from the selected profile's path for
 *         the current frame index. No-op when recordFramesDir is empty. */
void applyRecordCameraPath(RenderState &rs, const platform::CliOptions &cli, InputManager &input);

/** @brief Captures the tonemapped scene texture to frame_NNNNNN.png and advances
 *         the record frame index. No-op until the record warmup has elapsed and
 *         the render targets are valid. */
void captureRecordFrame(RenderState &rs, const platform::CliOptions &cli);

/** @brief One-shot --export-frame (PNG from the tonemapped texture) and
 *         --export-raw-frame (PFM from the HDR blackhole texture) after a short
 *         warmup; sets exportPerformed so it runs once, and exportFailed when a
 *         requested file was refused or not written. No-op when neither export
 *         path is set. */
void exportFrameOnce(RenderState &rs, const platform::CliOptions &cli);

/**
 * @brief Output time of the frame being recorded, or std::nullopt.
 *
 * Under --record-frames the frame at index recordFrameIndex shows output time
 * recordFrameIndex / K_CINEMATIC_FPS seconds; interactive runs return
 * std::nullopt.
 */
std::optional<double> recordOutputSeconds(const platform::CliOptions &cli, int recordFrameIndex);

/**
 * @brief Fraction of the record camera path at frame @p recordFrameIndex.
 *
 * A run writes frames [recordStartFrame, recordStartFrame + recordFramesTotal)
 * and the showcase-orbit and compare-orbit-near paths span frames 0 through
 * the run's last frame, so progress is recordFrameIndex / (last frame index),
 * in [0, 1]. It depends on the absolute frame index, as the output clock
 * does: a run resumed at --start-frame k with the remaining frame count
 * writes each frame exactly as the uninterrupted run does.
 */
float recordPathProgress(const platform::CliOptions &cli, int recordFrameIndex);

/**
 * @brief Content time of one frame in seconds: what time-driven shading reads.
 *
 * Recorded frames take recordOutputSeconds, so the film grain, disk and sky
 * rotation, background drift, and depth-cue motion of a frame depend on its
 * index alone and two runs, or a --start-frame resume, write identical
 * frames. Interactive frames take @p wallSeconds.
 */
double frameContentSeconds(const platform::CliOptions &cli, int recordFrameIndex,
                           double wallSeconds);

/**
 * @brief Why the requested exports cannot run in @p scene, or std::nullopt.
 *
 * --export-raw-frame reads the HDR scene target, which the tesseract scene's
 * SPECULATIVE label never reaches, so the tesseract scene rejects it; main
 * checks this before opening a window and exits with status 2.
 */
std::optional<std::string> exportConflictForScene(const platform::CliOptions &cli,
                                                  RenderState::SceneMode scene);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_RECORD_MODE_H
