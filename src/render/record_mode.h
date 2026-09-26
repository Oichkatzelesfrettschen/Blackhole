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

#include <string_view>

#include <glm/ext/vector_float4.hpp>

struct GLFWwindow;
class InputManager;

namespace platform {
struct CliOptions;
} // namespace platform

namespace blackhole {

struct WiregridParams;
struct RenderState;

/** @brief Framing preset for one named showcase-orbit composition. */
struct ShowcaseOrbitComposition {
  const char *name;
  const char *backgroundId;
  float frameOffsetX; ///< Aim shift along camera right, in half-widths of the frame.
  float frameOffsetY; ///< Aim shift along camera up, in half-heights of the frame.
  float pitchDeg;
  float distance;
  float fovDeg; ///< Vertical field of view of the traced image (bhPixelUv, d_ray_dir).
  float exposure; ///< The record exposure rule at the composition's camera and spin 0.
  float backgroundIntensity;
  float backgroundYawDeg;
  float backgroundPitchDeg;
  float backgroundOffsetX;
  float backgroundOffsetY;
  float sweepDeg;
};

/*
 * Record exposure rule. A record profile's toneExposure places the 99th
 * percentile L99 of the Rec. 709 luminance over the frame's disk pixels at
 * display value 0.9 after tonemapping.frag's ACES fit and gamma:
 * toneExposure = ACES^-1(0.9^gamma) / L99, with ACES^-1(0.9^2.35) = 0.900
 * and ACES^-1(0.9^2.25) = 0.934. L99 comes from the raw frame
 * (--export-raw-frame: texBlackhole before bloom and tone mapping) at the
 * profile's own camera and spin. The sky, whose 99th percentile lies in the
 * lensed Milky Way rather than in point stars, goes to display 0.8 instead
 * (ACES^-1(0.8^2.35) = 0.464, ACES^-1(0.8^2.25) = 0.483); it sets
 * compare-orbit-near's exposure, which renders no disk, and the cinematic
 * background intensity.
 */

/** @brief Tone-map exposure of the showcase-orbit profile when no composition
 *         matches: the record exposure rule at the fallback camera (pitch -6,
 *         distance 14, fov 37.2738) and the default spin, L99 = 0.256. */
inline constexpr float K_SHOWCASE_ORBIT_FALLBACK_EXPOSURE = 3.51f;

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
 *         warmup; sets exportPerformed so it runs once. No-op when neither export
 *         path is set. */
void exportFrameOnce(RenderState &rs, const platform::CliOptions &cli);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_RECORD_MODE_H
