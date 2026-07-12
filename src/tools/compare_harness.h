/**
 * @file compare_harness.h
 * @brief Compute/fragment parity harness: per-pixel diff statistics, texture
 *        readback, PPM/PFM snapshot writers, CSV summaries, and the camera +
 *        physics preset table swept by the parity test suite (Issue-009).
 */

#ifndef BLACKHOLE_TOOLS_COMPARE_HARNESS_H
#define BLACKHOLE_TOOLS_COMPARE_HARNESS_H

#include <array>
#include <cstddef>
#include <string>
#include <vector>

#include <glbinding/gl/types.h>

#include "input.h"
#include "render/interop_uniforms.h"

namespace blackhole {

/** @brief Summary statistics for a per-pixel difference image used in compute/fragment parity tests. */
struct DiffStats {
  float meanAbs = 0.0f; ///< Mean absolute per-channel difference across sampled pixels.
  float maxAbs  = 0.0f; ///< Maximum absolute per-channel difference.
  float rms     = 0.0f; ///< Root-mean-square per-channel difference.
  bool  valid   = false; ///< False if inputs were invalid or no pixels were sampled.
};

/**
 * @brief Reads a centered sampleSize x sampleSize window from two textures and
 *        returns per-channel difference statistics.
 */
DiffStats sampleTextureDiff(gl::GLuint texA, gl::GLuint texB, int width, int height,
                            int sampleSize);

/** @brief Reads a full RGBA32F texture into @p out; returns false on invalid input. */
bool readTextureRGBA(gl::GLuint texture, int width, int height, std::vector<float> &out);

/** @brief Writes the RGB channels of an RGBA float buffer as a binary PFM (bottom-up, -1.0 scale). */
bool writePfmRgb(const std::string &path, const std::vector<float> &rgba, int width, int height);

/** @brief Per-channel difference statistics over two full RGBA float buffers. */
DiffStats computeDiffStats(const std::vector<float> &a, const std::vector<float> &b);

/** @brief Counts pixels whose max RGB channel difference exceeds @p threshold. */
std::size_t countDiffOutliers(const std::vector<float> &a, const std::vector<float> &b,
                              float threshold);

/** @brief Writes an RGBA float buffer as a P6 PPM, scaling and clamping each channel. */
bool writePpm(const std::string &path, const std::vector<float> &rgba, int width, int height,
              float scale);

/** @brief Writes the absolute per-channel difference of two buffers as a P6 PPM. */
bool writeDiffPpm(const std::string &path, const std::vector<float> &a, const std::vector<float> &b,
                  int width, int height, float scale);

/** @brief Path for a numbered, tagged compare snapshot under logs/compare/. */
std::string compareSnapshotPath(int index, const std::string &tag);

/** @brief Path of the compare summary CSV under logs/compare/. */
std::string compareSummaryPath();

/** @brief Path of the compare uniforms CSV under logs/compare/. */
std::string compareUniformsPath();

/** @brief Appends one parity-comparison row (diff stats, thresholds, outliers) to the summary CSV. */
void appendCompareSummary(const std::string &path, int index, const std::string &primaryTag,
                          const std::string &secondaryTag, int width, int height,
                          const DiffStats &stats, float diffScale, bool wroteOutputs,
                          bool wroteDiff, float threshold, bool exceeded, double timeSec,
                          float kerrSpin, bool grbEnabled, float grbTime, int outlierCount,
                          int outlierLimit, float outlierFrac);

/** @brief Appends one row of the uniform values both render paths received to the uniforms CSV. */
void appendCompareUniforms(const std::string &path, int index, const std::string &label,
                           const InteropUniforms &interop, bool compareBaseline,
                           bool compareOverrides, bool backgroundEnabled, bool noiseEnabled,
                           bool grmhdEnabled, bool spectralEnabled, bool grbEnabled,
                           bool photonSphereEnabled);

/**
 * @brief A named camera + physics configuration used by the compute/fragment parity test suite.
 *
 * Each preset is rendered with both the GL fragment path and the CUDA compute
 * path; DiffStats are compared to detect arithmetic divergence (Issue-009).
 */
struct ComparePreset {
  const char *label{};               ///< Human-readable name shown in the compare UI.
  CameraMode  mode{CameraMode::Input}; ///< Camera positioning mode for this preset.
  CameraState camera;                ///< Camera state (used when mode == Input).
  float       orbitRadius{};         ///< Orbit radius in gravitational radii (Orbit mode).
  float       orbitSpeed{};          ///< Orbit angular speed in degrees per second.
  float       kerrSpin{};            ///< Dimensionless Kerr spin parameter a* in [0, 1).
};

constexpr float K_COMPARE_KERR_SPIN = 0.8f;

constexpr std::array<ComparePreset, 12> K_COMPARE_PRESETS = {{
    {.label = "Input Near (Schw)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 30.0f, .pitch = -10.0f, .roll = 0.0f, .distance = 8.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Input Near (Kerr)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 30.0f, .pitch = -10.0f, .roll = 0.0f, .distance = 8.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Input Far (Schw)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 60.0f, .pitch = 10.0f, .roll = 0.0f, .distance = 20.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Input Far (Kerr)",
     .mode = CameraMode::Input,
     .camera =
         CameraState{.yaw = 60.0f, .pitch = 10.0f, .roll = 0.0f, .distance = 20.0f, .fov = 45.0f},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Front (Schw)",
     .mode = CameraMode::Front,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Front (Kerr)",
     .mode = CameraMode::Front,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Top (Schw)",
     .mode = CameraMode::Top,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Top (Kerr)",
     .mode = CameraMode::Top,
     .camera = CameraState{},
     .orbitRadius = 15.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Orbit Near (Schw)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 10.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Orbit Near (Kerr)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 10.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
    {.label = "Orbit Far (Schw)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 20.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = 0.0f},
    {.label = "Orbit Far (Kerr)",
     .mode = CameraMode::Orbit,
     .camera = CameraState{},
     .orbitRadius = 20.0f,
     .orbitSpeed = 0.0f,
     .kerrSpin = K_COMPARE_KERR_SPIN},
}};

} // namespace blackhole

#endif // BLACKHOLE_TOOLS_COMPARE_HARNESS_H
