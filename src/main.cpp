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
#include <algorithm>
#include <cassert>
#include <cmath>
#include <csignal>
#include <cstdlib>
#include <cstdio>
#include <cstring>

#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/boolean.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>
#include <sys/types.h>
#include <unistd.h>

#include <cpptrace/basic.hpp>
#include <cpptrace/exceptions.hpp>
#include <cpptrace/forward.hpp>
#include <cpptrace/utils.hpp>
#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/geometric.hpp>
#include <glm/trigonometric.hpp>
#include <nlohmann/json_fwd.hpp>

// C++ system headers
#include <array>
#include <cstdint>
#include <cstdlib>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <ios>
#include <iostream>
#include <limits>
#include <map>
#include <ostream>
#include <sstream>
#include <string>
#include <thread>
#include <utility>
#include <vector>

// Third-party library headers
#include "constants.h"
#include "kerr.h"
#include "schwarzschild.h"
#ifndef BLACKHOLE_HAS_CPPTRACE
#if __has_include(<cpptrace/cpptrace.hpp>)
#define BLACKHOLE_HAS_CPPTRACE 1
#else
#define BLACKHOLE_HAS_CPPTRACE 0
#endif
#endif
#if BLACKHOLE_HAS_CPPTRACE
#endif
#include <GLFW/glfw3.h>
#include <imgui.h>
#include <imgui_internal.h>
#include <ImGuizmo.h>
#include <implot.h>

#include <glm/gtc/type_ptr.hpp>
#include <nlohmann/json.hpp>

// Local headers
#include "GLDebugMessageCallback.h"
#include "grmhd_packed_loader.h"
#include "grmhd_pbo_uploader.h"
#include "grmhd_streaming.h"
#include "hud_overlay.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include "input.h"
#include "overlay.h"
#include "physics/hawking_renderer.h"
#include "physics/lut.h"
#include "physics/synchrotron.h"
#include "render.h"
#include "render/noise_texture_cache.h"
#include "render/interop_uniform_registry.h"
#include "render/interop_uniforms.h"
#include "tools/compare_harness.h"
#include "platform/crash_handler.h"
#include "platform/resource_paths.h"
#include "render/gpu_timing.h"
#include "render/post_process.h"
#include "rmlui_overlay.h"
#include "settings.h"
#include "shader.h"
#include "shader_manager.h"
#include "texture.h"
#include <stb_image_write.h>
#include "cinematic.h"
#include "tracy_support.h"

#ifndef BLACKHOLE_HAS_CUDA
#define BLACKHOLE_HAS_CUDA 0
#endif
#ifndef BLACKHOLE_APP_VARIANT_GLSL_ONLY
#define BLACKHOLE_APP_VARIANT_GLSL_ONLY 0
#endif
#ifndef BLACKHOLE_APP_VARIANT_CUDA_ONLY
#define BLACKHOLE_APP_VARIANT_CUDA_ONLY 0
#endif
#if BLACKHOLE_APP_VARIANT_GLSL_ONLY && BLACKHOLE_APP_VARIANT_CUDA_ONLY
#error "Blackhole desktop variant cannot be both GLSL-only and CUDA-only"
#endif
#if BLACKHOLE_APP_VARIANT_CUDA_ONLY && !BLACKHOLE_HAS_CUDA
#error "Blackhole CUDA-only desktop variant requires BLACKHOLE_HAS_CUDA=1"
#endif
#if BLACKHOLE_HAS_CUDA
#include "cuda/cuda_render_manager.h"
#endif

namespace { // NOLINT(misc-use-anonymous-namespace) -- file-scope helpers

constexpr int K_BACKGROUND_LAYERS = 3;
constexpr bool kAppVariantGlslOnly = BLACKHOLE_APP_VARIANT_GLSL_ONLY != 0;
constexpr bool kAppVariantCudaOnly = BLACKHOLE_APP_VARIANT_CUDA_ONLY != 0;
constexpr const char *kWindowTitle = kAppVariantCudaOnly
                                         ? "BlackholeCUDA"
                                         : (kAppVariantGlslOnly ? "BlackholeGLSL" : "Blackhole");

// Extracted modules keep their call sites unqualified (STATE-2 extraction).
using platform::resourcePath;
using blackhole::PostProcessPass;
using blackhole::GpuTimer;
using blackhole::GpuTimerSet;
using blackhole::TimingHistory;
using blackhole::gpuTimingPath;
using blackhole::appendGpuTimingSample;
using blackhole::writeTimingHistoryCsv;



/**
 * @brief Convert spherical yaw/pitch angles to a Cartesian camera position.
 *
 * @param yawDeg   Horizontal rotation in degrees (0 = +Z axis).
 * @param pitchDeg Vertical elevation in degrees (positive = above equator).
 * @param radius   Distance from origin in world units.
 * @return World-space camera position on the sphere of the given radius.
 */
glm::vec3 cameraPositionFromYawPitch(float yawDeg, float pitchDeg, float radius) {
  float const yawRad = glm::radians(yawDeg);
  float const pitchRad = glm::radians(pitchDeg);
  return {radius * std::cos(pitchRad) * std::sin(yawRad), radius * std::sin(pitchRad),
          radius * std::cos(pitchRad) * std::cos(yawRad)};
}

/**
 * @brief Build an orthonormal camera basis (right, up, forward) from a look-at pair plus roll.
 *
 * Handles the degenerate case where forward is nearly parallel to world-up by
 * falling back to the +Z world axis as the up reference.
 *
 * @param cameraPos World-space camera origin.
 * @param target    World-space look-at point.
 * @param rollDeg   Camera roll in degrees applied after the standard basis is constructed.
 * @return Column-major mat3 with columns [right, up, forward].
 */
glm::mat3 buildCameraBasis(const glm::vec3 &cameraPos, const glm::vec3 &target, float rollDeg) {
  glm::vec3 const forward = glm::normalize(target - cameraPos);
  glm::vec3 worldUp(0.0f, 1.0f, 0.0f);
  if (std::abs(glm::dot(forward, worldUp)) > 0.99f) {
    worldUp = glm::vec3(0.0f, 0.0f, 1.0f);
  }

  glm::vec3 right = glm::normalize(glm::cross(forward, worldUp));
  glm::vec3 up = glm::normalize(glm::cross(right, forward));

  if (std::abs(rollDeg) > 0.001f) {
    float const rollRad = glm::radians(rollDeg);
    float const cosRoll = std::cos(rollRad);
    float const sinRoll = std::sin(rollRad);
    glm::vec3 const rolledRight = right * cosRoll + up * sinRoll;
    glm::vec3 const rolledUp = -right * sinRoll + up * cosRoll;
    right = rolledRight;
    up = rolledUp;
  }

  return {right, up, forward};
}

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

constexpr std::array<ShowcaseOrbitComposition, 5> K_SHOWCASE_ORBIT_COMPOSITIONS = {{
    {"centered", "nasa_deep_starmap_galactic", 0.0f, 0.0f, -8.0f, 21.0f, 60.0f, 3.05f, 0.74f, -18.0f, 6.0f, 0.00f, 0.00f, 8.0f},
    {"left-third", "nasa_deep_starmap", 0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, -34.0f, 7.0f, 0.05f, -0.02f, 7.0f},
    {"right-third", "nasa_deep_starmap_galactic", -0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, 18.0f, 7.0f, -0.05f, -0.02f, 7.0f},
    {"wide-left", "eso_milkyway_brunier", 0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.75f, 0.70f, -42.0f, 8.0f, 0.08f, -0.03f, 6.0f},
    {"wide-right", "nasa_deep_starmap_galactic", -0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.9f, 0.80f, 26.0f, 8.0f, -0.08f, -0.03f, 6.0f},
}};

const ShowcaseOrbitComposition *findShowcaseOrbitComposition(std::string_view name) {
  for (const auto &composition : K_SHOWCASE_ORBIT_COMPOSITIONS) {
    if (name == composition.name) {
      return &composition;
    }
  }
  return nullptr;
}

bool readTextFile(const std::string &path, std::string &out) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::ostringstream buffer;
  buffer << file.rdbuf();
  out = buffer.str();
  return !out.empty();
}

void printUsage(const char *argv0) {
  std::printf("Usage: %s [--curve-tsv <path>] [--export-frame <path.png>]"
              " [--export-raw-frame <path.pfm>]"
              " [--record-frames <dir> <N>] [--record-profile <name>]\n", argv0);
  std::printf("  --curve-tsv <path>       Load a 2-column TSV and plot it in ImGui.\n");
  std::printf("  --export-frame <path>    Render one frame, save as PNG, then exit.\n");
  std::printf("  --export-raw-frame <path> Export raw texBlackhole HDR RGB as PFM, then exit.\n");
  std::printf("  --record-frames <dir> N  Record N profile-driven frames as PNG into <dir>.\n");
  std::printf("                           N defaults to %d (3 min @ 60 fps).\n",
              K_CINEMATIC_FRAMES);
  std::printf("  --record-profile <name>  Recording profile: cinematic | compare-orbit-near | showcase-orbit.\n");
  std::printf("  --start-frame N          Start recording from frame N (default: 0).\n");
  std::printf("  --record-yaw <deg>       Override record camera yaw.\n");
  std::printf("  --record-pitch <deg>     Override record camera pitch.\n");
  std::printf("  --record-distance <r>    Override record camera distance.\n");
  std::printf("  --record-fov <deg>       Override record camera field of view.\n");
  std::printf("  --record-exposure <x>    Override record tone-map exposure.\n");
  std::printf("  --record-sweep-deg <x>   Override orbit sweep degrees across frames.\n");
  std::printf("  --record-composition <n> Showcase framing: centered | left-third | right-third | wide-left | wide-right.\n");
  std::printf("  --record-frame-x <n>     Override horizontal framing offset in half-frame units.\n");
  std::printf("  --record-frame-y <n>     Override vertical framing offset in half-frame units.\n");
  std::printf("  --record-background-id <id>  Override showcase background asset id.\n");
  std::printf("  --record-bg-yaw <deg>    Override showcase background yaw.\n");
  std::printf("  --record-bg-pitch <deg>  Override showcase background pitch.\n");
}

void drawCurvePlot(const OverlayCurve2D &curve, const ImVec2 &size) {
  ImDrawList *drawList = ImGui::GetWindowDrawList();
  ImVec2 const p0 = ImGui::GetCursorScreenPos();
  ImVec2 const p1 = ImVec2(p0.x + size.x, p0.y + size.y);

  ImGui::InvisibleButton("curve_plot", size);

  drawList->AddRectFilled(p0, p1, IM_COL32(20, 20, 20, 255), 0.0f);
  drawList->AddRect(p0, p1, IM_COL32(200, 200, 200, 255), 0.0f);

  float xSpan = curve.max.x - curve.min.x;
  float ySpan = curve.max.y - curve.min.y;
  if (xSpan == 0.0f) {
    xSpan = 1.0f;
  }
  if (ySpan == 0.0f) {
    ySpan = 1.0f;
  }

  const float pad = 6.0f;
  ImVec2 const q0 = ImVec2(p0.x + pad, p0.y + pad);
  ImVec2 const q1 = ImVec2(p1.x - pad, p1.y - pad);
  float const w = std::max(1.0f, q1.x - q0.x);
  float const h = std::max(1.0f, q1.y - q0.y);

  std::vector<ImVec2> pts;
  pts.reserve(curve.points.size());
  for (const auto &pt : curve.points) {
    float const nx = (pt.x - curve.min.x) / xSpan;
    float const ny = (pt.y - curve.min.y) / ySpan;
    float const px = q0.x + (nx * w);
    float const py = q1.y - (ny * h);
    pts.emplace_back(px, py);
  }

  if (pts.size() >= 2) {
    drawList->AddPolyline(pts.data(), static_cast<int>(pts.size()), IM_COL32(80, 200, 255, 255), 0,
                          2.0f);
  }

  ImGui::Text("x:[%.4g, %.4g]  y:[%.4g, %.4g]  n=%d", static_cast<double>(curve.min.x),
              static_cast<double>(curve.max.x), static_cast<double>(curve.min.y),
              static_cast<double>(curve.max.y), static_cast<int>(curve.points.size()));
}

bool hasExtension(const char *name) {
  GLint count = 0;
  glGetIntegerv(GL_NUM_EXTENSIONS, &count);
  for (GLint i = 0; i < count; ++i) {
    const char *ext =
        reinterpret_cast<const char *>(glGetStringi(GL_EXTENSIONS, static_cast<GLuint>(i)));
    if (ext != nullptr && std::string(ext) == name) {
      return true;
    }
  }
  return false;
}

bool supportsDrawId() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_shader_draw_parameters");
}

bool supportsMultiDrawIndirect() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs43 = (major > 4) || (major == 4 && minor >= 3);
  return versionIs43 || hasExtension("GL_ARB_multi_draw_indirect");
}

bool supportsIndirectCount() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_indirect_parameters");
}

/** @brief Metadata for a single background skybox asset loaded from manifest.json. */
struct BackgroundAsset {
  std::string id;        ///< Unique asset identifier matching the manifest "id" field.
  std::string title;     ///< Human-readable display name shown in the UI.
  std::string path;      ///< Relative file path to the 2D background image on disk.
  std::string skyboxDir; ///< Directory containing 6 cubemap face PNGs (empty = use default).
};

/**
 * @brief GPU-side draw command for glMultiDrawArraysIndirect.
 *
 * Layout matches the OpenGL specification for GL_DRAW_ARRAYS_INDIRECT_BUFFER.
 */
struct DrawArraysIndirectCommand {
  GLuint count = 0;        ///< Number of vertices to draw.
  GLuint primCount = 0;    ///< Number of instances.
  GLuint first = 0;        ///< Starting index in the enabled arrays.
  GLuint baseInstance = 0; ///< Base instance for instanced attributes.
};

/**
 * @brief Per-instance data uploaded to the GPU for instanced background rendering.
 *
 * Matches the std140 layout expected by the corresponding GLSL shader.
 */
struct DrawInstanceGpu {
  glm::vec4 offsetScale; ///< xy = NDC offset, zw = scale factors.
  glm::vec4 tint;        ///< RGBA tint multiplier applied in the fragment shader.
  glm::vec4 flags;       ///< Bit-packed feature flags (x = layer index, etc.).
};

/**
 * @brief Parameters for the Boyer-Lindquist coordinate wiregrid overlay.
 *
 * Controls the fragment-shader wiregridOverlay() call (wiregrid.glsl) and the
 * matching CUDA kernel path.  The overlay replaces the former Euclidean
 * Flamm's-paraboloid mesh, which was geometrically inconsistent with the
 * ray-traced geodesic view.
 */
struct WiregridParams {
  enum class Mode { Beauty = 0, Diagnostic = 1 };

  Mode  mode            = Mode::Beauty; ///< Intended use: beauty scene vs diagnostic teaching.
  bool  showErgosphere = true; ///< Render ergosphere boundary and interior glow.
  float gridScale      = 1.0f; ///< Grid density: 1.0 = pi/6 angular spacing; >1 = denser.
  float motionScale    = 1.0f; ///< Frame-dragging azimuth advection strength.
  float infallScale    = 0.6f; ///< Inward radial-shell advection strength.
  float strength       = 1.0f; ///< Overall overlay alpha multiplier after scene attenuation.
  float scenePreserve  = 1.0f; ///< 1 = fully defer to scene luminance, 0 = diagnostic override.
};

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

void applyShowcaseBeautyWiregridTuning(std::string_view compositionName, WiregridParams &params,
                                       glm::vec4 &color) {
  if (params.mode != WiregridParams::Mode::Beauty) {
    return;
  }

  if (compositionName == "wide-right") {
    params.gridScale = 0.78f;
    params.motionScale = 0.48f;
    params.infallScale = 0.16f;
    params.strength = 0.48f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.19f, 0.58f, 0.90f, 0.11f);
    return;
  }
  if (compositionName == "right-third") {
    params.gridScale = 0.84f;
    params.motionScale = 0.54f;
    params.infallScale = 0.20f;
    params.strength = 0.56f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.20f, 0.60f, 0.91f, 0.12f);
    return;
  }
  if (compositionName == "wide-left") {
    params.gridScale = 0.82f;
    params.motionScale = 0.50f;
    params.infallScale = 0.18f;
    params.strength = 0.52f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.19f, 0.58f, 0.89f, 0.11f);
  }
}

std::vector<BackgroundAsset> loadBackgroundAssets() {
  std::vector<BackgroundAsset> assets;
  std::string text;
  if (!readTextFile(resourcePath("assets/backgrounds/manifest.json"), text)) {
    return assets;
  }
  auto json = nlohmann::json::parse(text, nullptr, false);
  if (json.is_discarded() || !json.contains("assets") || !json.at("assets").is_array()) {
    return assets;
  }
  for (const auto &entry : json.at("assets")) {
    BackgroundAsset asset;
    asset.id = entry.value("id", "");
    asset.title = entry.value("title", asset.id);
    asset.path = entry.value("path", "");
    asset.skyboxDir = entry.value("skyboxDir", "");
    if (!asset.path.empty() && !std::filesystem::path(asset.path).is_absolute()) {
      asset.path = resourcePath(asset.path);
    }
    if (!asset.skyboxDir.empty() && !std::filesystem::path(asset.skyboxDir).is_absolute()) {
      asset.skyboxDir = resourcePath(asset.skyboxDir);
    }
    if (!asset.id.empty() && !asset.path.empty()) {
      assets.push_back(std::move(asset));
    }
  }
  return assets;
}

int findBackgroundIndex(const std::vector<BackgroundAsset> &assets, const std::string &id) {
  for (std::size_t i = 0; i < assets.size(); ++i) {
    if (assets.at(i).id == id) {
      return static_cast<int>(i);
    }
  }
  return 0;
}

bool parseJsonNumber(const std::string &text, const std::string &key, double &out) {
  std::string const needle = "\"" + key + "\"";
  std::size_t pos = text.find(needle);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find(':', pos);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find_first_of("+-0123456789.", pos);
  if (pos == std::string::npos) {
    return false;
  }
  const char *start = text.c_str() + pos;
  char *end = nullptr;
  out = std::strtod(start, &end);
  return end != start;
}

// Compare/parity harness (DiffStats, snapshot + CSV writers, preset
// table) lives in src/tools/compare_harness.*; InteropUniforms in
// src/render/interop_uniforms.h. Unqualified call sites below.
using blackhole::DiffStats;
using blackhole::InteropUniforms;
using blackhole::ComparePreset;
using blackhole::K_COMPARE_PRESETS;
using blackhole::sampleTextureDiff;
using blackhole::readTextureRGBA;
using blackhole::writePfmRgb;
using blackhole::computeDiffStats;
using blackhole::countDiffOutliers;
using blackhole::writePpm;
using blackhole::writeDiffPpm;
using blackhole::compareSnapshotPath;
using blackhole::compareSummaryPath;
using blackhole::compareUniformsPath;
using blackhole::appendCompareSummary;
using blackhole::appendCompareUniforms;

constexpr int K_INTEGRATOR_DEBUG_NAN_FLAG = 1;
constexpr int K_INTEGRATOR_DEBUG_RANGE_FLAG = 2;

void applyInteropUniforms(RenderToTextureInfo &rtti, const InteropUniforms &interop,
                          bool parityMode, bool hawkingEnabled, float hawkingTempScale,
                          float hawkingIntensity, bool hawkingUseLUTs, double blackHoleMass) {
  // Registry-driven float uniforms: one row in
  // interop_uniform_registry.h writes the struct field, this map entry,
  // and the compute-path call below.
#define BH_X(field, glslName, defaultValue)                                  \
  rtti.floatUniforms[glslName] = interop.field;
  BH_INTEROP_UNIFORM_FLOATS(BH_X)
#undef BH_X

  // Typed specials and per-call extras.
  rtti.vec3Uniforms["cameraPos"] = interop.cameraPos;
  rtti.mat3Uniforms["cameraBasis"] = interop.cameraBasis;
  rtti.floatUniforms["interopMaxSteps"] = static_cast<float>(interop.maxSteps);
  rtti.floatUniforms["interopParityMode"] = parityMode ? 1.0f : 0.0f;

  // Hawking radiation uniforms
  rtti.floatUniforms["hawkingGlowEnabled"] = hawkingEnabled ? 1.0f : 0.0f;
  rtti.floatUniforms["hawkingTempScale"] = hawkingTempScale;
  rtti.floatUniforms["hawkingGlowIntensity"] = hawkingIntensity;
  rtti.floatUniforms["useHawkingLUTs"] = hawkingUseLUTs ? 1.0f : 0.0f;
  rtti.floatUniforms["blackHoleMass"] = static_cast<float>(blackHoleMass);
  // Wiregrid BL-coord overlay (task A2) -- filled by caller via wiregridEnabled flag
  // (wiregridEnabled/ShowErgo/GridScale are set in the render loop after this call)
}

void applyInteropComputeUniforms(GLuint program, const InteropUniforms &interop, int width,
                                 int height) {
  // Registry-driven float uniforms: same table rows as the fragment
  // path, so the two paths cannot drift on which uniforms exist.
#define BH_X(field, glslName, defaultValue)                                  \
  glUniform1f(glGetUniformLocation(program, glslName), interop.field);
  BH_INTEROP_UNIFORM_FLOATS(BH_X)
#undef BH_X

  // Typed specials.
  glUniform2f(glGetUniformLocation(program, "resolution"), static_cast<float>(width),
              static_cast<float>(height));
  glUniformMatrix3fv(glGetUniformLocation(program, "cameraBasis"), 1, GL_FALSE,
                     glm::value_ptr(interop.cameraBasis));
  glUniform3f(glGetUniformLocation(program, "cameraPos"), interop.cameraPos.x, interop.cameraPos.y,
              interop.cameraPos.z);
  glUniform1i(glGetUniformLocation(program, "interopMaxSteps"), interop.maxSteps);
}

void applyHawkingUniforms(GLuint program, const physics::HawkingRenderer &renderer, bool enabled,
                          float tempScale, float intensity, bool useLUTs, double blackHoleMass) {
  if (!renderer.isReady()) {
    return;
  }

  physics::HawkingGlowParams params;
  params.enabled = enabled;
  params.tempScale = tempScale;
  params.intensity = intensity;
  params.useLUTs = useLUTs;

  renderer.setShaderUniforms(program, blackHoleMass, params);
}

bool loadLutCsv(const std::string &path, std::vector<float> &values) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::string line;
  bool first = true;
  while (std::getline(file, line)) {
    if (first) {
      first = false;
      continue;
    }
    if (line.empty()) {
      continue;
    }
    std::size_t const comma = line.find(',');
    if (comma == std::string::npos) {
      continue;
    }
    const char *start = line.c_str() + comma + 1;
    char *end = nullptr;
    double value = std::strtod(start, &end);
    if (end == start) {
      continue;
    }
    values.push_back(static_cast<float>(value));
  }
  return !values.empty();
}

bool loadLutAssets(physics::Lut1D &emissivity, physics::Lut1D &redshift, float &spinOut) {
  std::vector<float> emissivityValues;
  std::vector<float> redshiftValues;
  if (!loadLutCsv(resourcePath("assets/luts/emissivity_lut.csv"), emissivityValues)) {
    return false;
  }
  if (!loadLutCsv(resourcePath("assets/luts/redshift_lut.csv"), redshiftValues)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile(resourcePath("assets/luts/lut_meta.json"), metaText)) {
    return false;
  }
  double rInOverRs = 0.0;
  double rOutOverRs = 0.0;
  double spin = 0.0;
  if (!parseJsonNumber(metaText, "r_in_over_rs", rInOverRs)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_out_over_rs", rOutOverRs)) {
    return false;
  }
  parseJsonNumber(metaText, "spin", spin);

  emissivity.values = std::move(emissivityValues);
  emissivity.rMin = static_cast<float>(rInOverRs);
  emissivity.rMax = static_cast<float>(rOutOverRs);
  redshift.values = std::move(redshiftValues);
  redshift.rMin = static_cast<float>(rInOverRs);
  redshift.rMax = static_cast<float>(rOutOverRs);
  spinOut = static_cast<float>(spin);
  return true;
}

bool loadSpectralLutAssets(std::vector<float> &values, float &wavelengthMin, float &wavelengthMax) {
  values.clear();
  if (!loadLutCsv(resourcePath("assets/luts/rt_spectrum_lut.csv"), values)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile(resourcePath("assets/luts/rt_spectrum_meta.json"), metaText)) {
    return false;
  }
  double waveMin = 0.0;
  double waveMax = 0.0;
  if (!parseJsonNumber(metaText, "wavelength_min_angstrom", waveMin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "wavelength_max_angstrom", waveMax)) {
    return false;
  }
  wavelengthMin = static_cast<float>(waveMin);
  wavelengthMax = static_cast<float>(waveMax);
  return true;
}

bool loadGrbModulationLutAssets(std::vector<float> &values, float &timeMin, float &timeMax) {
  values.clear();
  if (!loadLutCsv(resourcePath("assets/luts/grb_modulation_lut.csv"), values)) {
    return false;
  }
  std::string metaText;
  if (!readTextFile(resourcePath("assets/luts/grb_modulation_meta.json"), metaText)) {
    return false;
  }
  double tMin = 0.0;
  double tMax = 0.0;
  if (!parseJsonNumber(metaText, "t_min", tMin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "t_max", tMax)) {
    return false;
  }
  timeMin = static_cast<float>(tMin);
  timeMax = static_cast<float>(tMax);
  return true;
}

void glfwErrorCallback(int error, const char *description) {
  fprintf(stderr, "Glfw Error %d: %s\n", error,
          description); // NOLINT(cert-err33-c) -- diagnostic output, return unused
}

// GLFW callbacks that delegate to InputManager
void keyCallback(GLFWwindow * /*window*/, int key, int scancode, int action, int mods) {
  InputManager::instance().onKey(key, scancode, action, mods);
}

void mouseButtonCallback(GLFWwindow * /*window*/, int button, int action, int mods) {
  InputManager::instance().onMouseButton(button, action, mods);
}

void cursorPosCallback(GLFWwindow * /*window*/, double x, double y) {
  InputManager::instance().onMouseMove(x, y);
}

void scrollCallback(GLFWwindow * /*window*/, double xoffset, double yoffset) {
  InputManager::instance().onScroll(xoffset, yoffset);
}

// Initialize OpenGL debug context (call after loader init)
void initializeGLDebugContext() {
#ifdef ENABLE_GL_DEBUG_CONTEXT
  // Check if debug context is available (OpenGL 4.3+ or KHR_debug extension)
  GLint contextFlags = 0;
  glGetIntegerv(GL_CONTEXT_FLAGS, &contextFlags);
  const auto flags = static_cast<ContextFlagMask>(contextFlags);

  if ((flags & GL_CONTEXT_FLAG_DEBUG_BIT) != ContextFlagMask{}) {
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

void configureParallelShaderCompile() {
  const char *env = std::getenv("BLACKHOLE_PARALLEL_SHADER_COMPILE");
  if (env == nullptr || std::string(env) != "1") {
    return;
  }
  if (!hasExtension("GL_KHR_parallel_shader_compile")) {
    std::cout << "Parallel shader compile requested but not supported.\n";
    return;
  }
  unsigned int threads = std::thread::hardware_concurrency();
  if (threads == 0) {
    threads = 1;
  }
  const char *threadEnv = std::getenv("BLACKHOLE_SHADER_COMPILE_THREADS");
  if (threadEnv != nullptr) {
    threads = static_cast<unsigned int>(
        std::max(1, std::atoi(threadEnv))); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                            // -- env var, invalid input defaults to 0
  }
  glMaxShaderCompilerThreadsKHR(static_cast<GLuint>(threads));
  std::cout << "Parallel shader compile enabled (" << threads << " threads).\n";
}

// Initialize GLFW and create window
GLFWwindow *initializeWindow(int width, int height) {
  glfwSetErrorCallback(glfwErrorCallback);
  if (glfwInit() == 0) {
    return nullptr;
  }

  glfwWindowHint(GLFW_DECORATED, GLFW_TRUE);
  const char *hiddenWindowEnv = std::getenv("BLACKHOLE_WINDOW_HIDDEN");
  if (hiddenWindowEnv != nullptr && std::string(hiddenWindowEnv) == "1") {
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    glfwWindowHint(GLFW_FOCUSED, GLFW_FALSE);
#if GLFW_VERSION_MAJOR > 3 || (GLFW_VERSION_MAJOR == 3 && GLFW_VERSION_MINOR >= 3)
    glfwWindowHint(GLFW_FOCUS_ON_SHOW, GLFW_FALSE);
#endif
  }
  glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
  glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
  glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
  glfwWindowHint(GLFW_OPENGL_FORWARD_COMPAT, GLFW_TRUE);
  const char *noErrorEnv = std::getenv("BLACKHOLE_NO_ERROR_CONTEXT");
  if (noErrorEnv != nullptr && std::string(noErrorEnv) == "1") {
    glfwWindowHint(GLFW_CONTEXT_NO_ERROR, GLFW_TRUE);
  }

#ifdef ENABLE_GL_DEBUG_CONTEXT
  // Request debug context for OpenGL error reporting
  glfwWindowHint(GLFW_OPENGL_DEBUG_CONTEXT, GLFW_TRUE);
#endif

  GLFWwindow *window = glfwCreateWindow(width, height, kWindowTitle, nullptr, nullptr);
  if (window == nullptr) {
    return nullptr;
  }

  glfwMakeContextCurrent(window);

  // Set up input callbacks
  glfwSetKeyCallback(window, keyCallback);
  glfwSetMouseButtonCallback(window, mouseButtonCallback);
  glfwSetCursorPosCallback(window, cursorPosCallback);
  glfwSetScrollCallback(window, scrollCallback);

  glfwSetWindowPos(window, 0, 0);

  glbinding::initialize(glfwGetProcAddress);

  GLint glMajor = 0;
  GLint glMinor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &glMajor);
  glGetIntegerv(GL_MINOR_VERSION, &glMinor);
  if (glMajor < 4 || (glMajor == 4 && glMinor < 6)) {
    std::fprintf(stderr, "OpenGL 4.6 required, found %d.%d\n", glMajor,
                 glMinor); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    glfwDestroyWindow(window);
    return nullptr;
  }

  // Initialize GL debug context after loader init
  initializeGLDebugContext();
  configureParallelShaderCompile();

  return window;
}

// Configure custom ImGui style for "Blackhole" theme (16-bit Voxel Aesthetic)
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
void renderControlsSettingsPanel(int &cameraModeIndex, float &orbitRadius, float &orbitSpeed) {
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

void renderGizmoPanel(bool &gizmoEnabled, ImGuizmo::OPERATION &operation, ImGuizmo::MODE &mode,
                      glm::mat4 &gizmoTransform) {
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

void renderDisplaySettingsPanel(GLFWwindow *window, int &swapInterval, float &renderScale,
                                int windowWidth, int windowHeight) {
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

void renderBackgroundPanel(const std::vector<BackgroundAsset> &assets, int &backgroundIndex,
                           float &parallaxStrength, float &driftStrength,
                           std::array<float, K_BACKGROUND_LAYERS> &layerDepth,
                           std::array<float, K_BACKGROUND_LAYERS> &layerScale,
                           std::array<float, K_BACKGROUND_LAYERS> &layerIntensity,
                           std::array<float, K_BACKGROUND_LAYERS> &layerLodBias) {
  auto &settings = SettingsManager::instance().get();

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

void renderWiregridPanel(bool &wiregridEnabled, WiregridParams &params, glm::vec4 &color) {
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

void renderRmlUiPanel(bool &rmluiEnabled) {
  ImGui::SetNextWindowPos(ImVec2(1020, 450), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(300, 140), ImGuiCond_FirstUseEver);

  if (ImGui::Begin("RmlUi", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Enable RmlUi overlay", &rmluiEnabled);
    ImGui::TextDisabled("Experimental: placeholder only");
  }
  ImGui::End();
}

// Cleanup resources
void cleanup(GLFWwindow *window) {
  // Sync and save settings before shutdown
  InputManager::instance().syncToSettings();
  SettingsManager::instance().save();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
  ShaderWatcher::instance().stop();
#endif
  InputManager::instance().shutdown();
  ImGui_ImplOpenGL3_Shutdown();
  ImGui_ImplGlfw_Shutdown();
  ImPlot::DestroyContext();
  ImGui::DestroyContext();
  glfwDestroyWindow(window);
  glfwTerminate();
}


// Reified render/application state: every value that was a function-local
// static in main() lives here, grouped by subsystem. One instance is
// constructed in main() after window and ImGui initialization; the
// grouped substructs let UI panels and dispatch paths take exactly the
// state they touch (debt-ledger.md tranche render-state-reification).
constexpr int kMaxBloomIterations = 8;

struct RenderState {
  struct CameraGroup {
    int cameraModeIndex = static_cast<int>(CameraMode::Input);
    float orbitTime = 0.0f;
    float orbitRadius = 15.0f;
    float orbitSpeed = 6.0f;
    bool gizmoEnabled = false;
    ImGuizmo::OPERATION gizmoOperation = ImGuizmo::TRANSLATE;
    ImGuizmo::MODE gizmoMode = ImGuizmo::WORLD;
    glm::mat4 gizmoTransform = glm::mat4(1.0f);
    bool cameraSettingsLoaded = false;
  } camera;

  struct DisplayGroup {
    float depthFar = 100.0f;
    bool displaySettingsLoaded = false;
    int swapInterval = 1;
    float renderScale = 1.0f;
  } display;

  struct OverlaysGroup {
    OverlayCurve2D curveOverlay;
    bool curveOverlayLoaded = false;
    HudOverlay controlsOverlay;
    bool controlsOverlayReady = false;
    bool controlsOverlayConfigInit = false;
    bool controlsOverlayEnabled = true;
    float controlsOverlayScale = 1.1f;
    HudOverlay perfOverlay;
    bool const perfOverlayReady = false;
    bool perfOverlayConfigInit = false;
    [[maybe_unused]] bool perfOverlayEnabled = true;
    [[maybe_unused]] float perfOverlayScale = 1.0f;
    ui::RmlUiOverlay rmluiOverlay;
    bool rmluiEnabled = false;
    bool rmluiReady = false;
    int rmluiWidth = 0;
    int rmluiHeight = 0;
      // curveOverlay and curveOverlayLoaded are declared earlier near curve TSV loading
    bool curveOverlayEnabled = true;
    bool curveOverlayWindowOpen = true;
    bool firstLayout = true;
  } overlays;

  struct PostGroup {
    bool bloomSettingsLoaded = false;
    int bloomIterations = kMaxBloomIterations;
    bool postProcessingSettingsLoaded = false;
    float bloomStrength = 0.1f;
    float bloomThreshold = 0.4f;  // A2: was hardcoded 1.0 in shader (killed disk bloom)
    float bloomKnee = 0.15f;      // A3: soft knee half-width (was binary sign())
    float bloomTone = 1.0f;       // A6: scene weight in bloom composite (was never dispatched)
    bool tonemappingEnabled = true;
    float toneExposure = 1.0f;
    float gamma = 2.5f;
    float tonemapChromaticAberrationStrength = 0.002f;
    float tonemapVignetteStrength = 1.0f;
    float tonemapFilmGrainStrength = 0.005f;
  } post;

  struct DiskGroup {
    bool gravitationalLensing = true;
    bool renderBlackHole = true;
    bool adiskEnabled = true;
    bool adiskParticle = true;
    float adiskDensityV = 2.0f;
    float adiskDensityH = 4.0f;
    float adiskHeight = 0.55f;
    float adiskLit = 0.25f;
    float adiskNoiseLOD = 5.0f;
    float adiskNoiseScale = 0.8f;
    bool useNoiseTexture = true;
    float noiseTextureScale = 0.25f;
    [[maybe_unused]] int const noiseTextureSize = 32;
    float adiskSpeed = 0.5f;
    float dopplerStrength = 1.0f;
    float photonSphereGlowStrength = 1.0f;
    GLuint texNoiseVolume = 0;
    bool noiseTextureReady = false;
    blackhole::NoiseTextureCache noiseCache;
  } disk;

  struct RteGroup {
      // D2: volumetric RTE
    bool  rteVolumetricEnabled = false;
    float rteOpacityScale      = 0.5f;
  } rte;

  struct StokesGroup {
      // D4: polarized Stokes IQUV
    bool  stokesEnabled        = false;
    float stokesBFieldAngle    = 0.0f;   // EVPA of projected B field [rad]
    float stokesNeScale        = 0.0f;   // Faraday rotation strength (0 = off)
  } stokes;

  struct PhysicsCoreGroup {
    float blackHoleMass = 1.0f;
    float kerrSpin = 0.0f;
    bool enablePhotonSphere = false;
    bool enableRedshift = false;
  } physicsCore;

  struct HawkingGroup {
    bool hawkingGlowEnabled = false;
    float hawkingTempScale = 1.0f;
    float hawkingGlowIntensity = 1.0f;
    bool hawkingUseLUTs = true;
    int hawkingPreset = 0; // 0=Physical, 1=Primordial, 2=Extreme
    physics::HawkingRenderer hawkingRenderer;
    bool hawkingLutsLoaded = false;
  } hawking;

  struct GrmhdGroup {
    bool useGrmhd = false;
    bool grmhdLoaded = false;
    GrmhdPackedTexture grmhdTexture;
    std::string grmhdLoadError;
    std::array<char, 256> grmhdPathBuffer{};
    bool grmhdPathInit = false;
    glm::vec3 grmhdBoundsMin = glm::vec3(-10.0f, -2.0f, -10.0f);
    glm::vec3 grmhdBoundsMax = glm::vec3(10.0f, 2.0f, 10.0f);
    bool grmhdSliceEnabled = false;
    int grmhdSliceAxis = 2;
    int grmhdSliceChannel = 0;
    float grmhdSliceCoord = 0.5f;
    bool grmhdSliceUseColorMap = true;
    bool grmhdSliceAutoRange = true;
    float grmhdSliceMin = 0.0f;
    float grmhdSliceMax = 1.0f;
    int grmhdSliceSize = 256;
    int grmhdSliceSizeCached = 0;
      // GRMHD Time-Series Playback (Phase 4.3 - streaming infrastructure)
    bool grmhdTimeSeriesEnabled = false;
    std::array<char, 256> grmhdTimeSeriesJsonBuffer{};
    std::array<char, 256> grmhdTimeSeriesBinBuffer{};
    bool grmhdTimeSeriesLoaded = false;
    int grmhdCurrentFrame = 0;
    int grmhdMaxFrame = 0;
    bool grmhdPlaying = false;
    float grmhdPlaybackSpeed = 1.0f;
    double grmhdCacheHitRate = 0.0;
    int grmhdQueueDepth = 0;
    std::unique_ptr<blackhole::GRMHDStreamer> grmhdStreamer;
      /* PBO uploader for streaming time-series tiles.  Initialized once when the
       * streamer loads a dataset and shut down when the dataset is unloaded.
       * Its texture() replaces grmhdTexture.texture for the time-series path. */
    blackhole::GrmhdPBOUploader grmhdPboUploader;
      /* C1d: second PBO uploader for the adjacent (next) GRMHD frame.
       * Holds frame N+1; blended with grmhdPboUploader (frame N) using grmhdFrameAlpha. */
    blackhole::GrmhdPBOUploader grmhdPboUploaderRight;
      /* Sub-frame blend factor [0,1): fraction of current inter-frame interval elapsed. */
    float grmhdFrameAlpha = 0.0f;
    GLuint texGrmhdSlice = 0;
    GLuint registeredRightTex = 0;
  } grmhd;

  struct LutsGroup {
    bool lutAssetsTried = false;
    bool lutAssetsLoaded = false;
    bool lutFromAssets = false;
    bool lutAssetOnly = false;
    bool lutAssetOnlyWarned = false;
    bool lutAssetConfigInit = false;
    float lutAssetSpin = 0.0f;
    physics::Lut1D lutAssetEmissivity;
    physics::Lut1D lutAssetRedshift;
    bool spectralLutTried = false;
    bool spectralLutLoaded = false;
    bool synchGLutCreated = false;
    bool useSpectralLut = false;
    float spectralWavelengthMin = 0.0f;
    float spectralWavelengthMax = 0.0f;
    float spectralRadiusMin = 0.0f;
    float spectralRadiusMax = 0.0f;
    bool grbModulationTried = false;
    bool grbModulationLoaded = false;
    bool useGrbModulation = false;
    bool grbTimeManual = false;
    float grbTimeManualValue = 0.0f;
    float grbTimeMin = 0.0f;
    float grbTimeMax = 1.0f;
    std::vector<float> grbModulationValues;
    GLuint texGrbModulationLUT = 0;
    std::vector<float> spectralLutValues;
    bool lutInitialized = false;
    float lutSpin = 0.0f;
    float lutRadiusMin = 0.0f;
    float lutRadiusMax = 0.0f;
    float redshiftRadiusMin = 0.0f;
    float redshiftRadiusMax = 0.0f;
    GLuint texEmissivityLUT = 0;
    GLuint texRedshiftLUT = 0;
    GLuint texPhotonGlowLUT = 0;  // Phase 8.2: Photon sphere glow effect LUT
    GLuint texDiskDensityLUT = 0; // Phase 8.2: Accretion disk density profile LUT
    GLuint texSpectralLUT = 0;
    GLuint texSynchGLut = 0;   /**< @brief Synchrotron G(x) LUT (GL_TEXTURE_2D, height=1). */
    float lutAdiskDensityV = 0.0f;
  } luts;

  struct TargetsGroup {
    GLuint texBlackhole = 0;
    GLuint texBlackholeCompare = 0;
    GLuint texBrightness = 0;
    GLuint texBloomFinal = 0;
    GLuint texTonemapped = 0;
    GLuint texDepthEffects = 0;
    std::array<GLuint, kMaxBloomIterations> texDownsampled = {};
    std::array<GLuint, kMaxBloomIterations> texUpsampled = {};
    int renderWidth = 0;
    int renderHeight = 0;
    GLuint sceneFbo = 0;
  } targets;

  struct RecordingGroup {
      // --record-frames: cinematic recording state
    bool         recordInitDone    = false;
    int          recordFrameIndex  = 0; // assigned from recordStartFrame after construction
    int          recordWarmup      = 0;
    float        recordCinematic   = 0.0f; // assigned from recordStartFrame after construction
    CinematicPath recordPath;
    CamKeyframe  recordCurrentKf   = K_CINEMATIC_KEYFRAMES[0];
    float        recordCurRs       = 2.0f;
    float        recordCurIsco     = 1.0f;
  } recording;

  struct DispatchGroup {
    bool useComputeRaytracer = false;
#if BLACKHOLE_HAS_CUDA
    CudaRenderManager cudaManager;
    bool cudaVariantEnvApplied = false;
#endif
    int computeMaxSteps = 300;
    float computeStepSize = 0.1f;
    bool computeTiled = false;
    int computeTileSize = 256;
  } dispatch;

  struct CompareGroup {
    bool compareComputeFragment = false;
    int compareSampleSize = 16;
    int compareFrameStride = 1;
    DiffStats compareStats;
    DiffStats compareFullStats;
    bool compareWriteOutputs = false;
    bool compareWriteDiff = true;
    bool compareWriteSummary = true;
    float compareDiffScale = 8.0f;
    float compareThreshold = 0.02f;
    int compareMaxOutliers = 10000;       // Enable outlier gating by default
    float compareMaxOutlierFrac = 0.006f; // 0.6% tolerance for Kerr divergence
    bool compareOverridesEnabled = false;
    int compareMaxStepsOverride = 0;
    float compareStepSizeOverride = 0.0f;
    bool compareBaselineEnabled = false;
    int integratorDebugFlags = 0;
    bool integratorDebugConfigInit = false;
    int compareFailureCount = 0;
    bool compareLastExceeded = false;
    int compareLastOutliers = 0;
    int compareLastOutlierLimit = 0;
    int compareSnapshotIndex = 0;
    bool compareAutoCapture = false;
    int compareAutoCount = static_cast<int>(K_COMPARE_PRESETS.size());
    int compareAutoStride = 30;
    int compareAutoRemaining = 0;
    int compareAutoStrideCounter = 0;
    bool comparePresetSweep = false;
    bool comparePresetSaved = false;
    bool compareRestorePending = false;
    int comparePresetIndex = 0;
    int comparePresetFrameCounter = 0;
    int comparePresetSettleFrames = 2;
    CameraState comparePresetSavedCamera{};
    int comparePresetSavedMode = 0;
    float comparePresetSavedOrbitRadius = 0.0f;
    float comparePresetSavedOrbitSpeed = 0.0f;
    float comparePresetSavedOrbitTime = 0.0f;
    float comparePresetSavedKerrSpin = 0.0f;
    bool captureCompareSnapshot = false;
    int compareFrameCounter = 0;
    bool compareAutoInit = false;
    bool forceInteropFragmentEnvApplied = false;
  } compare;

  struct ProbesGroup {
    bool drawIdProbeEnabled = false;
    bool drawIdProbeConfigInit = false;
    bool drawIdProbeSupported = false;
    bool multiDrawMainEnabled = false;
    bool multiDrawMainConfigInit = false;
    bool multiDrawIndirectCount = false;
    bool multiDrawSupported = false;
    bool multiDrawCountSupported = false;
    [[maybe_unused]] bool multiDrawOverlayEnabled = true;
    [[maybe_unused]] int const multiDrawInstanceCount = 2;
    [[maybe_unused]] GLuint const multiDrawProgram = 0;
    [[maybe_unused]] GLuint const multiDrawInstanceBuffer = 0;
    [[maybe_unused]] GLuint const multiDrawCommandBuffer = 0;
    [[maybe_unused]] GLuint const multiDrawCountBuffer = 0;
    [[maybe_unused]] GLuint const multiDrawComputeProgram = 0;
    [[maybe_unused]] bool depthPrepassEnabled =
        false; // For future mesh-based disk rendering
  } probes;

  struct TimingGroup {
    bool gpuTimingEnabled = false;
    bool gpuTimingLogInit = false;
    bool gpuTimingLogEnabled = false;
    int gpuTimingLogStride = 60;
    int gpuTimingLogCounter = 0;
    int gpuTimingLogIndex = 0;
    GpuTimerSet gpuTimers;
    TimingHistory timingHistory;
  } timing;

  struct BackgroundGroup {
    GLuint galaxy = 0;
    GLuint colorMap = 0;
    bool baseTexturesLoaded = false;
    std::vector<BackgroundAsset> backgroundAssets;
    int backgroundIndex = 0;
    std::string backgroundLoadedId;
    std::string skyboxLoadedDir;
    GLuint backgroundBase = 0;
    std::array<GLuint, K_BACKGROUND_LAYERS> backgroundTextures = {};
    std::array<glm::vec4, K_BACKGROUND_LAYERS> backgroundLayerParams = {};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerDepth = {0.2f, 0.5f, 0.9f};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerScale = {1.0f, 1.08f, 1.16f};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerIntensity = {1.0f, 0.6f, 0.35f};
    std::array<float, K_BACKGROUND_LAYERS> backgroundLayerLodBias = {0.0f, 1.0f, 2.0f};
    glm::vec2 backgroundLayerGlobalOffset = glm::vec2(0.0f);
    float backgroundYawRad = 0.0f;
    float backgroundPitchRad = 0.0f;
    GLuint fallback2D = 0;
    GLuint fallback3D = 0;
    GLuint fallbackCubemap = 0;
  } background;

  struct WiregridGroup {
    bool wiregridEnabled = false;
    WiregridParams wiregridParams;
    glm::vec4 wiregridColor = glm::vec4(0.21f, 0.62f, 0.92f, 0.16f);
    bool wiregridEnvApplied = false;
  } wiregrid;

  struct DebugGroup {
    bool debugPreRedshiftBackground = false;
    bool debugPreShapingBackground = false;
    bool debugPostShapingBackground = false;
    bool debugShaperInputs = false;
    bool debugClosestApproachState = false;
    bool debugClosestApproachTimeline = false;
    bool debugClosestApproachDirection = false;
    bool debugEscapedDirection = false;
    bool debugPreShapingBackgroundEnvApplied = false;
  } debug;

  struct ExportingGroup {
    int exportWarmup = 0;
    bool exportPerformed = false;
    int exportDone = 0;
  } exporting;

  struct DepthFxGroup {
    bool depthEffectsEnabled = true;
    bool fogEnabled = true;
    float fogDensity = 0.08f;
    float fogStart = 0.6f;
    float fogEnd = 0.98f;
    float fogColor[3] = {0.06f, 0.06f, 0.10f};
    bool edgeOutlinesEnabled = false;
    float edgeThreshold = 0.5f;
    float edgeWidth = 1.0f;
    float edgeColor[3] = {1.0f, 1.0f, 1.0f};
    bool depthDesatEnabled = true;
    float desatStrength = 0.10f;
    bool chromaDepthEnabled = false;
    bool motionParallaxHint = false;
    bool dofEnabled = false;
    float dofFocusNear = 0.3f;
    float dofFocusFar = 0.9f;
    float dofMaxRadius = 2.0f;
    float depthCurve = 1.0f;
  } depthFx;

};



void renderPerformancePanel(bool &gpuTimingEnabled, const GpuTimerSet &timers,
                            const TimingHistory &history, float cpuFrameMs,
                            bool &perfOverlayEnabled, float &perfOverlayScale,
                            bool &depthPrepassEnabled) {
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

} // anonymous namespace

// NOLINTNEXTLINE(readability-function-cognitive-complexity,readability-function-size) --
// application main loop
int main(int argc, char **argv) {
  platform::installCrashHandlers();
  try {
    std::string curveTsvPath;
    std::string exportFramePath;
    std::string exportRawFramePath;
    std::string recordFramesDir;
    std::string recordProfile = "cinematic";
    std::string recordComposition = "wide-right";
    std::string recordBackgroundId;
    int         recordFramesTotal = K_CINEMATIC_FRAMES;
    int         recordStartFrame  = 0;
    float       recordYawDeg = 0.0f;
    bool        hasRecordYaw = false;
    float       recordPitchDeg = 0.0f;
    bool        hasRecordPitch = false;
    float       recordDistance = 0.0f;
    bool        hasRecordDistance = false;
    float       recordFovDeg = 0.0f;
    bool        hasRecordFov = false;
    float       recordExposure = 0.0f;
    bool        hasRecordExposure = false;
    float       recordSweepDeg = 0.0f;
    bool        hasRecordSweep = false;
    float       recordFrameX = 0.0f;
    bool        hasRecordFrameX = false;
    float       recordFrameY = 0.0f;
    bool        hasRecordFrameY = false;
    bool        hasRecordBackgroundId = false;
    float       recordBackgroundYawDeg = 0.0f;
    bool        hasRecordBackgroundYaw = false;
    float       recordBackgroundPitchDeg = 0.0f;
    bool        hasRecordBackgroundPitch = false;
    for (int i = 1; i < argc; ++i) {
      std::string const arg = argv[i];
      if (arg == "--help" || arg == "-h") {
        printUsage(argv[0]);
        return 0;
      }
      if (arg == "--curve-tsv" && i + 1 < argc) {
        curveTsvPath = argv[++i];
        continue;
      }
      if (arg == "--export-frame" && i + 1 < argc) {
        exportFramePath = argv[++i];
        continue;
      }
      if (arg == "--export-raw-frame" && i + 1 < argc) {
        exportRawFramePath = argv[++i];
        continue;
      }
      if (arg == "--record-frames" && i + 1 < argc) {
        recordFramesDir = argv[++i];
        if (i + 1 < argc && argv[i + 1][0] != '-') {
          recordFramesTotal = std::atoi(argv[++i]);
        }
        continue;
      }
      if (arg == "--start-frame" && i + 1 < argc) {
        recordStartFrame = std::atoi(argv[++i]);
        continue;
      }
      if (arg == "--record-profile" && i + 1 < argc) {
        recordProfile = argv[++i];
        continue;
      }
      if (arg == "--record-composition" && i + 1 < argc) {
        recordComposition = argv[++i];
        continue;
      }
      if (arg == "--record-yaw" && i + 1 < argc) {
        recordYawDeg = std::strtof(argv[++i], nullptr);
        hasRecordYaw = true;
        continue;
      }
      if (arg == "--record-pitch" && i + 1 < argc) {
        recordPitchDeg = std::strtof(argv[++i], nullptr);
        hasRecordPitch = true;
        continue;
      }
      if (arg == "--record-distance" && i + 1 < argc) {
        recordDistance = std::strtof(argv[++i], nullptr);
        hasRecordDistance = true;
        continue;
      }
      if (arg == "--record-fov" && i + 1 < argc) {
        recordFovDeg = std::strtof(argv[++i], nullptr);
        hasRecordFov = true;
        continue;
      }
      if (arg == "--record-exposure" && i + 1 < argc) {
        recordExposure = std::strtof(argv[++i], nullptr);
        hasRecordExposure = true;
        continue;
      }
      if (arg == "--record-sweep-deg" && i + 1 < argc) {
        recordSweepDeg = std::strtof(argv[++i], nullptr);
        hasRecordSweep = true;
        continue;
      }
      if (arg == "--record-frame-x" && i + 1 < argc) {
        recordFrameX = std::strtof(argv[++i], nullptr);
        hasRecordFrameX = true;
        continue;
      }
      if (arg == "--record-frame-y" && i + 1 < argc) {
        recordFrameY = std::strtof(argv[++i], nullptr);
        hasRecordFrameY = true;
        continue;
      }
      if (arg == "--record-background-id" && i + 1 < argc) {
        recordBackgroundId = argv[++i];
        hasRecordBackgroundId = true;
        continue;
      }
      if (arg == "--record-bg-yaw" && i + 1 < argc) {
        recordBackgroundYawDeg = std::strtof(argv[++i], nullptr);
        hasRecordBackgroundYaw = true;
        continue;
      }
      if (arg == "--record-bg-pitch" && i + 1 < argc) {
        recordBackgroundPitchDeg = std::strtof(argv[++i], nullptr);
        hasRecordBackgroundPitch = true;
        continue;
      }
      std::printf("Unknown argument: %s\n", arg.c_str());
      printUsage(argv[0]);
      return 2;
    }

    if (recordProfile != "cinematic" && recordProfile != "compare-orbit-near" &&
        recordProfile != "showcase-orbit") {
      std::printf("Unknown record profile: %s\n", recordProfile.c_str());
      printUsage(argv[0]);
      return 2;
    }
    if (recordProfile == "showcase-orbit" &&
        findShowcaseOrbitComposition(recordComposition) == nullptr) {
      std::printf("Unknown showcase composition: %s\n", recordComposition.c_str());
      printUsage(argv[0]);
      return 2;
    }

    platform::initResourceRoot(argv[0]);
    setShaderBaseDir(platform::resourceRoot().string() + "/");

    // Load settings first
    SettingsManager::instance().load();
    auto &settings = SettingsManager::instance().get();

    // Initialize window and OpenGL context
    GLFWwindow *window = initializeWindow(settings.windowWidth, settings.windowHeight);
    if (window == nullptr) {
      return 1;
    }

    glfwSwapInterval(settings.swapInterval);

    // Initialize shader manager (must be after OpenGL context)
    ShaderManager::instance().init();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
    // Initialize shader hot-reload watcher
    ShaderWatcher::instance().start((std::filesystem::path(getShaderBaseDir()) / "shader").string());
#endif

    // Initialize input manager and sync with settings
    InputManager::instance().init(window);
    InputManager::instance().syncFromSettings();
    if (settings.fullscreen) {
      InputManager::instance().toggleFullscreen();
    }

    // Initialize ImGui
    initializeImGui(window);

    // Curve overlay for plotting (e.g., critical curves)
    RenderState rs;
    rs.recording.recordFrameIndex = recordStartFrame;
    rs.recording.recordCinematic =
        static_cast<float>(recordStartFrame) / static_cast<float>(K_CINEMATIC_FPS);

    if (!curveTsvPath.empty()) {
      rs.overlays.curveOverlayLoaded = rs.overlays.curveOverlay.loadFromTsv(curveTsvPath);
      if (!rs.overlays.curveOverlayLoaded) {
        std::fprintf(stderr, "curve overlay load failed: %s\n", // NOLINT(cert-err33-c) --
                                                                // diagnostic output, return unused
                     rs.overlays.curveOverlay.lastError.c_str());
      }
    }

    // Create fullscreen quad for rendering
    GLuint const quadVAO = createQuadVAO();
    glBindVertexArray(quadVAO);

    // Main loop
    PostProcessPass const passthrough("shader/passthrough.frag");

    double lastTime = glfwGetTime();


    auto loadGrmhdPacked = [&](const std::string &path) {
      std::string error;
      if (!loadGrmhdPackedTexture(path, rs.grmhd.grmhdTexture, error, true, true)) {
        rs.grmhd.grmhdLoadError = error;
        rs.grmhd.grmhdLoaded = false;
        return false;
      }
      rs.grmhd.grmhdLoadError.clear();
      rs.grmhd.grmhdLoaded = true;
      /* Wire BL radial extent from grid header into the Cartesian bounds uniforms.
       * The grid is spherical so the conservative bounding box is [-rMax, rMax]^3. */
      const float r = rs.grmhd.grmhdTexture.rMax;
      rs.grmhd.grmhdBoundsMin = glm::vec3(-r, -r, -r);
      rs.grmhd.grmhdBoundsMax = glm::vec3( r,  r,  r);
      /* Register GRMHD volume as CUDA texture object (slot 5 = BhLutGrmhd).
       * Registration is non-fatal: CUDA kernel falls back to no GRMHD sampling
       * if the backend is not active or registration fails. */
#if BLACKHOLE_HAS_CUDA
      if (rs.grmhd.grmhdTexture.texture != 0) {
        rs.dispatch.cudaManager.registerLut(5 /*BhLutGrmhd*/, rs.grmhd.grmhdTexture.texture,
                                static_cast<unsigned int>(GL_TEXTURE_3D));
      }
#endif
      return true;
    };

    if (!rs.grmhd.grmhdPathInit) {
      std::snprintf(
          rs.grmhd.grmhdPathBuffer.data(),
          rs.grmhd.grmhdPathBuffer.size(), // NOLINT(cert-err33-c) -- diagnostic output, return unused
          "%s", resourcePath("assets/grmhd/grmhd_pack.json").c_str());
      rs.grmhd.grmhdPathInit = true;
    }

    if (!rs.compare.compareAutoInit) {
      const char *sweepEnv = std::getenv("BLACKHOLE_COMPARE_SWEEP");
      if (sweepEnv != nullptr && std::string(sweepEnv) == "1") {
        rs.dispatch.useComputeRaytracer = true;
        rs.compare.compareComputeFragment = true;
        rs.compare.comparePresetSweep = true;
        rs.compare.compareWriteSummary = true;
        rs.compare.compareWriteOutputs = false;
        rs.compare.compareWriteDiff = false;
        rs.compare.compareAutoCapture = true;
        rs.compare.compareAutoCount = static_cast<int>(K_COMPARE_PRESETS.size());
        rs.compare.compareAutoRemaining = rs.compare.compareAutoCount;
        rs.compare.compareAutoStrideCounter = 0;
        rs.compare.compareAutoStride = rs.compare.comparePresetSettleFrames;
        rs.compare.compareRestorePending = false;
        const char *writeDiffEnv = std::getenv("BLACKHOLE_COMPARE_WRITE_DIFF");
        if (writeDiffEnv != nullptr && std::string(writeDiffEnv) == "1") {
          rs.compare.compareWriteDiff = true;
        }
        const char *writeOutputsEnv = std::getenv("BLACKHOLE_COMPARE_WRITE_OUTPUTS");
        if (writeOutputsEnv != nullptr && std::string(writeOutputsEnv) == "1") {
          rs.compare.compareWriteOutputs = true;
        }
        const char *writeSummaryEnv = std::getenv("BLACKHOLE_COMPARE_WRITE_SUMMARY");
        if (writeSummaryEnv != nullptr && std::string(writeSummaryEnv) == "0") {
          rs.compare.compareWriteSummary = false;
        }
        const char *outlierCountEnv = std::getenv("BLACKHOLE_COMPARE_OUTLIER_COUNT");
        if (outlierCountEnv != nullptr) {
          rs.compare.compareMaxOutliers =
              std::max(0, std::atoi(outlierCountEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                       // -- env var, invalid input defaults to 0
        }
        const char *outlierFracEnv = std::getenv("BLACKHOLE_COMPARE_OUTLIER_FRAC");
        if (outlierFracEnv != nullptr) {
          rs.compare.compareMaxOutlierFrac =
              std::max(0.0f, static_cast<float>(std::atof(
                                 outlierFracEnv))); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                    // -- env var, invalid input defaults to 0
        }
        const char *maxStepsEnv = std::getenv("BLACKHOLE_COMPARE_MAX_STEPS");
        if (maxStepsEnv != nullptr) {
          rs.compare.compareMaxStepsOverride =
              std::max(0, std::atoi(maxStepsEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                   // -- env var, invalid input defaults to 0
          if (rs.compare.compareMaxStepsOverride > 0) {
            rs.compare.compareOverridesEnabled = true;
          }
        }
        const char *stepSizeEnv = std::getenv("BLACKHOLE_COMPARE_STEP_SIZE");
        if (stepSizeEnv != nullptr) {
          rs.compare.compareStepSizeOverride =
              static_cast<float>(std::atof(stepSizeEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                          // -- env var, invalid input defaults to 0
          if (rs.compare.compareStepSizeOverride > 0.0f) {
            rs.compare.compareOverridesEnabled = true;
          }
        }
        const char *baselineEnv = std::getenv("BLACKHOLE_COMPARE_BASELINE");
        if (baselineEnv != nullptr && std::string(baselineEnv) == "1") {
          rs.compare.compareBaselineEnabled = true;
        }
      }
      rs.compare.compareAutoInit = true;
    }
    if (!rs.compare.forceInteropFragmentEnvApplied) {
      const char *interopEnv = std::getenv("BLACKHOLE_FORCE_INTEROP_FRAGMENT");
      if (interopEnv != nullptr && std::string(interopEnv) == "1") {
        rs.compare.compareComputeFragment = true;
        rs.dispatch.useComputeRaytracer = false;
#if BLACKHOLE_HAS_CUDA
        if (!kAppVariantCudaOnly) {
          rs.dispatch.cudaManager.setEnabled(false);
        }
#endif
      }
      rs.compare.forceInteropFragmentEnvApplied = true;
    }

#if BLACKHOLE_HAS_CUDA
    if (!rs.dispatch.cudaVariantEnvApplied) {
      if (const char *variantEnv = std::getenv("BLACKHOLE_CUDA_KERNEL_VARIANT")) {
        int requestedVariant = std::atoi(variantEnv);
        if (requestedVariant < -1 || requestedVariant >= BH_KERNEL_COUNT) {
          std::fprintf(stderr,
                       "Ignoring BLACKHOLE_CUDA_KERNEL_VARIANT=%s (expected -1..%d)\n",
                       variantEnv, BH_KERNEL_COUNT - 1);
        } else {
          rs.dispatch.cudaManager.setKernelVariant(requestedVariant);
          std::printf("CUDA kernel variant override: %d\n", requestedVariant);
        }
      }
      rs.dispatch.cudaVariantEnvApplied = true;
    }
#endif

    if (!rs.timing.gpuTimingLogInit) {
      const char *logEnv = std::getenv("BLACKHOLE_GPU_TIMING_LOG");
      if (logEnv != nullptr && std::string(logEnv) == "1") {
        rs.timing.gpuTimingLogEnabled = true;
        rs.timing.gpuTimingEnabled = true;
        const char *strideEnv = std::getenv("BLACKHOLE_GPU_TIMING_LOG_STRIDE");
        if (strideEnv != nullptr) {
          int const stride = std::atoi(strideEnv); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                   // -- env var, invalid input defaults to 0
          rs.timing.gpuTimingLogStride = std::max(1, stride);
        }
      }
      rs.timing.gpuTimingLogInit = true;
    }

    if (!rs.probes.drawIdProbeConfigInit) {
      const char *probeEnv = std::getenv("BLACKHOLE_DRAWID_PROBE");
      if (probeEnv != nullptr && std::string(probeEnv) == "1") {
        rs.probes.drawIdProbeEnabled = true;
      }
      rs.probes.drawIdProbeSupported = supportsDrawId() && supportsMultiDrawIndirect();
      if (rs.probes.drawIdProbeEnabled && !rs.probes.drawIdProbeSupported) {
        std::cout << "DrawID probe requested but not supported by the driver.\n";
        rs.probes.drawIdProbeEnabled = false;
      }
      rs.probes.drawIdProbeConfigInit = true;
    }

    if (!rs.probes.multiDrawMainConfigInit) {
      const char *multiDrawEnv = std::getenv("BLACKHOLE_MULTIDRAW_MAIN");
      if (multiDrawEnv != nullptr && std::string(multiDrawEnv) == "1") {
        rs.probes.multiDrawMainEnabled = true;
      }
      const char *overlayEnv = std::getenv("BLACKHOLE_MULTIDRAW_OVERLAY");
      if (overlayEnv != nullptr && std::string(overlayEnv) == "0") {
        rs.probes.multiDrawOverlayEnabled = false;
      }
      const char *countEnv = std::getenv("BLACKHOLE_MULTIDRAW_INDIRECT_COUNT");
      if (countEnv != nullptr && std::string(countEnv) == "1") {
        rs.probes.multiDrawIndirectCount = true;
      }
      rs.probes.multiDrawSupported = supportsDrawId() && supportsMultiDrawIndirect();
      rs.probes.multiDrawCountSupported = supportsIndirectCount();
      if (rs.probes.multiDrawMainEnabled && !rs.probes.multiDrawSupported) {
        std::cout << "Multi-draw main path requested but not supported.\n";
        rs.probes.multiDrawMainEnabled = false;
      }
      if (rs.probes.multiDrawIndirectCount && !rs.probes.multiDrawCountSupported) {
        std::cout << "Indirect count requested but not supported.\n";
        rs.probes.multiDrawIndirectCount = false;
      }
      rs.probes.multiDrawMainConfigInit = true;
    }

    if (!rs.luts.lutAssetConfigInit) {
      const char *assetOnlyEnv = std::getenv("BLACKHOLE_LUT_ASSET_ONLY");
      if (assetOnlyEnv != nullptr && std::string(assetOnlyEnv) == "1") {
        rs.luts.lutAssetOnly = true;
      }
      rs.luts.lutAssetConfigInit = true;
    }

    if (!rs.overlays.controlsOverlayConfigInit) {
      const char *overlayEnv = std::getenv("BLACKHOLE_OPENGL_CONTROLS");
      if (overlayEnv != nullptr && std::string(overlayEnv) == "0") {
        rs.overlays.controlsOverlayEnabled = false;
      }
      const char *scaleEnv = std::getenv("BLACKHOLE_OPENGL_CONTROLS_SCALE");
      if (scaleEnv != nullptr) {
        auto const scale =
            static_cast<float>(std::atof(scaleEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                     // -- env var, invalid input defaults to 0
        rs.overlays.controlsOverlayScale = std::max(scale, 0.5f);
      }
      rs.overlays.controlsOverlayConfigInit = true;
    }

    if (!rs.overlays.perfOverlayConfigInit) {
      const char *overlayEnv = std::getenv("BLACKHOLE_PERF_HUD");
      if (overlayEnv != nullptr && std::string(overlayEnv) == "0") {
        rs.overlays.perfOverlayEnabled = false;
      }
      const char *scaleEnv = std::getenv("BLACKHOLE_PERF_HUD_SCALE");
      if (scaleEnv != nullptr) {
        auto const scale =
            static_cast<float>(std::atof(scaleEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                                     // -- env var, invalid input defaults to 0
        rs.overlays.perfOverlayScale = std::max(scale, 0.5f);
      }
      rs.overlays.perfOverlayConfigInit = true;
    }

    if (!rs.compare.integratorDebugConfigInit) {
      const char *debugEnv = std::getenv("BLACKHOLE_INTEGRATOR_DEBUG_FLAGS");
      if (debugEnv != nullptr) {
        rs.compare.integratorDebugFlags =
            std::max(0, std::atoi(debugEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
                                              // -- env var, invalid input defaults to 0
      }
      rs.compare.integratorDebugConfigInit = true;
    }

    auto recreateRenderTargets = [&](int newWidth, int newHeight) {
      auto deleteTexture = [](GLuint &texture) {
        if (texture != 0) {
          glDeleteTextures(1, &texture);
          texture = 0;
        }
      };

      clearRenderToTextureCache();
      deleteTexture(rs.targets.texBlackhole);
      deleteTexture(rs.targets.texBlackholeCompare);
      deleteTexture(rs.targets.texBrightness);
      deleteTexture(rs.targets.texBloomFinal);
      deleteTexture(rs.targets.texTonemapped);
      deleteTexture(rs.targets.texDepthEffects);
      for (auto &texture : rs.targets.texDownsampled) {
        deleteTexture(texture);
      }
      for (auto &texture : rs.targets.texUpsampled) {
        deleteTexture(texture);
      }

      rs.targets.texBlackhole = createColorTexture32f(newWidth, newHeight);
      rs.targets.texBlackholeCompare = createColorTexture32f(newWidth, newHeight);
      rs.targets.texBrightness = createColorTexture(newWidth, newHeight);
      rs.targets.texBloomFinal = createColorTexture(newWidth, newHeight);
      rs.targets.texTonemapped = createColorTexture(newWidth, newHeight);
      rs.targets.texDepthEffects = createColorTexture(newWidth, newHeight);

      for (int i = 0; i < kMaxBloomIterations; ++i) {
        auto const index = static_cast<std::size_t>(i);
        int const downWidth = std::max(1, newWidth >> (i + 1));
        int const downHeight = std::max(1, newHeight >> (i + 1));
        int const upWidth = std::max(1, newWidth >> i);
        int const upHeight = std::max(1, newHeight >> i);
        rs.targets.texDownsampled.at(index) = createColorTexture(downWidth, downHeight);
        rs.targets.texUpsampled.at(index) = createColorTexture(upWidth, upHeight);
      }

      rs.targets.renderWidth = newWidth;
      rs.targets.renderHeight = newHeight;

#if BLACKHOLE_HAS_CUDA
      rs.dispatch.cudaManager.resize(rs.targets.texBlackhole, newWidth, newHeight);
#endif
    };


    auto updateLuts = [&](float spin, float densityV) {
      spin = std::clamp(spin, -0.99f, 0.99f);
      if (!rs.luts.lutAssetsTried) {
        rs.luts.lutAssetsTried = true;
        rs.luts.lutAssetsLoaded = loadLutAssets(rs.luts.lutAssetEmissivity, rs.luts.lutAssetRedshift, rs.luts.lutAssetSpin);
      }

      bool const useAssetLuts = rs.luts.lutAssetsLoaded && std::abs(spin - rs.luts.lutAssetSpin) <= 1e-3f &&
                                !rs.luts.lutAssetEmissivity.values.empty() &&
                                !rs.luts.lutAssetRedshift.values.empty();
      if (useAssetLuts) {
        if (!rs.luts.lutInitialized || !rs.luts.lutFromAssets) {
          if (rs.luts.texEmissivityLUT != 0) {
            glDeleteTextures(1, &rs.luts.texEmissivityLUT);
            rs.luts.texEmissivityLUT = 0;
          }
          if (rs.luts.texRedshiftLUT != 0) {
            glDeleteTextures(1, &rs.luts.texRedshiftLUT);
            rs.luts.texRedshiftLUT = 0;
          }
          if (rs.luts.texPhotonGlowLUT != 0) {
            glDeleteTextures(1, &rs.luts.texPhotonGlowLUT);
            rs.luts.texPhotonGlowLUT = 0;
          }
          if (rs.luts.texDiskDensityLUT != 0) {
            glDeleteTextures(1, &rs.luts.texDiskDensityLUT);
            rs.luts.texDiskDensityLUT = 0;
          }

          int const lutSize = static_cast<int>(rs.luts.lutAssetEmissivity.values.size());
          rs.luts.texEmissivityLUT = createFloatTexture2D(lutSize, 1, rs.luts.lutAssetEmissivity.values);
          rs.luts.texRedshiftLUT = createFloatTexture2D(lutSize, 1, rs.luts.lutAssetRedshift.values);

#if BLACKHOLE_HAS_CUDA
          /* Share asset LUTs with CUDA backend (slot 0=emissivity, 1=redshift) */
          rs.dispatch.cudaManager.registerLut(0, rs.luts.texEmissivityLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
          rs.dispatch.cudaManager.registerLut(1, rs.luts.texRedshiftLUT,   static_cast<unsigned int>(GL_TEXTURE_2D));
#endif

          rs.luts.lutRadiusMin = rs.luts.lutAssetEmissivity.rMin;
          rs.luts.lutRadiusMax = rs.luts.lutAssetEmissivity.rMax;
          rs.luts.redshiftRadiusMin = rs.luts.lutAssetRedshift.rMin;
          rs.luts.redshiftRadiusMax = rs.luts.lutAssetRedshift.rMax;
          rs.luts.lutSpin = rs.luts.lutAssetSpin;
          rs.luts.lutFromAssets = true;
          rs.luts.lutInitialized = true;
        }
        return;
      }

      if (rs.luts.lutAssetOnly) {
        if (!rs.luts.lutAssetOnlyWarned) {
          std::cout << "LUT asset-only mode active; skipping generated LUT fallback.\n";
          rs.luts.lutAssetOnlyWarned = true;
        }
        if (rs.luts.texEmissivityLUT != 0) {
          glDeleteTextures(1, &rs.luts.texEmissivityLUT);
          rs.luts.texEmissivityLUT = 0;
        }
        if (rs.luts.texRedshiftLUT != 0) {
          glDeleteTextures(1, &rs.luts.texRedshiftLUT);
          rs.luts.texRedshiftLUT = 0;
        }
        if (rs.luts.texPhotonGlowLUT != 0) {
          glDeleteTextures(1, &rs.luts.texPhotonGlowLUT);
          rs.luts.texPhotonGlowLUT = 0;
        }
        rs.luts.lutInitialized = false;
        rs.luts.lutFromAssets = false;
        return;
      }

      // Only regenerate if parameters changed or not initialized
      if (!rs.luts.lutInitialized || std::abs(spin - rs.luts.lutSpin) > 1e-3f ||
          std::abs(densityV - rs.luts.lutAdiskDensityV) > 1e-3f || rs.luts.lutFromAssets) {
        // Cleanup existing textures
        if (rs.luts.texEmissivityLUT != 0) {
          glDeleteTextures(1, &rs.luts.texEmissivityLUT);
          rs.luts.texEmissivityLUT = 0;
        }
        if (rs.luts.texRedshiftLUT != 0) {
          glDeleteTextures(1, &rs.luts.texRedshiftLUT);
          rs.luts.texRedshiftLUT = 0;
        }
        if (rs.luts.texPhotonGlowLUT != 0) {
          glDeleteTextures(1, &rs.luts.texPhotonGlowLUT);
          rs.luts.texPhotonGlowLUT = 0;
        }
        if (rs.luts.texDiskDensityLUT != 0) {
          glDeleteTextures(1, &rs.luts.texDiskDensityLUT);
          rs.luts.texDiskDensityLUT = 0;
        }

        constexpr int kLutSize = 256;
        constexpr double kMassSolar = 4.0e6;
        constexpr double kMdotEdd = 0.1;

        auto emissivityLut = physics::generateEmissivityLut(
            kLutSize, kMassSolar, static_cast<double>(spin), kMdotEdd, true);
        auto redshiftLut =
            physics::generateRedshiftLut(kLutSize, kMassSolar, static_cast<double>(spin));

        rs.luts.texEmissivityLUT = createFloatTexture2D(kLutSize, 1, emissivityLut.values);
        rs.luts.texRedshiftLUT = createFloatTexture2D(kLutSize, 1, redshiftLut.values);

#if BLACKHOLE_HAS_CUDA
        /* Share generated LUTs with CUDA backend (slot 0=emissivity, 1=redshift) */
        rs.dispatch.cudaManager.registerLut(0, rs.luts.texEmissivityLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
        rs.dispatch.cudaManager.registerLut(1, rs.luts.texRedshiftLUT,   static_cast<unsigned int>(GL_TEXTURE_2D));
#endif

        auto photonGlowLut = physics::generatePhotonGlowLut(256);
        rs.luts.texPhotonGlowLUT = createFloatTexture2D(256, 1, photonGlowLut.values);

        // Connect adiskDensityV to LUT generation
        // Use densityV as the exponent or scale factor for the density profile
        double const densityScale = static_cast<double>(std::max(0.1f, densityV));
        auto diskDensityLut = physics::generateDiskDensityLut(256, densityScale);
        rs.luts.texDiskDensityLUT = createFloatTexture2D(256, 1, diskDensityLut.values);

        rs.luts.lutRadiusMin = emissivityLut.rMin;
        rs.luts.lutRadiusMax = emissivityLut.rMax;
        rs.luts.redshiftRadiusMin = redshiftLut.rMin;
        rs.luts.redshiftRadiusMax = redshiftLut.rMax;
        rs.luts.lutSpin = spin;
        rs.luts.lutAdiskDensityV = densityV;
        rs.luts.lutFromAssets = false;
        rs.luts.lutInitialized = true;
        std::cout << "LUTs regenerated. Spin: " << spin << ", DensityV: " << densityV << '\n';
      }
    };

    // ... (rest of main) ...

    /* WHY: computeProgram is hoisted here (rather than a static local inside the
     * frame loop) so the hot-reload handler at the top of each frame can delete
     * and reset it to 0, triggering lazy re-creation on the next iteration. */
    GLuint computeProgram = 0;

    while (glfwWindowShouldClose(window) == 0) {
      // Clear default framebuffer (essential for ImGui Docking over Viewport)
      glClearColor(0.0f, 0.0f, 0.0f, 1.0f);
      glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

      // std::cout << "Frame start" << std::endl; // Debug instrumentation
      ZONE_SCOPED_N("Frame");
      // ...
      // Calculate delta time
      double const currentTime = glfwGetTime();
      auto const frameTime = static_cast<float>(currentTime);
      auto const deltaTime = static_cast<float>(currentTime - lastTime);
      lastTime = currentTime;
      const float cpuFrameMs = deltaTime * 1000.0f;

      glfwPollEvents();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
      // Check for shader file changes and recompile all affected programs.
      if (ShaderWatcher::instance().hasPendingReloads()) {
        auto changedShaders = ShaderWatcher::instance().pollChangedShaders();
        for (const auto &path : changedShaders) {
          std::cout << "[HotReload] Shader changed: " << path << "\n";
        }
        ShaderWatcher::instance().clearPendingReloads();

        /* WHY: reloadAllRenderShaders() recompiles every render-to-texture
         * program cached in render.cpp's shaderProgramMap.  This covers
         * blackhole_main.frag, all bloom stages, tonemapping.frag, and
         * depth_cues.frag -- any shader routed through renderToTexture().
         * The compute shader (computeProgram) is managed here in main.cpp;
         * resetting it to 0 triggers lazy re-creation on the next frame. */
        reloadAllRenderShaders();

        if (computeProgram != 0) {
          glDeleteProgram(computeProgram);
          computeProgram = 0;
          std::cout << "[HotReload] Queued recompile: shader/geodesic_trace.comp\n";
        }
      }
#endif

      // Update input manager
      InputManager::instance().update(deltaTime);
      auto &input = InputManager::instance();

      if (rs.timing.gpuTimingEnabled && !rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.init();
      } else if (!rs.timing.gpuTimingEnabled && rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.shutdown();
      }
      if (rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.resolve();
      }
      rs.timing.timingHistory.push(cpuFrameMs, rs.timing.gpuTimers);
      TRACY_PLOT("cpu_frame_ms", cpuFrameMs);
      if (rs.timing.gpuTimers.initialized) {
        TRACY_PLOT("gpu_fragment_ms", rs.timing.gpuTimers.blackholeFragment.lastMs);
        TRACY_PLOT("gpu_compute_ms", rs.timing.gpuTimers.blackholeCompute.lastMs);
        TRACY_PLOT("gpu_bloom_ms", rs.timing.gpuTimers.bloom.lastMs);
        TRACY_PLOT("gpu_tonemap_ms", rs.timing.gpuTimers.tonemap.lastMs);
        TRACY_PLOT("gpu_depth_ms", rs.timing.gpuTimers.depth.lastMs);
        TRACY_PLOT("gpu_grmhd_slice_ms", rs.timing.gpuTimers.grmhdSlice.lastMs);
      }

      // --record-frames: one-time initialization (cinematic quality, 1920x1080, no vsync)
      if (!recordFramesDir.empty() && !rs.recording.recordInitDone) {
        std::error_code recordDirEc;
        std::filesystem::create_directories(recordFramesDir, recordDirEc);
        if (recordDirEc) {
          std::fprintf(stderr, "record output directory create failed: %s (%s)\n",
                       recordFramesDir.c_str(), recordDirEc.message().c_str());
          return 1;
        }
        rs.recording.recordInitDone     = true;
        int recordWidth = 1920;
        int recordHeight = 1080;
        if (char const *const envWidth = std::getenv("BLACKHOLE_RECORD_WIDTH")) {
          int const parsed = std::atoi(envWidth);
          if (parsed > 0) {
            recordWidth = parsed;
          }
        }
        if (char const *const envHeight = std::getenv("BLACKHOLE_RECORD_HEIGHT")) {
          int const parsed = std::atoi(envHeight);
          if (parsed > 0) {
            recordHeight = parsed;
          }
        }
        glfwSetWindowSize(window, recordWidth, recordHeight);
        glfwSwapInterval(0);
        rs.display.swapInterval       = 0;
        if (recordProfile == "compare-orbit-near") {
          rs.disk.adiskEnabled       = false;
          rs.disk.adiskParticle      = false;
          rs.physicsCore.enableRedshift     = false;
          rs.physicsCore.enablePhotonSphere = false;
          rs.hawking.hawkingGlowEnabled = false;
          rs.rte.rteVolumetricEnabled = false;
          rs.stokes.stokesEnabled      = false;
          rs.disk.useNoiseTexture    = false;
          rs.disk.noiseTextureReady  = true;
          rs.disk.adiskNoiseLOD      = 3.0f;
          rs.disk.adiskNoiseScale    = 0.5f;
          rs.disk.adiskDensityV      = 2.0f;
          rs.disk.adiskLit           = 0.25f;
          rs.disk.dopplerStrength    = 1.0f;
          rs.disk.photonSphereGlowStrength = 1.0f;
          rs.post.bloomIterations    = 4;
          rs.post.bloomStrength      = 0.08f;
          rs.post.tonemappingEnabled = true;
          rs.post.toneExposure       = 6.0f;
          rs.post.gamma              = 2.35f;
          rs.dispatch.computeMaxSteps    = 1000;
          rs.dispatch.computeStepSize    = 0.02f;
          rs.display.depthFar           = 154.367004f;
          rs.physicsCore.kerrSpin           = 0.0f;
          SettingsManager::instance().get().backgroundId = "eso_milkyway_brunier";
          SettingsManager::instance().get().backgroundEnabled = true;
          SettingsManager::instance().get().backgroundIntensity = 0.8f;
          CameraState &camMutable = input.camera();
          camMutable = CameraState{.yaw = -90.0f, .pitch = 0.0f, .roll = 0.0f, .distance = 10.0f, .fov = 90.0f};
          rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
        } else if (recordProfile == "showcase-orbit") {
          const ShowcaseOrbitComposition *const composition =
              findShowcaseOrbitComposition(recordComposition);
          rs.disk.adiskEnabled       = true;
          rs.disk.adiskParticle      = false;
          rs.physicsCore.enableRedshift     = true;
          rs.physicsCore.enablePhotonSphere = true;
          rs.hawking.hawkingGlowEnabled = false;
          rs.rte.rteVolumetricEnabled = false;
          rs.stokes.stokesEnabled      = false;
          rs.disk.useNoiseTexture    = false;
          rs.disk.noiseTextureReady  = true;
          rs.disk.adiskNoiseLOD      = 3.0f;
          rs.disk.adiskNoiseScale    = 0.35f;
          rs.disk.adiskDensityV      = 1.6f;
          rs.disk.adiskDensityH      = 2.1f;
          rs.disk.adiskHeight        = 0.42f;
          rs.disk.adiskLit           = 0.24f;
          rs.disk.dopplerStrength    = 1.15f;
          rs.disk.photonSphereGlowStrength = 1.15f;
          rs.post.bloomIterations    = 5;
          rs.post.bloomStrength      = 0.055f;
          rs.post.tonemappingEnabled = true;
          rs.post.toneExposure       = 1.0f;
          rs.post.gamma              = 2.35f;
          rs.dispatch.computeMaxSteps    = 1000;
          rs.dispatch.computeStepSize    = 0.016f;
          rs.display.depthFar           = 154.367004f;
          rs.physicsCore.kerrSpin           = 0.62f;
          SettingsManager::instance().get().backgroundId =
              hasRecordBackgroundId
                  ? recordBackgroundId
                  : (composition != nullptr ? composition->backgroundId
                                            : "nasa_deep_starmap_galactic");
          SettingsManager::instance().get().backgroundEnabled = true;
          SettingsManager::instance().get().backgroundIntensity =
              composition != nullptr ? composition->backgroundIntensity : 0.72f;
          CameraState &camMutable = input.camera();
          camMutable = CameraState{
              .yaw = hasRecordYaw ? recordYawDeg : -90.0f,
              .pitch = hasRecordPitch ? recordPitchDeg
                                      : (composition != nullptr ? composition->pitchDeg : -6.0f),
              .roll = 0.0f,
              .distance = hasRecordDistance ? recordDistance
                                            : (composition != nullptr ? composition->distance
                                                                      : 14.0f),
              .fov = hasRecordFov ? recordFovDeg
                                  : (composition != nullptr ? composition->fovDeg : 68.0f)};
          if (hasRecordExposure) {
            rs.post.toneExposure = recordExposure;
          } else if (composition != nullptr) {
            rs.post.toneExposure = composition->exposure;
          }
          rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
        } else {
          // Physics: on, but not everything -- avoids noise pileup / fuzz
          rs.disk.adiskEnabled       = true;
          rs.disk.adiskParticle      = false;  // particle mode adds visual noise
          rs.physicsCore.enableRedshift     = true;
          rs.physicsCore.enablePhotonSphere = true;
          rs.hawking.hawkingGlowEnabled = false;  // haze effect competes with disk shading
          rs.rte.rteVolumetricEnabled = false; // volumetric fog washes out fine detail
          rs.stokes.stokesEnabled      = false;
          // Skip noise texture LUT generation in record mode: FastNoise2
          // SIMD code has a heap double-free at >= 128^3 on this system.
          // The disk looks clean without it.
          rs.disk.useNoiseTexture    = false;
          rs.disk.noiseTextureReady  = true;   // mark done so we never call initialize()
          rs.disk.adiskNoiseLOD      = 3.0f;
          rs.disk.adiskNoiseScale    = 0.5f;
          rs.disk.adiskDensityV      = 1.4f;
          rs.disk.adiskLit           = 0.08f;
          rs.disk.dopplerStrength    = 1.0f;
          rs.disk.photonSphereGlowStrength = 1.0f;
          // Post-processing: preserve ring detail instead of washing it out
          rs.post.bloomIterations    = 3;
          rs.post.bloomStrength      = 0.03f;
          rs.post.tonemappingEnabled = true;
          rs.post.toneExposure       = 0.02f;
          rs.post.gamma              = 2.25f;
          // Integration quality
          rs.dispatch.computeMaxSteps    = 500;   // more steps for wide shots at 350+ rs
          rs.dispatch.computeStepSize    = 0.08f;
          // Escape radius must exceed the maximum camera distance (380 rs).
          // depthFar is passed as interop.depthFar and used as the ray max_dist.
          rs.display.depthFar           = 500.0f;
          rs.physicsCore.kerrSpin           = K_CINEMATIC_KEYFRAMES[0].kerrSpin;
          // Background: override to the ESO Milky Way panorama which ships as a real
          // JPEG (not a Git LFS pointer) -- the default "nasa_pia22085" is LFS-tracked.
          SettingsManager::instance().get().backgroundId = "eso_milkyway_brunier";
          SettingsManager::instance().get().backgroundEnabled = true;
          SettingsManager::instance().get().backgroundIntensity = 0.8f;
        }
#if BLACKHOLE_HAS_CUDA
        // Keep legacy record profiles on the CUDA path in the hybrid app, but let
        // showcase-orbit remain a true GLSL lane for apples-to-apples captures.
        if (recordProfile != "showcase-orbit") {
          // isEnabled() gates the CUDA dispatch path (line ~4295). It is normally set
          // via the ImGui "Use CUDA Raytracer" checkbox; record mode must set it directly.
          // useComputeRaytracer alone is insufficient -- it only controls the GLSL compute
          // path, not the CUDA path.
          rs.dispatch.cudaManager.setEnabled(true);
        } else {
          rs.dispatch.cudaManager.setEnabled(false);
          rs.dispatch.useComputeRaytracer = false;
          rs.compare.compareComputeFragment = false;
        }
#endif
        std::printf("Record mode: dir=%s  frames=%d  duration=%.0f s @ %d fps\n",
                    recordFramesDir.c_str(), recordFramesTotal,
                    static_cast<double>(K_CINEMATIC_DURATION_S), K_CINEMATIC_FPS);
        std::printf("Record profile: %s\n", recordProfile.c_str());
      }

      ImGui_ImplOpenGL3_NewFrame();
      ImGui_ImplGlfw_NewFrame();
      ImGui::NewFrame();
      ImGuizmo::BeginFrame();

      int windowWidth;
      int windowHeight;
      glfwGetFramebufferSize(window, &windowWidth, &windowHeight);
      if (windowWidth == 0 || windowHeight == 0) {
        glfwWaitEvents();
        continue;
      }
      glViewport(0, 0, windowWidth, windowHeight);

      // ---------------------------------------------------------
      // DOCKING & VIEWPORT SETUP (EARLY)
      // ---------------------------------------------------------
      ImGuiID const dockspaceId = ImGui::GetID("MyDockSpace");
      ImGui::DockSpaceOverViewport(dockspaceId, ImGui::GetMainViewport(), ImGuiDockNodeFlags_None);

      if (rs.overlays.firstLayout) {
        resetLayout(dockspaceId);
        rs.overlays.firstLayout = false;
      }

      ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0.0f, 0.0f));
      ImGui::Begin("Viewport", nullptr,
                   ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse |
                       ImGuiWindowFlags_NoTitleBar);
      ImVec2 viewportSize = ImGui::GetContentRegionAvail();

      // Resize render targets to match viewport
      if (viewportSize.x > 0 && viewportSize.y > 0 &&
          (static_cast<int>(viewportSize.x) != rs.targets.renderWidth ||
           static_cast<int>(viewportSize.y) != rs.targets.renderHeight)) {
        recreateRenderTargets(static_cast<int>(viewportSize.x), static_cast<int>(viewportSize.y));
      }
      ImGui::End();
      ImGui::PopStyleVar();

      if (rs.overlays.rmluiEnabled) {
        if (!rs.overlays.rmluiReady) {
          rs.overlays.rmluiReady = rs.overlays.rmluiOverlay.init(window, windowWidth, windowHeight);
        }
        if (rs.overlays.rmluiReady && (windowWidth != rs.overlays.rmluiWidth || windowHeight != rs.overlays.rmluiHeight)) {
          rs.overlays.rmluiOverlay.resize(windowWidth, windowHeight);
          rs.overlays.rmluiWidth = windowWidth;
          rs.overlays.rmluiHeight = windowHeight;
        }
      } else if (rs.overlays.rmluiReady) {
        rs.overlays.rmluiOverlay.shutdown();
        rs.overlays.rmluiReady = false;
      }

      if (!rs.background.baseTexturesLoaded) {
        rs.background.galaxy = loadCubemap(resourcePath("assets/skybox_nebula_dark"));
        rs.background.colorMap = loadTexture2D(resourcePath("assets/color_map.png"));
        rs.background.baseTexturesLoaded = true;
      }
      if (!recordFramesDir.empty() && recordProfile == "showcase-orbit") {
        const ShowcaseOrbitComposition *const composition =
            findShowcaseOrbitComposition(recordComposition);
        rs.background.backgroundLayerScale = {1.0f, 1.18f, 1.42f};
        rs.background.backgroundLayerIntensity = {1.0f, 0.94f, 0.72f};
        rs.background.backgroundLayerLodBias = {0.45f, 1.2f, 1.9f};
        rs.background.backgroundLayerGlobalOffset =
            composition != nullptr
                ? glm::vec2(composition->backgroundOffsetX, composition->backgroundOffsetY)
                : glm::vec2(0.0f);
        rs.background.backgroundYawRad = glm::radians(hasRecordBackgroundYaw
                                            ? recordBackgroundYawDeg
                                            : (composition != nullptr ? composition->backgroundYawDeg
                                                                      : 0.0f));
        rs.background.backgroundPitchRad = glm::radians(hasRecordBackgroundPitch
                                              ? recordBackgroundPitchDeg
                                              : (composition != nullptr
                                                     ? composition->backgroundPitchDeg
                                                     : 0.0f));
        rs.post.tonemapChromaticAberrationStrength = 0.00015f;
        rs.post.tonemapVignetteStrength = 0.05f;
        rs.post.tonemapFilmGrainStrength = 0.0f;
      } else {
        rs.background.backgroundLayerScale = {1.0f, 1.08f, 1.16f};
        rs.background.backgroundLayerIntensity = {1.0f, 0.6f, 0.35f};
        rs.background.backgroundLayerLodBias = {0.0f, 1.0f, 2.0f};
        rs.background.backgroundLayerGlobalOffset = glm::vec2(0.0f);
        rs.background.backgroundYawRad = 0.0f;
        rs.background.backgroundPitchRad = 0.0f;
        rs.post.tonemapChromaticAberrationStrength = 0.002f;
        rs.post.tonemapVignetteStrength = 1.0f;
        rs.post.tonemapFilmGrainStrength = 0.005f;
      }
      if (!rs.debug.debugPreShapingBackgroundEnvApplied) {
        if (const char *stage = std::getenv("BLACKHOLE_EXPORT_RAW_STAGE")) {
          rs.debug.debugPreRedshiftBackground =
              (std::strcmp(stage, "pre-redshift-background") == 0);
          rs.debug.debugPreShapingBackground =
              (std::strcmp(stage, "pre-shaping-background") == 0);
          rs.debug.debugPostShapingBackground =
              (std::strcmp(stage, "post-shaping-background") == 0);
          rs.debug.debugShaperInputs =
              (std::strcmp(stage, "shaper-inputs") == 0);
          rs.debug.debugClosestApproachState =
              (std::strcmp(stage, "closest-approach-state") == 0);
          rs.debug.debugClosestApproachTimeline =
              (std::strcmp(stage, "closest-approach-timeline") == 0);
          rs.debug.debugClosestApproachDirection =
              (std::strcmp(stage, "closest-approach-direction") == 0);
          rs.debug.debugEscapedDirection =
              (std::strcmp(stage, "escaped-direction") == 0);
        }
        rs.debug.debugPreShapingBackgroundEnvApplied = true;
      }
      if (!rs.wiregrid.wiregridEnvApplied) {
        auto parseEnvFloat = [](const char *name, float &out) {
          if (const char *value = std::getenv(name)) {
            char *end = nullptr;
            float parsed = std::strtof(value, &end);
            if (end != value) {
              out = parsed;
            }
          }
        };
        if (const char *enabled = std::getenv("BLACKHOLE_WIREGRID_ENABLED")) {
          rs.wiregrid.wiregridEnabled = (std::strcmp(enabled, "0") != 0);
        }
        applyWiregridModeProfile(WiregridParams::Mode::Beauty, rs.wiregrid.wiregridParams, rs.wiregrid.wiregridColor);
        if (const char *mode = std::getenv("BLACKHOLE_WIREGRID_MODE")) {
          if (std::strcmp(mode, "diagnostic") == 0) {
            applyWiregridModeProfile(WiregridParams::Mode::Diagnostic, rs.wiregrid.wiregridParams,
                                     rs.wiregrid.wiregridColor);
          } else if (std::strcmp(mode, "beauty") == 0) {
            applyWiregridModeProfile(WiregridParams::Mode::Beauty, rs.wiregrid.wiregridParams,
                                     rs.wiregrid.wiregridColor);
          }
        }
        if (const char *showErgo = std::getenv("BLACKHOLE_WIREGRID_SHOW_ERGO")) {
          rs.wiregrid.wiregridParams.showErgosphere = (std::strcmp(showErgo, "0") != 0);
        }
        parseEnvFloat("BLACKHOLE_WIREGRID_GRID_SCALE", rs.wiregrid.wiregridParams.gridScale);
        parseEnvFloat("BLACKHOLE_WIREGRID_MOTION_SCALE", rs.wiregrid.wiregridParams.motionScale);
        parseEnvFloat("BLACKHOLE_WIREGRID_INFALL_SCALE", rs.wiregrid.wiregridParams.infallScale);
        parseEnvFloat("BLACKHOLE_WIREGRID_STRENGTH", rs.wiregrid.wiregridParams.strength);
        parseEnvFloat("BLACKHOLE_WIREGRID_SCENE_PRESERVE", rs.wiregrid.wiregridParams.scenePreserve);
        parseEnvFloat("BLACKHOLE_WIREGRID_COLOR_R", rs.wiregrid.wiregridColor.r);
        parseEnvFloat("BLACKHOLE_WIREGRID_COLOR_G", rs.wiregrid.wiregridColor.g);
        parseEnvFloat("BLACKHOLE_WIREGRID_COLOR_B", rs.wiregrid.wiregridColor.b);
        parseEnvFloat("BLACKHOLE_WIREGRID_COLOR_A", rs.wiregrid.wiregridColor.a);
        rs.wiregrid.wiregridEnvApplied = true;
      }
      if (!recordFramesDir.empty() && recordProfile == "showcase-orbit" &&
          rs.wiregrid.wiregridEnabled && rs.wiregrid.wiregridParams.mode == WiregridParams::Mode::Beauty) {
        applyShowcaseBeautyWiregridTuning(recordComposition, rs.wiregrid.wiregridParams, rs.wiregrid.wiregridColor);
      }
      if (rs.background.fallback2D == 0) {
        rs.background.fallback2D = createColorTexture(1, 1, false);
      }
      if (rs.background.fallback3D == 0) {
        rs.background.fallback3D = createFloatTexture3D(1, 1, 1, std::vector<float>{0.0f});
      }
      if (rs.background.fallbackCubemap == 0) {
        rs.background.fallbackCubemap = createSolidCubemap1x1(0, 0, 0);
      }
      if (rs.background.backgroundAssets.empty()) {
        rs.background.backgroundAssets = loadBackgroundAssets();
      }
      if (!rs.background.backgroundAssets.empty()) {
        rs.background.backgroundIndex = findBackgroundIndex(rs.background.backgroundAssets, settings.backgroundId);
        if (rs.background.backgroundIndex < 0 ||
            std::cmp_greater_equal(rs.background.backgroundIndex, rs.background.backgroundAssets.size())) {
          rs.background.backgroundIndex = 0;
        }
        const auto &asset = rs.background.backgroundAssets.at(static_cast<std::size_t>(rs.background.backgroundIndex));
        if (rs.background.backgroundLoadedId != asset.id) {
          GLuint const nextTexture = loadTexture2D(asset.path, true);
          if (nextTexture != 0) {
            if (rs.background.backgroundBase != 0) {
              glDeleteTextures(1, &rs.background.backgroundBase);
            }
            rs.background.backgroundBase = nextTexture;
            rs.background.backgroundLoadedId = asset.id;
          }
          // Swap cubemap skybox if the asset specifies one.
          if (!asset.skyboxDir.empty() && rs.background.skyboxLoadedDir != asset.skyboxDir) {
            GLuint const nextCubemap = loadCubemap(asset.skyboxDir);
            if (nextCubemap != 0) {
              if (rs.background.galaxy != 0) {
                glDeleteTextures(1, &rs.background.galaxy);
              }
              rs.background.galaxy = nextCubemap;
              rs.background.skyboxLoadedDir = asset.skyboxDir;
            }
          }
        }
      }
      GLuint const backgroundFallback = rs.background.backgroundBase != 0 ? rs.background.backgroundBase : rs.background.fallback2D;
      rs.background.backgroundTextures.fill(backgroundFallback);
      if (!rs.disk.noiseTextureReady) {
        bool const noiseOk = rs.disk.noiseCache.initialize();
        rs.disk.noiseTextureReady = true;  // don't retry regardless; FastNoise2 may be disabled
        if (noiseOk) {
          rs.disk.texNoiseVolume = rs.disk.noiseCache.getTurbulenceTexture();
        }
      }

      if (!rs.camera.cameraSettingsLoaded) {
        rs.camera.cameraModeIndex = settings.cameraMode;
        rs.camera.orbitRadius = settings.orbitRadius;
        rs.camera.orbitSpeed = settings.orbitSpeed;
        rs.camera.cameraSettingsLoaded = true;
      }

      if (!rs.display.displaySettingsLoaded) {
        rs.display.renderScale = settings.renderScale;
        rs.display.swapInterval = settings.swapInterval;
        rs.display.displaySettingsLoaded = true;
      }
      if (!rs.post.postProcessingSettingsLoaded) {
        rs.post.bloomStrength = settings.bloomStrength;
        rs.post.tonemappingEnabled = settings.tonemappingEnabled;
        rs.post.toneExposure = 1.0f;
        rs.post.gamma = settings.gamma;
        rs.post.postProcessingSettingsLoaded = true;
      }
      if (!recordFramesDir.empty()) {
        const ShowcaseOrbitComposition *const composition =
            recordProfile == "showcase-orbit" ? findShowcaseOrbitComposition(recordComposition)
                                              : nullptr;
        if (hasRecordExposure) {
          rs.post.toneExposure = recordExposure;
        } else if (recordProfile == "showcase-orbit") {
          rs.post.toneExposure = composition != nullptr ? composition->exposure : 3.4f;
        }
      }
      if (!rs.post.bloomSettingsLoaded) {
        rs.post.bloomIterations = std::clamp(settings.bloomIterations, 1, kMaxBloomIterations);
        rs.post.bloomSettingsLoaded = true;
      }

      rs.display.renderScale = std::clamp(rs.display.renderScale, 0.25f, 1.5f);
      // Legacy resize logic disabled in favor of Viewport-based sizing
      /*
      int targetWidth =
          std::max(1, static_cast<int>(static_cast<float>(windowWidth) * rs.display.renderScale));
      int targetHeight =
          std::max(1, static_cast<int>(static_cast<float>(windowHeight) * rs.display.renderScale));
      if (targetWidth != rs.targets.renderWidth || targetHeight != rs.targets.renderHeight) {
        recreateRenderTargets(targetWidth, targetHeight);
      }
      */
      settings.fullscreen = input.isFullscreen();
      settings.swapInterval = rs.display.swapInterval;
      settings.renderScale = rs.display.renderScale;
      settings.bloomStrength = rs.post.bloomStrength;
      settings.tonemappingEnabled = rs.post.tonemappingEnabled;
      settings.gamma = rs.post.gamma;
      settings.bloomIterations = rs.post.bloomIterations;

      rs.compare.comparePresetSettleFrames = std::clamp(rs.compare.comparePresetSettleFrames, 1, 10);
      bool const compareSweepAllowed =
          rs.compare.compareComputeFragment && ShaderManager::instance().canUseComputeShaders();
      if (rs.compare.comparePresetSweep && !compareSweepAllowed) {
        rs.compare.comparePresetSweep = false;
        if (rs.compare.comparePresetSaved) {
          rs.compare.compareRestorePending = true;
        }
      }
      if (rs.compare.comparePresetSweep) {
        if (!rs.compare.comparePresetSaved) {
          rs.compare.comparePresetSavedCamera = input.camera();
          rs.compare.comparePresetSavedMode = rs.camera.cameraModeIndex;
          rs.compare.comparePresetSavedOrbitRadius = rs.camera.orbitRadius;
          rs.compare.comparePresetSavedOrbitSpeed = rs.camera.orbitSpeed;
          rs.compare.comparePresetSavedOrbitTime = rs.camera.orbitTime;
          rs.compare.comparePresetSavedKerrSpin = rs.physicsCore.kerrSpin;
          rs.compare.comparePresetSaved = true;
        }
        int const presetCount = static_cast<int>(K_COMPARE_PRESETS.size());
        rs.compare.comparePresetIndex = std::clamp(rs.compare.comparePresetIndex, 0, presetCount);
        if (rs.compare.comparePresetIndex >= presetCount) {
          rs.compare.comparePresetSweep = false;
          rs.compare.compareRestorePending = true;
        } else {
          const auto &preset = K_COMPARE_PRESETS.at(static_cast<std::size_t>(rs.compare.comparePresetIndex));
          CameraState &camMutable = input.camera();
          camMutable = preset.camera;
          rs.camera.cameraModeIndex = static_cast<int>(preset.mode);
          rs.camera.orbitRadius = preset.orbitRadius;
          rs.camera.orbitSpeed = preset.orbitSpeed;
          rs.camera.orbitTime = 0.0f;
          rs.physicsCore.kerrSpin = preset.kerrSpin;
          rs.compare.comparePresetFrameCounter++;
          if (rs.compare.comparePresetFrameCounter >= rs.compare.comparePresetSettleFrames) {
            rs.compare.captureCompareSnapshot = true;
            rs.compare.comparePresetFrameCounter = 0;
            rs.compare.comparePresetIndex++;
            if (rs.compare.comparePresetIndex >= presetCount) {
              rs.compare.comparePresetSweep = false;
              rs.compare.compareRestorePending = true;
            }
          }
        }
      }

      // --record-frames: drive camera and spin from the selected record path
      if (!recordFramesDir.empty()) {
        if (recordProfile == "compare-orbit-near") {
          float const denom = static_cast<float>(std::max(recordFramesTotal - 1, 1));
          float const progress =
              static_cast<float>(rs.recording.recordFrameIndex - recordStartFrame) / denom;
          CameraState &camMutable = input.camera();
          camMutable.yaw = -90.0f + progress * 18.0f;
          camMutable.pitch = 0.0f;
          camMutable.roll = 0.0f;
          camMutable.distance = 10.0f;
          camMutable.fov = 90.0f;
          rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
          rs.physicsCore.kerrSpin = 0.0f;
        } else if (recordProfile == "showcase-orbit") {
          const ShowcaseOrbitComposition *const composition =
              findShowcaseOrbitComposition(recordComposition);
          float const denom = static_cast<float>(std::max(recordFramesTotal - 1, 1));
          float const progress =
              static_cast<float>(rs.recording.recordFrameIndex - recordStartFrame) / denom;
          float const baseYaw = hasRecordYaw ? recordYawDeg : -90.0f;
          float const sweepDeg =
              hasRecordSweep ? recordSweepDeg
                             : (composition != nullptr ? composition->sweepDeg : 10.0f);
          CameraState &camMutable = input.camera();
          camMutable.yaw = baseYaw + progress * sweepDeg;
          camMutable.pitch = hasRecordPitch ? recordPitchDeg
                                            : (composition != nullptr ? composition->pitchDeg
                                                                      : -6.0f);
          camMutable.roll = 0.0f;
          camMutable.distance = hasRecordDistance ? recordDistance
                                                  : (composition != nullptr
                                                         ? composition->distance
                                                         : 14.0f);
          camMutable.fov = hasRecordFov ? recordFovDeg
                                        : (composition != nullptr ? composition->fovDeg : 68.0f);
          rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
          rs.physicsCore.kerrSpin = 0.0f;
          rs.recording.recordCurrentKf = CamKeyframe{
              .t_sec = static_cast<float>(rs.recording.recordFrameIndex - recordStartFrame) /
                       static_cast<float>(K_CINEMATIC_FPS),
              .cam = camMutable,
              .kerrSpin = rs.physicsCore.kerrSpin,
              .caption = "Showcase orbit",
          };
        } else {
          rs.recording.recordCurrentKf = rs.recording.recordPath.evaluate(rs.recording.recordCinematic);
          CameraState &camMutable = input.camera();
          camMutable   = rs.recording.recordCurrentKf.cam;
          rs.camera.cameraModeIndex = static_cast<int>(CameraMode::Input);
          rs.physicsCore.kerrSpin     = rs.recording.recordCurrentKf.kerrSpin;
        }
      }

      // Get camera state for shader
      const auto &cam = input.camera();
      rs.camera.cameraModeIndex = std::clamp(rs.camera.cameraModeIndex, 0, 3);
      rs.camera.orbitRadius = std::max(rs.camera.orbitRadius, 2.0f);
      rs.camera.orbitSpeed = std::max(rs.camera.orbitSpeed, 0.0f);

      glm::vec3 const focusTarget =
          rs.camera.gizmoEnabled ? glm::vec3(rs.camera.gizmoTransform[3]) : glm::vec3(0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                                         // -- glm::mat has no .at()

      rs.camera.orbitTime += input.getEffectiveDeltaTime(deltaTime);
      glm::vec3 cameraPos;
      auto const cameraMode = static_cast<CameraMode>(rs.camera.cameraModeIndex);
      switch (cameraMode) {
      case CameraMode::Front:
        cameraPos = focusTarget + glm::vec3(10.0f, 1.0f, 10.0f);
        break;
      case CameraMode::Top:
        cameraPos = focusTarget + glm::vec3(15.0f, 15.0f, 0.0f);
        break;
      case CameraMode::Orbit: {
        float const angle = rs.camera.orbitTime * glm::radians(rs.camera.orbitSpeed);
        cameraPos =
            focusTarget + glm::vec3(-std::cos(angle) * rs.camera.orbitRadius, std::sin(angle) * rs.camera.orbitRadius,
                                    std::sin(angle) * rs.camera.orbitRadius);
        break;
      }
      case CameraMode::Input:
      default:
        cameraPos = focusTarget + cameraPositionFromYawPitch(cam.yaw, cam.pitch, cam.distance);
        break;
      }

      glm::vec3 aimTarget = focusTarget;
      if (!recordFramesDir.empty() && recordProfile == "showcase-orbit") {
        const ShowcaseOrbitComposition *const composition =
            findShowcaseOrbitComposition(recordComposition);
        float const frameX =
            hasRecordFrameX ? recordFrameX
                            : (composition != nullptr ? composition->frameOffsetX : 0.0f);
        float const frameY =
            hasRecordFrameY ? recordFrameY
                            : (composition != nullptr ? composition->frameOffsetY : 0.0f);
        if (std::abs(frameX) > 0.0001f || std::abs(frameY) > 0.0001f) {
          glm::mat3 const baseBasis = buildCameraBasis(cameraPos, focusTarget, cam.roll);
          float const halfHeight = std::tan(glm::radians(cam.fov) * 0.5f) * cam.distance;
          float const aspect =
              static_cast<float>(std::max(rs.targets.renderWidth, 1)) /
              static_cast<float>(std::max(rs.targets.renderHeight, 1));
          float const halfWidth = halfHeight * aspect;
          aimTarget = focusTarget + baseBasis[0] * (frameX * halfWidth) +
                      baseBasis[1] * (frameY * halfHeight);
        }
      }

      glm::mat3 cameraBasis = buildCameraBasis(cameraPos, aimTarget, cam.roll);
      float const fovScale = std::tan(glm::radians(cam.fov) * 0.5f);
      glm::mat4 viewRotation(1.0f);
      viewRotation[0] = glm::vec4(cameraBasis[0], 0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                         // -- glm::mat has no .at()
      viewRotation[1] = glm::vec4(cameraBasis[1], 0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                         // -- glm::mat has no .at()
      viewRotation[2] = glm::vec4(cameraBasis[2], 0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                         // -- glm::mat has no .at()

      glm::vec2 const parallaxBase =
          glm::vec2(cameraPos.x, cameraPos.y) * settings.backgroundParallaxStrength;
      glm::vec2 const drift = glm::vec2(std::cos(static_cast<float>(currentTime) * 0.02f),
                                        std::sin(static_cast<float>(currentTime) * 0.02f)) *
                              settings.backgroundDriftStrength;
      for (std::size_t i = 0; i < static_cast<std::size_t>(K_BACKGROUND_LAYERS); ++i) {
        glm::vec2 const offset = drift + parallaxBase * rs.background.backgroundLayerDepth.at(i);
        rs.background.backgroundLayerParams.at(i) =
            glm::vec4(offset + rs.background.backgroundLayerGlobalOffset, rs.background.backgroundLayerScale.at(i),
                      rs.background.backgroundLayerIntensity.at(i));
      }
      glm::mat4 projectionMatrix = glm::perspective(
          glm::radians(cam.fov), static_cast<float>(rs.targets.renderWidth) / static_cast<float>(rs.targets.renderHeight),
          0.1f, rs.display.depthFar);
      glm::mat4 gizmoViewMatrix =
          glm::lookAt(cameraPos, aimTarget, cameraBasis[1]); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                                                               // -- glm::mat has no .at()
      bool computeActiveForLog = false;

      /* Per-frame streaming tile upload: when GRMHDStreamer is running and the
       * PBOUploader is initialized, obtain the current frame tile and upload.
       * getTile() is non-blocking; on a cache miss it enqueues the request. */
      if (rs.grmhd.grmhdStreamer && rs.grmhd.grmhdPboUploader.texture() != 0) {
        auto tile = rs.grmhd.grmhdStreamer->getTile(0, 0, 0, 0);
        if (tile && tile->ready()) {
          rs.grmhd.grmhdPboUploader.upload(tile->data.data(), tile->data.size());
        }
      }
      /* C1d: upload adjacent (next) frame into the right PBO uploader for
       * temporal interpolation.  getAdjacentTile() returns nullptr at the last
       * frame or on a cache miss (seekFrame prefetch keeps it warm).
       * rs.grmhd.grmhdFrameAlpha is the sub-frame blend fraction; sub-frame position is
       * approximated as the fractional part of (current_frame + time_bias). */
      rs.grmhd.grmhdFrameAlpha = 0.0f;
      if (rs.grmhd.grmhdStreamer && rs.grmhd.grmhdPboUploaderRight.texture() != 0) {
        auto rightTile = rs.grmhd.grmhdStreamer->getAdjacentTile(0, 0, 0, 0);
        if (rightTile && rightTile->ready()) {
          rs.grmhd.grmhdPboUploaderRight.upload(rightTile->data.data(), rightTile->data.size());
        }
        /* Advance CUDA slot 7 registration when the right PBO first becomes ready */
#if BLACKHOLE_HAS_CUDA
        if (rs.grmhd.grmhdPboUploaderRight.ready()) {
          if (rs.grmhd.registeredRightTex != rs.grmhd.grmhdPboUploaderRight.texture()) {
            rs.grmhd.registeredRightTex = rs.grmhd.grmhdPboUploaderRight.texture();
            rs.dispatch.cudaManager.registerLut(7 /*BhLutGrmhdRight*/, rs.grmhd.registeredRightTex,
                                    static_cast<unsigned int>(GL_TEXTURE_3D));
          }
        }
#endif
        if (rs.grmhd.grmhdPboUploaderRight.ready()) {
          /* Sub-frame alpha: fraction of inter-frame interval elapsed.
           * rs.grmhd.grmhdPlaybackSpeed controls simulation-time advance per real second. */
          rs.grmhd.grmhdFrameAlpha = std::fmod(
              static_cast<float>(rs.grmhd.grmhdCurrentFrame) * rs.grmhd.grmhdPlaybackSpeed, 1.0f);
          rs.grmhd.grmhdFrameAlpha = std::max(0.0f, std::min(1.0f, rs.grmhd.grmhdFrameAlpha));
        }
      }

      /* grmhdReady: true when packed texture OR PBO streaming path is valid. */
      bool const grmhdReady = (rs.grmhd.grmhdLoaded && rs.grmhd.grmhdTexture.texture != 0) ||
                              (rs.grmhd.grmhdTimeSeriesLoaded && rs.grmhd.grmhdPboUploader.ready());
      bool grmhdEnabled = rs.grmhd.useGrmhd && grmhdReady;
      /* grmhdTexId: prefer PBO streaming texture when the streamer is running;
       * fall back to the packed static texture otherwise. */
      GLuint const grmhdTexId =
          (rs.grmhd.grmhdTimeSeriesLoaded && rs.grmhd.grmhdPboUploader.ready())
              ? rs.grmhd.grmhdPboUploader.texture()
              : rs.grmhd.grmhdTexture.texture;
      bool const spectralReady = rs.luts.spectralLutLoaded && rs.luts.texSpectralLUT != 0;
      bool spectralEnabled = rs.luts.useSpectralLut && spectralReady;
      rs.luts.spectralRadiusMin = std::max(0.0f, rs.luts.spectralRadiusMin);
      rs.luts.spectralRadiusMax = std::max(rs.luts.spectralRadiusMax, rs.luts.spectralRadiusMin + 0.001f);

      if (!rs.luts.grbModulationTried) {
        rs.luts.grbModulationTried = true;
        rs.luts.grbModulationLoaded =
            loadGrbModulationLutAssets(rs.luts.grbModulationValues, rs.luts.grbTimeMin, rs.luts.grbTimeMax);
        if (rs.luts.grbModulationLoaded) {
          if (rs.luts.texGrbModulationLUT != 0) {
            glDeleteTextures(1, &rs.luts.texGrbModulationLUT);
            rs.luts.texGrbModulationLUT = 0;
          }
          int const lutSize = static_cast<int>(rs.luts.grbModulationValues.size());
          rs.luts.texGrbModulationLUT = createFloatTexture2D(lutSize, 1, rs.luts.grbModulationValues);
          rs.luts.grbTimeManualValue = rs.luts.grbTimeMin;
        }
      }
      bool const grbModulationReady = rs.luts.grbModulationLoaded && rs.luts.texGrbModulationLUT != 0;
      bool grbModulationEnabled = false;
      float const grbSpan = std::max(rs.luts.grbTimeMax - rs.luts.grbTimeMin, 0.001f);
      float grbTimeSeconds = 0.0f;
      if (grbModulationReady) {
        if (rs.luts.grbTimeManual) {
          grbTimeSeconds = std::clamp(rs.luts.grbTimeManualValue, rs.luts.grbTimeMin, rs.luts.grbTimeMax);
        } else {
          grbTimeSeconds = rs.luts.grbTimeMin + std::fmod(static_cast<float>(currentTime), grbSpan);
        }
      }

      bool const lutReady = rs.luts.texEmissivityLUT != 0 && rs.luts.texRedshiftLUT != 0;

      {
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/blackhole_main.frag";
        rtti.cubemapUniforms["galaxy"] = rs.background.galaxy != 0 ? rs.background.galaxy : rs.background.fallbackCubemap;
        rtti.textureUniforms["colorMap"] = rs.background.colorMap != 0 ? rs.background.colorMap : rs.background.fallback2D;
        rtti.textureUniforms["emissivityLUT"] = lutReady ? rs.luts.texEmissivityLUT : rs.background.fallback2D;
        rtti.textureUniforms["redshiftLUT"] = lutReady ? rs.luts.texRedshiftLUT : rs.background.fallback2D;
        rtti.textureUniforms["photonGlowLUT"] =
            rs.luts.texPhotonGlowLUT != 0 ? rs.luts.texPhotonGlowLUT : rs.background.fallback2D; // Phase 8.2
        rtti.textureUniforms["diskDensityLUT"] =
            rs.luts.texDiskDensityLUT != 0 ? rs.luts.texDiskDensityLUT : rs.background.fallback2D; // Phase 8.2 P2
        rtti.textureUniforms["spectralLUT"] = spectralEnabled ? rs.luts.texSpectralLUT : rs.background.fallback2D;
        rtti.textureUniforms["grbModulationLUT"] =
            grbModulationReady ? rs.luts.texGrbModulationLUT : rs.background.fallback2D;
        rtti.textureUniforms["hawkingTempLUT"] =
            rs.hawking.hawkingLutsLoaded ? rs.hawking.hawkingRenderer.getTempLUTTexture() : rs.background.fallback2D;
        rtti.textureUniforms["hawkingSpectrumLUT"] =
            rs.hawking.hawkingLutsLoaded ? rs.hawking.hawkingRenderer.getSpectrumLUTTexture() : rs.background.fallback2D;
        for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
          const std::string name = "backgroundLayers[" + std::to_string(i) + "]";
          rtti.textureUniforms[name] = rs.background.backgroundTextures.at(static_cast<std::size_t>(i));
        }
        rs.disk.noiseTextureScale = std::max(rs.disk.noiseTextureScale, 0.01f);
        bool noiseReady = rs.disk.useNoiseTexture && rs.disk.texNoiseVolume != 0;
        rtti.texture3DUniforms["noiseTexture"] = noiseReady ? rs.disk.texNoiseVolume : rs.background.fallback3D;
        rtti.texture3DUniforms["grmhdTexture"] = grmhdEnabled ? grmhdTexId : rs.background.fallback3D;

        rtti.floatUniforms["useNoiseTexture"] = noiseReady ? 1.0f : 0.0f;
        rtti.floatUniforms["useGrmhd"] = grmhdEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["noiseTextureScale"] = rs.disk.noiseTextureScale;
        rtti.floatUniforms["backgroundEnabled"] = settings.backgroundEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["backgroundIntensity"] = settings.backgroundIntensity;
        rtti.floatUniforms["backgroundYawRad"] = rs.background.backgroundYawRad;
        rtti.floatUniforms["backgroundPitchRad"] = rs.background.backgroundPitchRad;
        rtti.floatUniforms["time"] = frameTime;
        rtti.vec3Uniforms["grmhdBoundsMin"] = rs.grmhd.grmhdBoundsMin;
        rtti.vec3Uniforms["grmhdBoundsMax"] = rs.grmhd.grmhdBoundsMax;
        for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
          const std::string name = "backgroundLayerParams[" + std::to_string(i) + "]";
          rtti.vec4Uniforms[name] = rs.background.backgroundLayerParams.at(static_cast<std::size_t>(i));
        }
        for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
          const std::string name = "backgroundLayerLodBias[" + std::to_string(i) + "]";
          rtti.floatUniforms[name] =
              std::max(rs.background.backgroundLayerLodBias.at(static_cast<std::size_t>(i)), 0.0f);
        }

        rtti.targetTexture = rs.targets.texBlackhole;
        rtti.width = rs.targets.renderWidth;
        rtti.height = rs.targets.renderHeight;

        // Render UI controls only if visible
        if (input.isUIVisible()) {
          ImGui::SetNextWindowSize(ImVec2(450, 700), ImGuiCond_FirstUseEver);
          ImGui::Begin("Settings", nullptr, ImGuiWindowFlags_NoCollapse);
          if (ImGui::BeginTabBar("MainTabs")) {
            if (ImGui::BeginTabItem("Visuals")) {
              ImGui::Checkbox("gravitationalLensing", &rs.disk.gravitationalLensing);
              ImGui::SliderInt("Bloom Iterations", &rs.post.bloomIterations, 1, kMaxBloomIterations);
              settings.bloomIterations = rs.post.bloomIterations;
              ImGui::Checkbox("renderBlackHole", &rs.disk.renderBlackHole);
              ImGui::Checkbox("adiskEnabled", &rs.disk.adiskEnabled);
              ImGui::Checkbox("adiskParticle", &rs.disk.adiskParticle);
              ImGui::SliderFloat("adiskDensityV", &rs.disk.adiskDensityV, 0.0f, 10.0f);
              ImGui::SliderFloat("adiskDensityH", &rs.disk.adiskDensityH, 0.0f, 10.0f);
              ImGui::SliderFloat("adiskHeight", &rs.disk.adiskHeight, 0.0f, 1.0f);
              ImGui::SliderFloat("adiskLit", &rs.disk.adiskLit, 0.0f, 4.0f);
              ImGui::SliderFloat("adiskNoiseLOD", &rs.disk.adiskNoiseLOD, 1.0f, 12.0f);
              ImGui::SliderFloat("adiskNoiseScale", &rs.disk.adiskNoiseScale, 0.0f, 10.0f);
              ImGui::Checkbox("Noise Texture", &rs.disk.useNoiseTexture);
              ImGui::SliderFloat("Noise Tex Scale", &rs.disk.noiseTextureScale, 0.05f, 2.0f);
              ImGui::SliderFloat("adiskSpeed", &rs.disk.adiskSpeed, 0.0f, 1.0f);
              ImGui::SliderFloat("dopplerStrength", &rs.disk.dopplerStrength, 0.0f, 5.0f);

              ImGui::Separator();
              ImGui::Text("Volumetric RTE (D2)");
              ImGui::Checkbox("Volumetric RTE", &rs.rte.rteVolumetricEnabled);
              if (rs.rte.rteVolumetricEnabled) {
                ImGui::SliderFloat("RTE Opacity Scale", &rs.rte.rteOpacityScale, 0.0f, 5.0f);
              }

              ImGui::Separator();
              ImGui::Text("Polarized Stokes IQUV (D4)");
              ImGui::Checkbox("Stokes Transport", &rs.stokes.stokesEnabled);
              if (rs.stokes.stokesEnabled) {
                ImGui::SliderFloat("B Field Angle (rad)", &rs.stokes.stokesBFieldAngle, -3.14159f, 3.14159f);
                ImGui::SliderFloat("Faraday Ne Scale",   &rs.stokes.stokesNeScale,     0.0f, 5.0f);
              }

              ImGui::EndTabItem();
            }
            if (ImGui::BeginTabItem("GRMHD")) {
              ImGui::Text("GRMHD Packed");
              ImGui::Checkbox("Use GRMHD Field", &rs.grmhd.useGrmhd);
              ImGui::InputText("GRMHD Meta", rs.grmhd.grmhdPathBuffer.data(), rs.grmhd.grmhdPathBuffer.size());
              if (ImGui::Button("Load GRMHD")) {
                loadGrmhdPacked(rs.grmhd.grmhdPathBuffer.data());
              }
              ImGui::SameLine();
              if (ImGui::Button("Unload GRMHD")) {
                destroyGrmhdPackedTexture(rs.grmhd.grmhdTexture);
                rs.grmhd.grmhdLoaded = false;
                rs.grmhd.grmhdLoadError.clear();
              }
              if (!rs.grmhd.grmhdLoadError.empty()) {
                ImGui::TextColored(ImVec4(1.0f, 0.35f, 0.35f, 1.0f), "%s", rs.grmhd.grmhdLoadError.c_str());
              }
              if (rs.grmhd.grmhdLoaded) {
                ImGui::Text("GRMHD grid: %d x %d x %d", rs.grmhd.grmhdTexture.width, rs.grmhd.grmhdTexture.height,
                            rs.grmhd.grmhdTexture.depth);
              }
              ImGui::SliderFloat3("GRMHD Bounds Min", &rs.grmhd.grmhdBoundsMin.x, -50.0f, 50.0f);
              ImGui::SliderFloat3("GRMHD Bounds Max", &rs.grmhd.grmhdBoundsMax.x, -50.0f, 50.0f);
              ImGui::BeginDisabled(!rs.grmhd.grmhdLoaded);
              ImGui::Checkbox("Show GRMHD Slice", &rs.grmhd.grmhdSliceEnabled);
              const char *const axisLabels[] = {"X", "Y", "Z"};
              ImGui::Combo("Slice Axis", &rs.grmhd.grmhdSliceAxis, axisLabels, 3);
              ImGui::SliderFloat("Slice Coord", &rs.grmhd.grmhdSliceCoord, 0.0f, 1.0f);
              ImGui::SliderInt("Slice Channel", &rs.grmhd.grmhdSliceChannel, 0, 3);
              if (rs.grmhd.grmhdLoaded && rs.grmhd.grmhdSliceChannel >= 0 &&
                  static_cast<std::size_t>(rs.grmhd.grmhdSliceChannel) < rs.grmhd.grmhdTexture.channels.size()) {
                auto const channelIndex = static_cast<std::size_t>(rs.grmhd.grmhdSliceChannel);
                ImGui::Text("Channel: %s", rs.grmhd.grmhdTexture.channels.at(channelIndex).c_str());
              }
              ImGui::Checkbox("Slice Auto Range", &rs.grmhd.grmhdSliceAutoRange);
              if (!rs.grmhd.grmhdSliceAutoRange) {
                ImGui::InputFloat("Slice Min", &rs.grmhd.grmhdSliceMin);
                ImGui::InputFloat("Slice Max", &rs.grmhd.grmhdSliceMax);
              }
              ImGui::Checkbox("Slice Color Map", &rs.grmhd.grmhdSliceUseColorMap);
              ImGui::SliderInt("Slice Size", &rs.grmhd.grmhdSliceSize, 64, 1024);
              if (rs.grmhd.texGrmhdSlice != 0) {
                auto const sliceId =
                    static_cast<ImTextureID>(static_cast<uintptr_t>(rs.grmhd.texGrmhdSlice));
                ImGui::Image(sliceId, ImVec2(192.0f, 192.0f));
              }
              ImGui::EndDisabled();

              // GRMHD Time-Series Playback (Phase 4.3)
              ImGui::Separator();
              ImGui::TextColored(ImVec4(0.3f, 0.9f, 0.9f, 1.0f), "GRMHD Time-Series");
              ImGui::Checkbox("Enable Time-Series Playback", &rs.grmhd.grmhdTimeSeriesEnabled);

              ImGui::BeginDisabled(!rs.grmhd.grmhdTimeSeriesEnabled);

              // File paths
              ImGui::InputText("JSON Metadata", rs.grmhd.grmhdTimeSeriesJsonBuffer.data(),
                               rs.grmhd.grmhdTimeSeriesJsonBuffer.size());
              ImGui::InputText("Binary Data", rs.grmhd.grmhdTimeSeriesBinBuffer.data(),
                               rs.grmhd.grmhdTimeSeriesBinBuffer.size());

              // Load/Unload buttons
              if (ImGui::Button("Load Time-Series")) {
                /* Shut down any previously loaded dataset */
                if (rs.grmhd.grmhdStreamer) {
                  rs.grmhd.grmhdStreamer->shutdown();
                  rs.grmhd.grmhdStreamer.reset();
                  rs.grmhd.grmhdTimeSeriesLoaded = false;
                }
                std::string const jsonPath(rs.grmhd.grmhdTimeSeriesJsonBuffer.data());
                std::string const binPath(rs.grmhd.grmhdTimeSeriesBinBuffer.data());
                if (!jsonPath.empty()) {
                  rs.grmhd.grmhdStreamer = std::make_unique<blackhole::GRMHDStreamer>(jsonPath, binPath);
                  if (rs.grmhd.grmhdStreamer->init()) {
                    rs.grmhd.grmhdTimeSeriesLoaded = true;
                    rs.grmhd.grmhdMaxFrame = static_cast<int>(rs.grmhd.grmhdStreamer->metadata().frameCount) - 1;
                    rs.grmhd.grmhdCurrentFrame = 0;
                    rs.grmhd.grmhdStreamer->seekFrame(0);
                    /* Initialize PBOUploader with the grid dimensions from metadata.
                     * Shuts down any previous allocation first. */
                    const auto &meta = rs.grmhd.grmhdStreamer->metadata();
                    if (rs.grmhd.grmhdPboUploader.texture() != 0) {
                      rs.grmhd.grmhdPboUploader.shutdown();
                    }
                    rs.grmhd.grmhdPboUploader.init(static_cast<int>(meta.gridX),
                                         static_cast<int>(meta.gridY),
                                         static_cast<int>(meta.gridZ));
                    /* C1d: initialize right-frame uploader with same dimensions */
                    if (rs.grmhd.grmhdPboUploaderRight.texture() != 0) {
                      rs.grmhd.grmhdPboUploaderRight.shutdown();
                    }
                    rs.grmhd.grmhdPboUploaderRight.init(static_cast<int>(meta.gridX),
                                              static_cast<int>(meta.gridY),
                                              static_cast<int>(meta.gridZ));
                  } else {
                    rs.grmhd.grmhdStreamer.reset();
                  }
                }
              }
              ImGui::SameLine();
              if (ImGui::Button("Unload Time-Series")) {
                if (rs.grmhd.grmhdStreamer) {
                  rs.grmhd.grmhdStreamer->shutdown();
                  rs.grmhd.grmhdStreamer.reset();
                }
                rs.grmhd.grmhdPboUploader.shutdown();
                rs.grmhd.grmhdPboUploaderRight.shutdown();  /* C1d: tear down right-frame uploader */
                rs.grmhd.grmhdFrameAlpha = 0.0f;
                rs.grmhd.grmhdTimeSeriesLoaded = false;
                rs.grmhd.grmhdCurrentFrame = 0;
                rs.grmhd.grmhdMaxFrame = 0;
                rs.grmhd.grmhdPlaying = false;
                rs.grmhd.grmhdCacheHitRate = 0.0;
                rs.grmhd.grmhdQueueDepth = 0;
              }

              ImGui::BeginDisabled(!rs.grmhd.grmhdTimeSeriesLoaded);

              // Frame control
              ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Playback");
              if (ImGui::SliderInt("Frame", &rs.grmhd.grmhdCurrentFrame, 0, rs.grmhd.grmhdMaxFrame)) {
                if (rs.grmhd.grmhdStreamer) {
                  rs.grmhd.grmhdStreamer->seekFrame(static_cast<uint32_t>(rs.grmhd.grmhdCurrentFrame));
                }
              }
              ImGui::Text("Time: %.2f s", static_cast<double>(rs.grmhd.grmhdCurrentFrame) / 30.0);

              // Play/Pause button
              if (rs.grmhd.grmhdPlaying) {
                if (ImGui::Button("Pause")) {
                  rs.grmhd.grmhdPlaying = false;
                  if (rs.grmhd.grmhdStreamer) { rs.grmhd.grmhdStreamer->pause(); }
                }
              } else {
                if (ImGui::Button("Play")) {
                  rs.grmhd.grmhdPlaying = true;
                  if (rs.grmhd.grmhdStreamer) { rs.grmhd.grmhdStreamer->play(); }
                }
              }
              ImGui::SameLine();
              if (ImGui::Button("Reset")) {
                rs.grmhd.grmhdCurrentFrame = 0;
                if (rs.grmhd.grmhdStreamer) { rs.grmhd.grmhdStreamer->seekFrame(0); }
              }

              // Playback speed
              if (ImGui::SliderFloat("Playback Speed", &rs.grmhd.grmhdPlaybackSpeed, 0.1f, 4.0f)) {
                if (rs.grmhd.grmhdStreamer) {
                  rs.grmhd.grmhdStreamer->setPlaybackSpeed(static_cast<double>(rs.grmhd.grmhdPlaybackSpeed));
                }
              }

              // Cache statistics
              /* Refresh cache stats from live streamer each frame */
              if (rs.grmhd.grmhdStreamer) {
                rs.grmhd.grmhdCacheHitRate = rs.grmhd.grmhdStreamer->cacheHitRate();
                rs.grmhd.grmhdQueueDepth = static_cast<int>(rs.grmhd.grmhdStreamer->queueDepth());
                /* Mirror current frame from streamer (updated by background thread) */
                rs.grmhd.grmhdCurrentFrame = static_cast<int>(rs.grmhd.grmhdStreamer->currentFrame());
              }

              ImGui::Separator();
              ImGui::TextColored(ImVec4(0.2f, 0.9f, 0.9f, 1.0f), "Cache Statistics");
              ImGui::Text("Hit Rate: %.1f%%", rs.grmhd.grmhdCacheHitRate * 100.0);
              ImGui::Text("Queue Depth: %d", rs.grmhd.grmhdQueueDepth);

              // Progress indicator for queue
              if (rs.grmhd.grmhdQueueDepth > 0) {
                ImGui::ProgressBar(static_cast<float>(rs.grmhd.grmhdQueueDepth) / 10.0f, ImVec2(-1.0f, 0.0f),
                                   nullptr);
              }

              // Performance targets reference
              ImGui::Separator();
              ImGui::TextDisabled("Performance Targets:");
              ImGui::TextDisabled("  Cache hit rate: >90%%");
              ImGui::TextDisabled("  Frame load time: <16ms (60 fps)");
              ImGui::TextDisabled("  Memory footprint: <4GB");

              ImGui::EndDisabled(); // !grmhdTimeSeriesLoaded
              ImGui::EndDisabled(); // !grmhdTimeSeriesEnabled

              ImGui::EndTabItem();
            }
            if (ImGui::BeginTabItem("Physics")) {
              ImGui::Text("Physics Parameters");

              // Black hole mass in solar masses (scaled for visualization)
              ImGui::SliderFloat("blackHoleMass", &rs.physicsCore.blackHoleMass, 0.1f, 10.0f);
              // Kerr spin parameter a (|a|<M)
              ImGui::SliderFloat("kerrSpin(a/M)", &rs.physicsCore.kerrSpin, -0.99f, 0.99f);

              // Physics visualization toggles
              ImGui::Checkbox("enablePhotonSphere", &rs.physicsCore.enablePhotonSphere);
              ImGui::Checkbox("enableRedshift", &rs.physicsCore.enableRedshift);

              ImGui::Separator();
              ImGui::Text("Hawking Radiation Glow");
              ImGui::Checkbox("Enable Hawking Glow", &rs.hawking.hawkingGlowEnabled);

              if (rs.hawking.hawkingGlowEnabled) {
                // Preset buttons
                const char *const presetLabels[] = {"Physical", "Primordial", "Extreme"};
                if (ImGui::Combo("Preset", &rs.hawking.hawkingPreset, presetLabels, 3)) {
                  // Apply preset
                  auto const preset = static_cast<physics::HawkingPreset>(rs.hawking.hawkingPreset);
                  physics::HawkingGlowParams const params =
                      physics::HawkingRenderer::applyPreset(preset);
                  rs.hawking.hawkingTempScale = params.tempScale;
                  rs.hawking.hawkingGlowIntensity = params.intensity;
                }

                // Manual controls
                ImGui::SliderFloat("Temp Scale", &rs.hawking.hawkingTempScale, 1.0f, 1e9f, "%.1e",
                                   ImGuiSliderFlags_Logarithmic);
                ImGui::TextDisabled("1=physical, 1e6=primordial, 1e9=extreme");
                ImGui::SliderFloat("Glow Intensity", &rs.hawking.hawkingGlowIntensity, 0.0f, 5.0f);
                ImGui::Checkbox("Use LUTs", &rs.hawking.hawkingUseLUTs);

                if (rs.hawking.hawkingLutsLoaded) {
                  ImGui::TextColored(ImVec4(0.0f, 1.0f, 0.0f, 1.0f), "LUTs loaded");
                } else {
                  ImGui::TextColored(ImVec4(1.0f, 0.35f, 0.35f, 1.0f), "LUTs not loaded");
                }
              }

              ImGui::Separator();
              ImGui::Text("Spectral LUT");
              ImGui::Checkbox("Use Spectral LUT", &rs.luts.useSpectralLut);
              if (rs.luts.spectralLutLoaded) {
                ImGui::Text("Wavelength: %.0f - %.0f A", static_cast<double>(rs.luts.spectralWavelengthMin),
                            static_cast<double>(rs.luts.spectralWavelengthMax));
              } else {
                ImGui::TextDisabled("rt_spectrum_lut.csv not loaded");
              }
              if (ImGui::Button("Reload Spectral LUT")) {
                rs.luts.spectralLutTried = false;
                rs.luts.spectralLutLoaded = false;
                rs.luts.spectralLutValues.clear();
                if (rs.luts.texSpectralLUT != 0) {
                  glDeleteTextures(1, &rs.luts.texSpectralLUT);
                  rs.luts.texSpectralLUT = 0;
                }
              }

              ImGui::Separator();
              ImGui::Text("GRB Modulation");
              ImGui::Checkbox("Use GRB Modulation", &rs.luts.useGrbModulation);
              if (rs.luts.grbModulationLoaded) {
                ImGui::Text("Time: %.2f - %.2f s", static_cast<double>(rs.luts.grbTimeMin),
                            static_cast<double>(rs.luts.grbTimeMax));
              } else {
                ImGui::TextDisabled("grb_modulation_lut.csv not loaded");
              }
              ImGui::BeginDisabled(!rs.luts.grbModulationLoaded);
              ImGui::Checkbox("Manual GRB Time", &rs.luts.grbTimeManual);
              if (rs.luts.grbTimeManual) {
                ImGui::SliderFloat("GRB Time", &rs.luts.grbTimeManualValue, rs.luts.grbTimeMin, rs.luts.grbTimeMax);
              }
              ImGui::EndDisabled();
              if (ImGui::Button("Reload GRB LUT")) {
                rs.luts.grbModulationTried = false;
                rs.luts.grbModulationLoaded = false;
                rs.luts.grbModulationValues.clear();
                if (rs.luts.texGrbModulationLUT != 0) {
                  glDeleteTextures(1, &rs.luts.texGrbModulationLUT);
                  rs.luts.texGrbModulationLUT = 0;
                }
              }
              ImGui::SliderFloat("Spectral Radius Min", &rs.luts.spectralRadiusMin, 0.0f, 50.0f);
              ImGui::SliderFloat("Spectral Radius Max", &rs.luts.spectralRadiusMax, 0.0f, 50.0f);

              const double referenceMass = physics::M_SUN;
              const double referenceRs = physics::schwarzschildRadius(referenceMass);
              const double referenceRg = physics::G * referenceMass / physics::C2;
              const double referenceA = static_cast<double>(rs.physicsCore.kerrSpin) * referenceRg;
              const bool progradeSpin = rs.physicsCore.kerrSpin >= 0.0f;
              const double iscoRatio =
                  physics::kerrIscoRadius(referenceMass, referenceA, progradeSpin) / referenceRs;
              const double photonRatio =
                  (progradeSpin ? physics::kerrPhotonOrbitPrograde
                                : physics::kerrPhotonOrbitRetrograde)(referenceMass, referenceA) /
                  referenceRs;

              float const schwarzschildRadius = 2.0f * rs.physicsCore.blackHoleMass;
              float const photonSphereRadius =
                  static_cast<float>(photonRatio) * schwarzschildRadius;
              float const iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
              ImGui::Text("r_s = %.2f, r_ph = %.2f, r_ISCO = %.2f",
                          static_cast<double>(schwarzschildRadius),
                          static_cast<double>(photonSphereRadius), static_cast<double>(iscoRadius));

              ImGui::EndTabItem();
            }
            if (ImGui::BeginTabItem("Compute")) {
              ImGui::Text("Compute Raytracer");
              bool const computeAvailable = ShaderManager::instance().canUseComputeShaders();
              if (!computeAvailable) {
                ImGui::TextDisabled("Compute shaders unavailable");
                rs.dispatch.useComputeRaytracer = false;
                rs.compare.compareComputeFragment = false;
              }
              if (kAppVariantCudaOnly) {
                rs.dispatch.useComputeRaytracer = false;
                rs.compare.compareComputeFragment = false;
                ImGui::TextDisabled("Compute/fragment comparison is disabled in BlackholeCUDA.");
              } else {
                ImGui::Checkbox("Use Compute Raytracer", &rs.dispatch.useComputeRaytracer);
              }
              if (rs.dispatch.useComputeRaytracer && !kAppVariantCudaOnly) {
                ImGui::SliderInt("Compute Steps", &rs.dispatch.computeMaxSteps, 50, 600);
                ImGui::SliderFloat("Compute Step Size", &rs.dispatch.computeStepSize, 0.01f, 1.0f);
                ImGui::Checkbox("Compute Tiled", &rs.dispatch.computeTiled);
                if (rs.dispatch.computeTiled) {
                  ImGui::SliderInt("Compute Tile Size", &rs.dispatch.computeTileSize, 64, 1024);
                }
              }
#if BLACKHOLE_HAS_CUDA
              ImGui::Separator();
              ImGui::Text("CUDA Backend");
              {
                bool cudaEnabled = rs.dispatch.cudaManager.isEnabled();
                if (ImGui::Checkbox("Use CUDA Raytracer", &cudaEnabled)) {
                  rs.dispatch.cudaManager.setEnabled(cudaEnabled);
                }
              }
              if (rs.dispatch.cudaManager.isEnabled()) {
                const char *const variantNames[] = {"FP32 Baseline",
                                                    "FP32 Coarsened (2 ray/thread)", "FP16 Storage",
                                                    "FP16 H2 ILP (2 ray/thread)", "Auto"};
                int variantUI = rs.dispatch.cudaManager.kernelVariant() < 0 ? 4 : rs.dispatch.cudaManager.kernelVariant();
                if (ImGui::Combo("Kernel Variant", &variantUI, variantNames, 5)) {
                  rs.dispatch.cudaManager.setKernelVariant((variantUI >= 4) ? -1 : variantUI);
                }
                if (rs.dispatch.cudaManager.isReady()) {
                  int const actual = rs.dispatch.cudaManager.activeVariant();
                  if (actual >= 0 && actual < BH_KERNEL_COUNT) {
                    ImGui::TextDisabled("Active: %s", variantNames[actual]);
                  }
                } else if (rs.dispatch.cudaManager.wasInitAttempted()) {
                  ImGui::TextColored(ImVec4(1.f, 0.4f, 0.4f, 1.f),
                                     "Init failed -- toggle checkbox to retry");
                } else {
                  ImGui::TextDisabled("Will init on next frame");
                }
              }
              ImGui::Separator();
#endif
              if (!kAppVariantCudaOnly) {
                ImGui::Checkbox("Compare Compute vs Fragment", &rs.compare.compareComputeFragment);
              }
              if (rs.compare.compareComputeFragment && !kAppVariantCudaOnly) {
                ImGui::SliderInt("Compare Sample Size", &rs.compare.compareSampleSize, 4, 64);
                ImGui::SliderInt("Compare Frame Stride", &rs.compare.compareFrameStride, 1, 60);
                if (rs.compare.compareStats.valid) {
                  ImGui::Text("Diff mean=%.6f max=%.6f", static_cast<double>(rs.compare.compareStats.meanAbs),
                              static_cast<double>(rs.compare.compareStats.maxAbs));
                } else {
                  ImGui::TextDisabled("Diff metrics unavailable");
                }
                if (rs.compare.compareFullStats.valid) {
                  ImGui::Text("Full diff mean=%.6f rms=%.6f max=%.6f",
                              static_cast<double>(rs.compare.compareFullStats.meanAbs),
                              static_cast<double>(rs.compare.compareFullStats.rms),
                              static_cast<double>(rs.compare.compareFullStats.maxAbs));
                }
                ImGui::Checkbox("Write Snapshot PPMs", &rs.compare.compareWriteOutputs);
                ImGui::Checkbox("Write Diff PPM", &rs.compare.compareWriteDiff);
                ImGui::Checkbox("Write Summary CSV", &rs.compare.compareWriteSummary);
                ImGui::SliderFloat("Diff Scale", &rs.compare.compareDiffScale, 0.1f, 32.0f);
                ImGui::SliderFloat("Max Diff Threshold", &rs.compare.compareThreshold, 0.0f, 0.5f);
                rs.compare.compareThreshold = std::max(rs.compare.compareThreshold, 0.0f);
                ImGui::SliderInt("Allowed Outliers", &rs.compare.compareMaxOutliers, 0, 50000);
                ImGui::SliderFloat("Allowed Outlier Frac", &rs.compare.compareMaxOutlierFrac, 0.0f, 0.01f,
                                   "%.5f");
                rs.compare.compareMaxOutlierFrac = std::max(rs.compare.compareMaxOutlierFrac, 0.0f);
                ImGui::Checkbox("Compare Baseline (disable extras)", &rs.compare.compareBaselineEnabled);
                if (ImGui::Checkbox("Compare Overrides", &rs.compare.compareOverridesEnabled)) {
                  if (rs.compare.compareOverridesEnabled) {
                    if (rs.compare.compareMaxStepsOverride <= 0) {
                      rs.compare.compareMaxStepsOverride = rs.dispatch.computeMaxSteps;
                    }
                    if (rs.compare.compareStepSizeOverride <= 0.0f) {
                      rs.compare.compareStepSizeOverride = rs.dispatch.computeStepSize;
                    }
                  }
                }
                ImGui::BeginDisabled(!rs.compare.compareOverridesEnabled);
                ImGui::SliderInt("Compare Max Steps Override", &rs.compare.compareMaxStepsOverride, 0, 1000);
                ImGui::SliderFloat("Compare Step Size Override", &rs.compare.compareStepSizeOverride, 0.0f,
                                   2.0f);
                ImGui::EndDisabled();
                ImGui::Separator();
                ImGui::Text("Integrator Debug");
                bool debugNan = (rs.compare.integratorDebugFlags & K_INTEGRATOR_DEBUG_NAN_FLAG) != 0;
                bool debugRange = (rs.compare.integratorDebugFlags & K_INTEGRATOR_DEBUG_RANGE_FLAG) != 0;
                ImGui::Checkbox("Flag NaN/Inf", &debugNan);
                ImGui::SameLine();
                ImGui::Checkbox("Flag Out-of-Range", &debugRange);
                rs.compare.integratorDebugFlags = (debugNan ? K_INTEGRATOR_DEBUG_NAN_FLAG : 0) |
                                       (debugRange ? K_INTEGRATOR_DEBUG_RANGE_FLAG : 0);
                ImGui::Text("Threshold failures: %d", rs.compare.compareFailureCount);
                if (rs.compare.compareFullStats.valid) {
                  ImGui::Text("Last capture: %s", rs.compare.compareLastExceeded ? "FAIL" : "PASS");
                  ImGui::Text("Outliers: %d (limit %d)", rs.compare.compareLastOutliers,
                              rs.compare.compareLastOutlierLimit);
                }
                if (ImGui::Checkbox("Auto Capture", &rs.compare.compareAutoCapture)) {
                  rs.compare.compareAutoRemaining = rs.compare.compareAutoCapture ? std::max(rs.compare.compareAutoCount, 1) : 0;
                  rs.compare.compareAutoStrideCounter = 0;
                }
                ImGui::SliderInt("Auto Capture Count", &rs.compare.compareAutoCount, 1, 120);
                ImGui::SliderInt("Auto Capture Stride", &rs.compare.compareAutoStride, 1, 600);
                if (rs.compare.compareAutoCapture) {
                  ImGui::Text("Auto remaining: %d", rs.compare.compareAutoRemaining);
                }
                if (ImGui::Button("Capture Preset Sweep")) {
                  rs.compare.comparePresetSweep = true;
                  rs.compare.comparePresetIndex = 0;
                  rs.compare.comparePresetFrameCounter = 0;
                  rs.compare.compareAutoCapture = false;
                  rs.compare.compareAutoRemaining = 0;
                  rs.compare.compareRestorePending = false;
                }
                ImGui::SliderInt("Preset Settle Frames", &rs.compare.comparePresetSettleFrames, 1, 10);
                if (rs.compare.comparePresetSweep) {
                  std::size_t const presetCount = K_COMPARE_PRESETS.size();
                  int const displayIndex =
                      std::clamp(rs.compare.comparePresetIndex + 1, 1, static_cast<int>(presetCount));
                  auto const labelIndex = static_cast<std::size_t>(displayIndex - 1);
                  const char *label = K_COMPARE_PRESETS.at(labelIndex).label;
                  ImGui::Text("Preset sweep: %s (%d/%d)", label, displayIndex,
                              static_cast<int>(presetCount));
                }
                if (ImGui::Button("Capture A/B Snapshot")) {
                  rs.compare.captureCompareSnapshot = true;
                }
              }
              ImGui::EndTabItem();
            }
            ImGui::EndTabBar();
          }
          ImGui::End();
        }

        if (rs.overlays.curveOverlayWindowOpen) {
          ImGui::Begin("Curve Overlay", &rs.overlays.curveOverlayWindowOpen);
          ImGui::Checkbox("Enabled", &rs.overlays.curveOverlayEnabled);
          if (ImGui::Button("Reload") && !curveTsvPath.empty()) {
            rs.overlays.curveOverlayLoaded = rs.overlays.curveOverlay.loadFromTsv(curveTsvPath);
          }
          if (!curveTsvPath.empty()) {
            ImGui::SameLine();
            ImGui::Text("%s", curveTsvPath.c_str());
          }

          if (curveTsvPath.empty()) {
            ImGui::Text("Pass --curve-tsv <path> to plot a 2-column TSV.");
          } else if (!rs.overlays.curveOverlayLoaded) {
            ImGui::Text("Load error: %s", rs.overlays.curveOverlay.lastError.c_str());
          } else if (rs.overlays.curveOverlayEnabled) {
            ImVec2 plotSize = ImGui::GetContentRegionAvail();
            plotSize.y = std::max(plotSize.y, 220.0f);
            drawCurvePlot(rs.overlays.curveOverlay, plotSize);
          }

          ImGui::End();
        }

        updateLuts(rs.physicsCore.kerrSpin, rs.disk.adiskDensityV);
        if (!rs.luts.spectralLutTried) {
          rs.luts.spectralLutTried = true;
          rs.luts.spectralLutLoaded = loadSpectralLutAssets(rs.luts.spectralLutValues, rs.luts.spectralWavelengthMin,
                                                    rs.luts.spectralWavelengthMax);
          if (rs.luts.spectralLutLoaded && !rs.luts.spectralLutValues.empty()) {
            if (rs.luts.texSpectralLUT != 0) {
              glDeleteTextures(1, &rs.luts.texSpectralLUT);
              rs.luts.texSpectralLUT = 0;
            }
            int const lutSize = static_cast<int>(rs.luts.spectralLutValues.size());
            rs.luts.texSpectralLUT = createFloatTexture2D(lutSize, 1, rs.luts.spectralLutValues);
#if BLACKHOLE_HAS_CUDA
            /* Share spectral LUT with CUDA backend (slot 2=spectral) */
            rs.dispatch.cudaManager.registerLut(2, rs.luts.texSpectralLUT, static_cast<unsigned int>(GL_TEXTURE_2D));
#endif
            rs.luts.spectralRadiusMin = rs.luts.lutRadiusMin;
            rs.luts.spectralRadiusMax = rs.luts.lutRadiusMax;
            if (rs.luts.spectralRadiusMax <= rs.luts.spectralRadiusMin) {
              rs.luts.spectralRadiusMin = 0.0f;
              rs.luts.spectralRadiusMax = 1.0f;
            }
          }
        }

        /* Generate synchrotron G(x)=x*K_{2/3}(x) LUT once (task E5).
         * Stored as GL_TEXTURE_2D (width=256, height=1) so the same handle
         * can be registered for CUDA-GL interop via cudaGraphicsGLRegisterImage,
         * which does not support GL_TEXTURE_1D.  The GLSL path samples it
         * via sampler2D with y=0.5; the CUDA path uses tex2D at v=0.5. */
        if (!rs.luts.synchGLutCreated) {
          // The G(x) domain is single-sourced across C++, CUDA, and GLSL via
          // shader/include/synchrotron_lut_domain.h; every consumer reads the
          // same macros, so no cross-file pinning asserts are needed here.
          rs.luts.synchGLutCreated = true;
          constexpr int kSynchGLutSize = SYNCH_G_LUT_DOMAIN_ENTRIES;
          std::vector<float> synchGData(static_cast<std::size_t>(kSynchGLutSize));
          physics::synchrotronGGenerateLut(synchGData.data(), kSynchGLutSize,
                                           static_cast<double>(physics::SYNCH_G_LUT_X_MIN),
                                           static_cast<double>(physics::SYNCH_G_LUT_X_MAX));
          if (rs.luts.texSynchGLut != 0) {
            glDeleteTextures(1, &rs.luts.texSynchGLut);
            rs.luts.texSynchGLut = 0;
          }
          rs.luts.texSynchGLut = createFloatTexture2D(kSynchGLutSize, 1, synchGData);
#if BLACKHOLE_HAS_CUDA
          rs.dispatch.cudaManager.registerLut(6 /*BhLutSynchG*/, rs.luts.texSynchGLut,
                                  static_cast<unsigned int>(GL_TEXTURE_2D));
#endif
        }

        // Load Hawking radiation LUTs
        if (!rs.hawking.hawkingLutsLoaded) {
          std::filesystem::path const lutPath = resourcePath("assets/luts");
          if (std::filesystem::exists(lutPath)) {
            rs.hawking.hawkingLutsLoaded = rs.hawking.hawkingRenderer.loadLUTs(lutPath);
            if (rs.hawking.hawkingLutsLoaded) {
              std::cout << "Hawking radiation LUTs loaded successfully" << '\n';
            } else {
              std::cerr << "Failed to load Hawking radiation LUTs" << '\n';
            }
          }
        }

        const double referenceMass = physics::M_SUN;
        const double referenceRs = physics::schwarzschildRadius(referenceMass);
        const double referenceRg = physics::G * referenceMass / physics::C2;
        const double referenceA = static_cast<double>(rs.physicsCore.kerrSpin) * referenceRg;
        const bool progradeSpin = rs.physicsCore.kerrSpin >= 0.0f;
        const double iscoRatio =
            physics::kerrIscoRadius(referenceMass, referenceA, progradeSpin) / referenceRs;

        float const schwarzschildRadius = 2.0f * rs.physicsCore.blackHoleMass;
        float const iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
        // Keep record-mode copies accessible outside this inner block
        rs.recording.recordCurRs   = schwarzschildRadius;
        rs.recording.recordCurIsco = iscoRadius;
#if BLACKHOLE_HAS_CUDA
        if (kAppVariantCudaOnly) {
          rs.dispatch.cudaManager.setEnabled(true);
          rs.dispatch.useComputeRaytracer = false;
          rs.compare.compareComputeFragment = false;
        }
#endif
        bool const computeSupported = ShaderManager::instance().canUseComputeShaders();
        bool const computeActive = rs.dispatch.useComputeRaytracer && computeSupported;
        bool const compareActive =
            rs.compare.compareComputeFragment && computeSupported && !kAppVariantCudaOnly;
        bool const compareBaselineActive = rs.compare.compareBaselineEnabled && compareActive;
        bool const adiskEnabledEffective = rs.disk.adiskEnabled && !compareBaselineActive;
        bool const adiskParticleEffective = rs.disk.adiskParticle && !compareBaselineActive;
        bool const enableRedshiftEffective = rs.physicsCore.enableRedshift && !compareBaselineActive;
        bool const useNoiseTextureEffective = rs.disk.useNoiseTexture && !compareBaselineActive;
        bool const useGrmhdEffective = rs.grmhd.useGrmhd && !compareBaselineActive;
        bool const useSpectralLutEffective = rs.luts.useSpectralLut && !compareBaselineActive;
        bool const useGrbModulationEffective = rs.luts.useGrbModulation && !compareBaselineActive;
        bool const enablePhotonSphereEffective = rs.physicsCore.enablePhotonSphere && !compareBaselineActive;
        bool const backgroundEnabledEffective =
            settings.backgroundEnabled && !compareBaselineActive;
        computeActiveForLog = computeActive;
        rs.compare.compareSampleSize = std::clamp(rs.compare.compareSampleSize, 4, 64);
        rs.compare.compareFrameStride = std::max(rs.compare.compareFrameStride, 1);
        rs.compare.compareAutoCount = std::max(rs.compare.compareAutoCount, 1);
        rs.compare.compareAutoStride = std::max(rs.compare.compareAutoStride, 1);
        if (!compareActive) {
          rs.compare.compareAutoCapture = false;
          rs.compare.compareAutoRemaining = 0;
          rs.compare.compareAutoStrideCounter = 0;
        }
        rs.dispatch.computeMaxSteps = std::clamp(rs.dispatch.computeMaxSteps, 10, 1000);
        rs.dispatch.computeStepSize = std::clamp(rs.dispatch.computeStepSize, 0.001f, 2.0f);
        int compareSteps = rs.dispatch.computeMaxSteps;
        float compareStepSize = rs.dispatch.computeStepSize;
        if (rs.compare.compareOverridesEnabled) {
          if (rs.compare.compareMaxStepsOverride > 0) {
            compareSteps = rs.compare.compareMaxStepsOverride;
          }
          if (rs.compare.compareStepSizeOverride > 0.0f) {
            compareStepSize = rs.compare.compareStepSizeOverride;
          }
        }

        grmhdEnabled = useGrmhdEffective && grmhdReady;
        spectralEnabled = useSpectralLutEffective && spectralReady;
        grbModulationEnabled = useGrbModulationEffective && grbModulationReady;
        noiseReady = useNoiseTextureEffective && rs.disk.texNoiseVolume != 0;
        rtti.texture3DUniforms["noiseTexture"] = noiseReady ? rs.disk.texNoiseVolume : rs.background.fallback3D;
        rtti.texture3DUniforms["grmhdTexture"] = grmhdEnabled ? grmhdTexId : rs.background.fallback3D;
        rtti.textureUniforms["spectralLUT"] = spectralEnabled ? rs.luts.texSpectralLUT : rs.background.fallback2D;
        rtti.textureUniforms["grbModulationLUT"] =
            grbModulationEnabled ? rs.luts.texGrbModulationLUT : rs.background.fallback2D;
        rtti.textureUniforms["hawkingTempLUT"] =
            rs.hawking.hawkingLutsLoaded ? rs.hawking.hawkingRenderer.getTempLUTTexture() : rs.background.fallback2D;
        rtti.textureUniforms["hawkingSpectrumLUT"] =
            rs.hawking.hawkingLutsLoaded ? rs.hawking.hawkingRenderer.getSpectrumLUTTexture() : rs.background.fallback2D;
        rtti.floatUniforms["useNoiseTexture"] = noiseReady ? 1.0f : 0.0f;
        rtti.floatUniforms["useGrmhd"] = grmhdEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["backgroundEnabled"] = backgroundEnabledEffective ? 1.0f : 0.0f;
        rtti.floatUniforms["bhDebugFlags"] = static_cast<float>(rs.compare.integratorDebugFlags);

        InteropUniforms interop;
        interop.cameraPos = cameraPos;
        interop.cameraBasis = cameraBasis;
        interop.fovScale = fovScale;
        interop.timeSec = frameTime;
        interop.schwarzschildRadius = schwarzschildRadius;
        interop.iscoRadius = iscoRadius;
        interop.kerrSpin = rs.physicsCore.kerrSpin;
        interop.depthFar = rs.display.depthFar;
        if (compareActive) {
          interop.maxSteps = compareSteps;
          interop.stepSize = compareStepSize;
        } else {
          interop.maxSteps = rs.dispatch.computeMaxSteps;
          interop.stepSize = rs.dispatch.computeStepSize;
        }
        interop.adiskEnabled = adiskEnabledEffective ? 1.0f : 0.0f;
        interop.enableRedshift = enableRedshiftEffective ? 1.0f : 0.0f;
        interop.useLUTs = lutReady ? 1.0f : 0.0f;
        interop.useSpectralLUT = spectralEnabled ? 1.0f : 0.0f;
        interop.useGrbModulation = grbModulationEnabled ? 1.0f : 0.0f;
        interop.lutRadiusMin = rs.luts.lutRadiusMin;
        interop.lutRadiusMax = rs.luts.lutRadiusMax;
        interop.redshiftRadiusMin = rs.luts.redshiftRadiusMin;
        interop.redshiftRadiusMax = rs.luts.redshiftRadiusMax;
        interop.spectralRadiusMin = rs.luts.spectralRadiusMin;
        interop.spectralRadiusMax = rs.luts.spectralRadiusMax;
        interop.grbTime = grbTimeSeconds;
        interop.grbTimeMin = rs.luts.grbTimeMin;
        interop.grbTimeMax = rs.luts.grbTimeMax;
        // D2: volumetric RTE
        interop.rteEnabled      = rs.rte.rteVolumetricEnabled ? 1.0f : 0.0f;
        interop.rteOpacityScale = rs.rte.rteOpacityScale;
        interop.debugPreRedshiftBackground = rs.debug.debugPreRedshiftBackground ? 1.0f : 0.0f;
        interop.debugPreShapingBackground = rs.debug.debugPreShapingBackground ? 1.0f : 0.0f;
        interop.debugPostShapingBackground = rs.debug.debugPostShapingBackground ? 1.0f : 0.0f;
        interop.debugShaperInputs = rs.debug.debugShaperInputs ? 1.0f : 0.0f;
        interop.debugClosestApproachState = rs.debug.debugClosestApproachState ? 1.0f : 0.0f;
        interop.debugClosestApproachTimeline = rs.debug.debugClosestApproachTimeline ? 1.0f : 0.0f;
        interop.debugClosestApproachDirection = rs.debug.debugClosestApproachDirection ? 1.0f : 0.0f;
        interop.debugEscapedDirection = rs.debug.debugEscapedDirection ? 1.0f : 0.0f;

        // Convert black hole mass to grams (CGS units for Hawking calculation)
        double const bhMassGrams = static_cast<double>(rs.physicsCore.blackHoleMass) * physics::M_SUN;
        applyInteropUniforms(rtti, interop, compareActive, rs.hawking.hawkingGlowEnabled, rs.hawking.hawkingTempScale,
                             rs.hawking.hawkingGlowIntensity, rs.hawking.hawkingUseLUTs, bhMassGrams);

        rtti.floatUniforms["wiregridEnabled"]   = rs.wiregrid.wiregridEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["wiregridShowErgo"]  = rs.wiregrid.wiregridParams.showErgosphere ? 1.0f : 0.0f;
        rtti.floatUniforms["wiregridGridScale"] = rs.wiregrid.wiregridParams.gridScale;
        rtti.floatUniforms["wiregridMotionScale"] = rs.wiregrid.wiregridParams.motionScale;
        rtti.floatUniforms["wiregridInfallScale"] = rs.wiregrid.wiregridParams.infallScale;
        rtti.floatUniforms["wiregridStrength"] = rs.wiregrid.wiregridParams.strength;
        rtti.floatUniforms["wiregridScenePreserve"] = rs.wiregrid.wiregridParams.scenePreserve;
        rtti.vec4Uniforms["wiregridColor"] = rs.wiregrid.wiregridColor;
        // D4: polarized Stokes IQUV
        rtti.floatUniforms["stokesEnabled"]     = rs.stokes.stokesEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["stokesBFieldAngle"] = rs.stokes.stokesBFieldAngle;
        rtti.floatUniforms["stokesNeScale"]     = rs.stokes.stokesNeScale;
        rtti.floatUniforms["gravitationalLensing"] = rs.disk.gravitationalLensing ? 1.0f : 0.0f;
        rtti.floatUniforms["renderBlackHole"] = rs.disk.renderBlackHole ? 1.0f : 0.0f;
        rtti.floatUniforms["adiskParticle"] = adiskParticleEffective ? 1.0f : 0.0f;
        // rtti.floatUniforms["adiskDensityV"] = adiskDensityV; // Removed: consumed by LUT
        // generation
        rtti.floatUniforms["adiskDensityH"] = rs.disk.adiskDensityH;
        rtti.floatUniforms["adiskHeight"] = rs.disk.adiskHeight;
        rtti.floatUniforms["adiskLit"] = rs.disk.adiskLit;
        rtti.floatUniforms["adiskNoiseLOD"] = rs.disk.adiskNoiseLOD;
        rtti.floatUniforms["adiskNoiseScale"] = rs.disk.adiskNoiseScale;
        rtti.floatUniforms["adiskSpeed"] = rs.disk.adiskSpeed;
        rtti.floatUniforms["dopplerStrength"] = rs.disk.dopplerStrength;
        rtti.floatUniforms["photonSphereGlowStrength"] = rs.disk.photonSphereGlowStrength;
        rtti.floatUniforms["enablePhotonSphere"] = enablePhotonSphereEffective ? 1.0f : 0.0f;

#if BLACKHOLE_HAS_CUDA
        /* CUDA dispatch path: bypasses both fragment and compute GLSL paths */
        if (rs.dispatch.cudaManager.isEnabled()) {
          ZONE_SCOPED_N("Blackhole CUDA");

          /* Lazy init on first use or after resize.
           * Track pre-call state to detect the single frame where init succeeds. */
          bool const wasReady = rs.dispatch.cudaManager.isReady();
          rs.dispatch.cudaManager.ensureInit(rs.targets.texBlackhole, rs.targets.renderWidth, rs.targets.renderHeight);
          if (!wasReady && rs.dispatch.cudaManager.isReady()) {
            /* Register rs.background.galaxy cubemap as CUDA texture object (slot 4 = BhLutGalaxy).
             * Done exactly once on the frame that init first succeeds.
             * Registration failure is non-fatal: kernels fall back to no background. */
            GLuint const galaxyTexForCuda = (rs.background.galaxy != 0) ? rs.background.galaxy : rs.background.fallbackCubemap;
            if (galaxyTexForCuda != 0) {
              rs.dispatch.cudaManager.registerLut(4, galaxyTexForCuda,
                                      static_cast<unsigned int>(GL_TEXTURE_CUBE_MAP));
            }
            /* Register the layered desktop background equirect texture so the CUDA
             * lane samples the same 2D scene asset class as the GLSL desktop lane. */
            GLuint const backgroundTexForCuda = (rs.background.backgroundBase != 0) ? rs.background.backgroundBase : rs.background.fallback2D;
            if (backgroundTexForCuda != 0) {
              bhCudaRegisterBackgroundTexture(rs.dispatch.cudaManager.backend(), backgroundTexForCuda,
                                              static_cast<unsigned int>(GL_TEXTURE_2D));
            }
          }

          if (rs.dispatch.cudaManager.isReady()) {
            BH_LaunchParams cp = {};
            cp.rs = interop.schwarzschildRadius;
            cp.spin = interop.kerrSpin;
            cp.isco = interop.iscoRadius;
            cp.step_size = interop.stepSize;
            cp.fov_scale = interop.fovScale;
            cp.max_dist = interop.depthFar;
            cp.cam_pos[0] = interop.cameraPos.x;
            cp.cam_pos[1] = interop.cameraPos.y;
            cp.cam_pos[2] = interop.cameraPos.z;
            /* glm mat3 is column-major, same layout as our flat array */
            std::memcpy(cp.cam_basis, glm::value_ptr(interop.cameraBasis), 9 * sizeof(float));
            cp.max_steps = interop.maxSteps;
            cp.width = rs.targets.renderWidth;
            cp.height = rs.targets.renderHeight;
            cp.adisk_enabled = adiskEnabledEffective ? 1 : 0;
            cp.redshift_enabled = enableRedshiftEffective ? 1 : 0;
            cp.kerr_enabled = (fabsf(interop.kerrSpin) > 1e-6f) ? 1 : 0;
            cp.use_luts = (interop.useLUTs > 0.5f) ? 1 : 0;
            cp.lut_radius_min = interop.lutRadiusMin;
            cp.lut_radius_max = interop.lutRadiusMax;
            cp.redshift_radius_min = interop.redshiftRadiusMin;
            cp.redshift_radius_max = interop.redshiftRadiusMax;
            cp.spectral_radius_min = interop.spectralRadiusMin;
            cp.spectral_radius_max = interop.spectralRadiusMax;
            cp.time_sec = interop.timeSec;
            cp.doppler_strength = rs.disk.dopplerStrength;
            cp.background_intensity = settings.backgroundIntensity;
            cp.background_enabled = backgroundEnabledEffective ? 1 : 0;
            cp.photon_glow_strength = enablePhotonSphereEffective ? rs.disk.photonSphereGlowStrength : 0.0f;
            cp.debug_pre_redshift_background = rs.debug.debugPreRedshiftBackground ? 1 : 0;
            cp.debug_pre_shaping_background = rs.debug.debugPreShapingBackground ? 1 : 0;
            cp.debug_post_shaping_background = rs.debug.debugPostShapingBackground ? 1 : 0;
            cp.debug_shaper_inputs = rs.debug.debugShaperInputs ? 1 : 0;
            cp.debug_closest_approach_state = rs.debug.debugClosestApproachState ? 1 : 0;
            cp.debug_closest_approach_timeline = rs.debug.debugClosestApproachTimeline ? 1 : 0;
            cp.debug_closest_approach_direction = rs.debug.debugClosestApproachDirection ? 1 : 0;
            cp.debug_escaped_direction = rs.debug.debugEscapedDirection ? 1 : 0;
            cp.background_yaw_rad = rs.background.backgroundYawRad;
            cp.background_pitch_rad = rs.background.backgroundPitchRad;
            cp.background_filter_radius = 0.0f;
            if (!recordFramesDir.empty() && recordProfile == "showcase-orbit") {
              const ShowcaseOrbitComposition *const composition =
                  findShowcaseOrbitComposition(recordComposition);
              cp.frame_shift_x =
                  hasRecordFrameX ? recordFrameX
                                  : (composition != nullptr ? composition->frameOffsetX : 0.0f);
              cp.frame_shift_y =
                  hasRecordFrameY ? recordFrameY
                                  : (composition != nullptr ? composition->frameOffsetY : 0.0f);
            } else {
              cp.frame_shift_x = 0.0f;
              cp.frame_shift_y = 0.0f;
            }
            for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
              auto const &params = rs.background.backgroundLayerParams.at(static_cast<std::size_t>(i));
              cp.background_layer_params[i * 4 + 0] = params.x;
              cp.background_layer_params[i * 4 + 1] = params.y;
              cp.background_layer_params[i * 4 + 2] = params.z;
              cp.background_layer_params[i * 4 + 3] = params.w;
              cp.background_layer_lod_bias[i] =
                  std::max(rs.background.backgroundLayerLodBias.at(static_cast<std::size_t>(i)), 0.0f);
            }
            // Wiregrid BL-coord overlay (task A4)
            cp.wiregrid_enabled    = rs.wiregrid.wiregridEnabled ? 1 : 0;
            cp.wiregrid_show_ergo  = rs.wiregrid.wiregridParams.showErgosphere ? 1.0f : 0.0f;
            cp.wiregrid_grid_scale = rs.wiregrid.wiregridParams.gridScale;
            cp.wiregrid_motion_scale = rs.wiregrid.wiregridParams.motionScale;
            cp.wiregrid_infall_scale = rs.wiregrid.wiregridParams.infallScale;
            cp.wiregrid_strength = rs.wiregrid.wiregridParams.strength;
            cp.wiregrid_scene_preserve = rs.wiregrid.wiregridParams.scenePreserve;
            cp.wiregrid_color[0] = rs.wiregrid.wiregridColor.r;
            cp.wiregrid_color[1] = rs.wiregrid.wiregridColor.g;
            cp.wiregrid_color[2] = rs.wiregrid.wiregridColor.b;
            cp.wiregrid_color[3] = rs.wiregrid.wiregridColor.a;
            // GRMHD volume radial bounds (task C1l) + temporal blend (C1d)
            cp.grmhd_r_min  = rs.grmhd.grmhdTexture.rMin;
            cp.grmhd_r_max  = rs.grmhd.grmhdTexture.rMax;
            cp.grmhd_alpha  = rs.grmhd.grmhdFrameAlpha;
            // Volumetric RTE (D3): mirrors GLSL rteEnabled path
            cp.rte_enabled       = (interop.rteEnabled > 0.5f) ? 1 : 0;
            cp.rte_opacity_scale = interop.rteOpacityScale;
            // D4: polarized Stokes IQUV
            cp.stokes_enabled     = rs.stokes.stokesEnabled ? 1 : 0;
            cp.stokes_b_field_angle = rs.stokes.stokesBFieldAngle;
            cp.stokes_ne_scale    = rs.stokes.stokesNeScale;
            // Disk brightness: matches adiskLit GLSL uniform (record mode sets 0.35)
            cp.adisk_lit = rs.disk.adiskLit;

            rs.dispatch.cudaManager.renderFrame(&cp);
          }
        } else
#endif
        {
          /* Original GLSL fragment/compute paths */

          GLuint fragmentTarget = 0;
          if (computeActive) {
            fragmentTarget = compareActive ? rs.targets.texBlackholeCompare : 0;
          } else {
            fragmentTarget = rs.targets.texBlackhole;
          }
          GLuint computeTarget = 0;
          if (computeActive) {
            computeTarget = rs.targets.texBlackhole;
          } else {
            computeTarget = compareActive ? rs.targets.texBlackholeCompare : 0;
          }
          if (rs.timing.gpuTimers.initialized && fragmentTarget != 0) {
            rs.timing.gpuTimers.blackholeFragment.begin();
          }
          if (fragmentTarget != 0) {
            ZONE_SCOPED_N("Blackhole Fragment");
            rtti.targetTexture = fragmentTarget;
            // std::cout << "Rendering to texture..." << std::endl;
            renderToTexture(rtti);
          }
          if (rs.timing.gpuTimers.initialized && fragmentTarget != 0) {
            rs.timing.gpuTimers.blackholeFragment.end();
          }

          if (rs.timing.gpuTimers.initialized && computeTarget != 0) {
            rs.timing.gpuTimers.blackholeCompute.begin();
          }
          if (computeTarget != 0) {
            ZONE_SCOPED_N("Blackhole Compute");
            if (computeProgram == 0) {
              computeProgram = createComputeProgram(std::string("shader/geodesic_trace.comp"));
            }

            glUseProgram(computeProgram);
            applyInteropComputeUniforms(computeProgram, interop, rs.targets.renderWidth, rs.targets.renderHeight);

            // Apply Hawking radiation uniforms
            double const bhMass = static_cast<double>(rs.physicsCore.blackHoleMass) * physics::M_SUN;
            applyHawkingUniforms(computeProgram, rs.hawking.hawkingRenderer, rs.hawking.hawkingGlowEnabled,
                                 rs.hawking.hawkingTempScale, rs.hawking.hawkingGlowIntensity, rs.hawking.hawkingUseLUTs, bhMass);

            // Wiregrid BL-coord overlay (parity with fragment path)
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridEnabled"),
                        rs.wiregrid.wiregridEnabled ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridShowErgo"),
                        rs.wiregrid.wiregridParams.showErgosphere ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridGridScale"),
                        rs.wiregrid.wiregridParams.gridScale);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridMotionScale"),
                        rs.wiregrid.wiregridParams.motionScale);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridInfallScale"),
                        rs.wiregrid.wiregridParams.infallScale);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridStrength"),
                        rs.wiregrid.wiregridParams.strength);
            glUniform1f(glGetUniformLocation(computeProgram, "wiregridScenePreserve"),
                        rs.wiregrid.wiregridParams.scenePreserve);
            glUniform4f(glGetUniformLocation(computeProgram, "wiregridColor"),
                        rs.wiregrid.wiregridColor.r, rs.wiregrid.wiregridColor.g, rs.wiregrid.wiregridColor.b, rs.wiregrid.wiregridColor.a);

            // D4: polarized Stokes IQUV (parity with fragment path)
            glUniform1f(glGetUniformLocation(computeProgram, "stokesEnabled"),
                        rs.stokes.stokesEnabled ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "stokesBFieldAngle"),
                        rs.stokes.stokesBFieldAngle);
            glUniform1f(glGetUniformLocation(computeProgram, "stokesNeScale"),
                        rs.stokes.stokesNeScale);

            GLint texUnit = 0;
            glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
            glBindTexture(GL_TEXTURE_2D, lutReady ? rs.luts.texEmissivityLUT : rs.background.fallback2D);
            glUniform1i(glGetUniformLocation(computeProgram, "emissivityLUT"), texUnit);
            texUnit++;
            glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
            glBindTexture(GL_TEXTURE_2D, lutReady ? rs.luts.texRedshiftLUT : rs.background.fallback2D);
            glUniform1i(glGetUniformLocation(computeProgram, "redshiftLUT"), texUnit);
            texUnit++;
            glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
            glBindTexture(GL_TEXTURE_2D, spectralEnabled ? rs.luts.texSpectralLUT : rs.background.fallback2D);
            glUniform1i(glGetUniformLocation(computeProgram, "spectralLUT"), texUnit);
            texUnit++;
            glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
            glBindTexture(GL_TEXTURE_2D, grbModulationEnabled ? rs.luts.texGrbModulationLUT : rs.background.fallback2D);
            glUniform1i(glGetUniformLocation(computeProgram, "grbModulationLUT"), texUnit);
            texUnit++;
            glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
            glBindTexture(GL_TEXTURE_CUBE_MAP, rs.background.galaxy != 0 ? rs.background.galaxy : rs.background.fallbackCubemap);
            glUniform1i(glGetUniformLocation(computeProgram, "galaxy"), texUnit);
            texUnit++;
            for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
              glActiveTexture(GL_TEXTURE0 + static_cast<unsigned>(texUnit));
              glBindTexture(GL_TEXTURE_2D, rs.background.backgroundTextures.at(static_cast<std::size_t>(i)));
              std::string const name = "backgroundLayers[" + std::to_string(i) + "]";
              glUniform1i(glGetUniformLocation(computeProgram, name.c_str()), texUnit);
              texUnit++;
            }
            glUniform1f(glGetUniformLocation(computeProgram, "backgroundEnabled"),
                        backgroundEnabledEffective ? 1.0f : 0.0f);
            glUniform1f(glGetUniformLocation(computeProgram, "bhDebugFlags"),
                        static_cast<float>(rs.compare.integratorDebugFlags));
            glUniform1f(glGetUniformLocation(computeProgram, "backgroundIntensity"),
                        settings.backgroundIntensity);
            for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
              std::string const name = "backgroundLayerParams[" + std::to_string(i) + "]";
              const auto &params = rs.background.backgroundLayerParams.at(static_cast<std::size_t>(i));
              glUniform4f(glGetUniformLocation(computeProgram, name.c_str()), params.x, params.y,
                          params.z, params.w);
            }
            for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
              std::string const name = "backgroundLayerLodBias[" + std::to_string(i) + "]";
              float const bias =
                  std::max(rs.background.backgroundLayerLodBias.at(static_cast<std::size_t>(i)), 0.0f);
              glUniform1f(glGetUniformLocation(computeProgram, name.c_str()), bias);
            }

            glBindImageTexture(0, computeTarget, 0, GL_FALSE, 0, GL_WRITE_ONLY, GL_RGBA32F);
            GLint const tileOffsetLoc = glGetUniformLocation(computeProgram, "tileOffset");
            constexpr int kGroupSize = 16;
            if (rs.dispatch.computeTiled) {
              rs.dispatch.computeTileSize = std::clamp(rs.dispatch.computeTileSize, kGroupSize, 2048);
              for (int y = 0; y < rs.targets.renderHeight; y += rs.dispatch.computeTileSize) {
                for (int x = 0; x < rs.targets.renderWidth; x += rs.dispatch.computeTileSize) {
                  int const tileWidth = std::min(rs.dispatch.computeTileSize, rs.targets.renderWidth - x);
                  int const tileHeight = std::min(rs.dispatch.computeTileSize, rs.targets.renderHeight - y);
                  if (tileOffsetLoc != -1) {
                    glUniform2i(tileOffsetLoc, x, y);
                  }
                  auto const groupsX =
                      static_cast<GLuint>((tileWidth + kGroupSize - 1) / kGroupSize);
                  auto const groupsY =
                      static_cast<GLuint>((tileHeight + kGroupSize - 1) / kGroupSize);
                  glDispatchCompute(groupsX, groupsY, 1);
                  glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
                }
              }
            } else {
              if (tileOffsetLoc != -1) {
                glUniform2i(tileOffsetLoc, 0, 0);
              }
              auto const groupsX = static_cast<GLuint>((rs.targets.renderWidth + kGroupSize - 1) / kGroupSize);
              auto const groupsY =
                  static_cast<GLuint>((rs.targets.renderHeight + kGroupSize - 1) / kGroupSize);
              glDispatchCompute(groupsX, groupsY, 1);
              glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
            }
            glUseProgram(0);
          }
          if (rs.timing.gpuTimers.initialized && computeTarget != 0) {
            rs.timing.gpuTimers.blackholeCompute.end();
          }

          if (compareActive && fragmentTarget != 0 && computeTarget != 0) {
            if (rs.compare.compareAutoCapture && rs.compare.compareAutoRemaining > 0) {
              rs.compare.compareAutoStrideCounter++;
              if (rs.compare.compareAutoStrideCounter >= rs.compare.compareAutoStride) {
                rs.compare.captureCompareSnapshot = true;
                rs.compare.compareAutoStrideCounter = 0;
                rs.compare.compareAutoRemaining--;
                if (rs.compare.compareAutoRemaining <= 0) {
                  rs.compare.compareAutoCapture = false;
                }
              }
            }

            if (++rs.compare.compareFrameCounter >= rs.compare.compareFrameStride) {
              rs.compare.compareStats =
                  sampleTextureDiff(rs.targets.texBlackhole, rs.targets.texBlackholeCompare, rs.targets.renderWidth,
                                    rs.targets.renderHeight, // NOLINT(readability-suspicious-call-argument) --
                                                  // order is correct: primary then compare
                                    rs.compare.compareSampleSize);
              rs.compare.compareFrameCounter = 0;
            }

            if (rs.compare.captureCompareSnapshot) {
              std::vector<float> primary;
              std::vector<float> secondary;
              if (readTextureRGBA(rs.targets.texBlackhole, rs.targets.renderWidth, rs.targets.renderHeight, primary) &&
                  readTextureRGBA(rs.targets.texBlackholeCompare, rs.targets.renderWidth, rs.targets.renderHeight, secondary)) {
                rs.compare.compareFullStats = computeDiffStats(primary, secondary);
                std::size_t const outlierCount =
                    countDiffOutliers(primary, secondary, rs.compare.compareThreshold);
                std::size_t const totalPixels = primary.size() / 4;
                std::size_t limitFromFrac = 0;
                if (rs.compare.compareMaxOutlierFrac > 0.0f && totalPixels > 0) {
                  limitFromFrac =
                      static_cast<std::size_t>(static_cast<double>(rs.compare.compareMaxOutlierFrac) *
                                               static_cast<double>(totalPixels));
                }
                std::size_t const limitFromCount =
                    static_cast<std::size_t>(std::max(rs.compare.compareMaxOutliers, 0));
                std::size_t const outlierLimit = std::max(limitFromCount, limitFromFrac);
                rs.compare.compareLastOutliers = static_cast<int>(outlierCount);
                rs.compare.compareLastOutlierLimit = static_cast<int>(outlierLimit);
                float const outlierFrac = totalPixels > 0 ? static_cast<float>(outlierCount) /
                                                                static_cast<float>(totalPixels)
                                                          : 0.0f;
                bool const outlierGateEnabled =
                    (rs.compare.compareMaxOutliers > 0) || (rs.compare.compareMaxOutlierFrac > 0.0f);
                rs.compare.compareLastExceeded = rs.compare.compareFullStats.valid &&
                                      rs.compare.compareFullStats.maxAbs > rs.compare.compareThreshold &&
                                      (!outlierGateEnabled || outlierCount > outlierLimit);
                if (rs.compare.compareLastExceeded) {
                  ++rs.compare.compareFailureCount;
                }

                const bool computeIsPrimary = (computeTarget == rs.targets.texBlackhole);
                const std::string primaryTag = computeIsPrimary ? "compute" : "fragment";
                const std::string secondaryTag = computeIsPrimary ? "fragment" : "compute";
                std::string presetLabel = "custom";
                if (rs.compare.compareSnapshotIndex >= 0 &&
                    std::cmp_less(rs.compare.compareSnapshotIndex, K_COMPARE_PRESETS.size())) {
                  presetLabel =
                      K_COMPARE_PRESETS.at(static_cast<std::size_t>(rs.compare.compareSnapshotIndex)).label;
                }

                if (rs.compare.compareWriteOutputs) {
                  writePpm(compareSnapshotPath(rs.compare.compareSnapshotIndex, primaryTag), primary,
                           rs.targets.renderWidth, rs.targets.renderHeight, 1.0f);
                  writePpm(compareSnapshotPath(rs.compare.compareSnapshotIndex, secondaryTag), secondary,
                           rs.targets.renderWidth, rs.targets.renderHeight, 1.0f);
                }
                if (rs.compare.compareWriteDiff) {
                  writeDiffPpm(compareSnapshotPath(rs.compare.compareSnapshotIndex, "diff"), primary,
                               secondary, rs.targets.renderWidth, rs.targets.renderHeight, rs.compare.compareDiffScale);
                }
                if (rs.compare.compareWriteSummary) {
                  appendCompareSummary(compareSummaryPath(), rs.compare.compareSnapshotIndex, primaryTag,
                                       secondaryTag, rs.targets.renderWidth, rs.targets.renderHeight, rs.compare.compareFullStats,
                                       rs.compare.compareDiffScale, rs.compare.compareWriteOutputs, rs.compare.compareWriteDiff,
                                       rs.compare.compareThreshold, rs.compare.compareLastExceeded, glfwGetTime(),
                                       rs.physicsCore.kerrSpin, grbModulationEnabled, grbTimeSeconds,
                                       rs.compare.compareLastOutliers, rs.compare.compareLastOutlierLimit, outlierFrac);
                  appendCompareUniforms(compareUniformsPath(), rs.compare.compareSnapshotIndex, presetLabel,
                                        interop, compareBaselineActive, rs.compare.compareOverridesEnabled,
                                        backgroundEnabledEffective, noiseReady, grmhdEnabled,
                                        spectralEnabled, grbModulationEnabled,
                                        enablePhotonSphereEffective);
                }
                rs.compare.compareSnapshotIndex++;
              } else {
                rs.compare.compareFullStats.valid = false;
                rs.compare.compareLastExceeded = false;
              }
              rs.compare.captureCompareSnapshot = false;
            }
          } else {
            rs.compare.compareStats.valid = false;
            rs.compare.compareFullStats.valid = false;
            rs.compare.captureCompareSnapshot = false;
            rs.compare.compareLastExceeded = false;
            rs.compare.compareLastOutliers = 0;
            rs.compare.compareLastOutlierLimit = 0;
          }
        } /* end of GLSL fragment/compute else block */
      }
      if (rs.compare.compareRestorePending && !rs.compare.comparePresetSweep && rs.compare.comparePresetSaved &&
          !rs.compare.captureCompareSnapshot) {
        CameraState &camMutable = input.camera();
        camMutable = rs.compare.comparePresetSavedCamera;
        rs.camera.cameraModeIndex = rs.compare.comparePresetSavedMode;
        rs.camera.orbitRadius = rs.compare.comparePresetSavedOrbitRadius;
        rs.camera.orbitSpeed = rs.compare.comparePresetSavedOrbitSpeed;
        rs.camera.orbitTime = rs.compare.comparePresetSavedOrbitTime;
        rs.physicsCore.kerrSpin = rs.compare.comparePresetSavedKerrSpin;
        rs.compare.comparePresetSaved = false;
        rs.compare.compareRestorePending = false;
      }

      if (rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.bloom.begin();
      }
      {
        ZONE_SCOPED_N("Bloom Brightness");
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/bloom_brightness_pass.frag";
        rtti.textureUniforms["texture0"] = rs.targets.texBlackhole;
        rtti.targetTexture = rs.targets.texBrightness;
        rtti.width = rs.targets.renderWidth;
        rtti.height = rs.targets.renderHeight;
        rtti.floatUniforms["brightPassThreshold"] = rs.post.bloomThreshold;
        rtti.floatUniforms["brightPassKnee"]      = rs.post.bloomKnee;
        renderToTexture(rtti);
      }

      // Post Processing panel moved to Main Settings

      {
        ZONE_SCOPED_N("Bloom Downsample");
        for (int level = 0; level < rs.post.bloomIterations; level++) {
          auto const levelIndex = static_cast<std::size_t>(level);
          RenderToTextureInfo rtti;
          rtti.fragShader = "shader/bloom_downsample.frag";
          rtti.textureUniforms["texture0"] =
              level == 0 ? rs.targets.texBrightness : rs.targets.texDownsampled.at(static_cast<std::size_t>(level - 1));
          rtti.targetTexture = rs.targets.texDownsampled.at(levelIndex);
          int const downWidth = std::max(1, rs.targets.renderWidth >> (level + 1));
          int const downHeight = std::max(1, rs.targets.renderHeight >> (level + 1));
          rtti.width = downWidth;
          rtti.height = downHeight;
          renderToTexture(rtti);
        }
      }

      {
        ZONE_SCOPED_N("Bloom Upsample");
        for (int level = rs.post.bloomIterations - 1; level >= 0; level--) {
          auto const levelIndex = static_cast<std::size_t>(level);
          RenderToTextureInfo rtti;
          rtti.fragShader = "shader/bloom_upsample.frag";
          rtti.textureUniforms["texture0"] =
              level == rs.post.bloomIterations - 1 ? rs.targets.texDownsampled.at(levelIndex)
                                           : rs.targets.texUpsampled.at(static_cast<std::size_t>(level) + 1);
          rtti.textureUniforms["texture1"] =
              level == 0 ? rs.targets.texBrightness : rs.targets.texDownsampled.at(static_cast<std::size_t>(level - 1));
          rtti.targetTexture = rs.targets.texUpsampled.at(levelIndex);
          int const upWidth = std::max(1, rs.targets.renderWidth >> level);
          int const upHeight = std::max(1, rs.targets.renderHeight >> level);
          rtti.width = upWidth;
          rtti.height = upHeight;
          renderToTexture(rtti);
        }
      }

      {
        ZONE_SCOPED_N("Bloom Composite");
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/bloom_composite.frag";
        rtti.textureUniforms["texture0"] = rs.targets.texBlackhole;
        rtti.textureUniforms["texture1"] = rs.targets.texUpsampled.at(0);
        rtti.targetTexture = rs.targets.texBloomFinal;
        rtti.width = rs.targets.renderWidth;
        rtti.height = rs.targets.renderHeight;

        if (input.isUIVisible()) {
          ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
          ImGui::SliderFloat("bloomStrength",  &rs.post.bloomStrength, 0.0f, 1.0f);
          ImGui::SliderFloat("bloomThreshold", &rs.post.bloomThreshold, 0.0f, 2.0f);
          ImGui::SliderFloat("bloomKnee",      &rs.post.bloomKnee, 0.0f, 0.5f);
          ImGui::SliderFloat("bloomTone",      &rs.post.bloomTone, 0.0f, 2.0f);
          settings.bloomStrength = rs.post.bloomStrength;
          ImGui::End();
        }
        rtti.floatUniforms["bloomStrength"] = rs.post.bloomStrength;
        rtti.floatUniforms["tone"]          = rs.post.bloomTone;

        renderToTexture(rtti);
      }
      if (rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.bloom.end();
      }

      if (rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.tonemap.begin();
      }
      {
        ZONE_SCOPED_N("Tonemap");
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/tonemapping.frag";
        rtti.textureUniforms["texture0"] = rs.targets.texBloomFinal;
        rtti.targetTexture = rs.targets.texTonemapped;
        rtti.width = rs.targets.renderWidth;
        rtti.height = rs.targets.renderHeight;

        if (input.isUIVisible()) {
          ImGui::Begin("Post Processing", nullptr, ImGuiWindowFlags_NoCollapse);
          ImGui::Checkbox("tonemappingEnabled", &rs.post.tonemappingEnabled);
          ImGui::SliderFloat("exposure", &rs.post.toneExposure, 0.01f, 2.0f, "%.2f", ImGuiSliderFlags_Logarithmic);
          ImGui::SliderFloat("gamma", &rs.post.gamma, 1.0f, 4.0f);
          settings.tonemappingEnabled = rs.post.tonemappingEnabled;
          settings.gamma = rs.post.gamma;
          ImGui::End();
        }
        rtti.floatUniforms["tonemappingEnabled"] = rs.post.tonemappingEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["exposure"] = rs.post.toneExposure;
        rtti.floatUniforms["gamma"] = rs.post.gamma;
        rtti.floatUniforms["chromaticAberrationStrength"] = rs.post.tonemapChromaticAberrationStrength;
        rtti.floatUniforms["vignetteStrength"] = rs.post.tonemapVignetteStrength;
        rtti.floatUniforms["filmGrainStrength"] = rs.post.tonemapFilmGrainStrength;

        renderToTexture(rtti);
      }
      if (rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.tonemap.end();
      }


      if (input.isUIVisible()) {
        ImGui::Begin("Depth Effects", nullptr, ImGuiWindowFlags_NoCollapse);
        ImGui::Checkbox("Enable Depth Effects", &rs.depthFx.depthEffectsEnabled);
        ImGui::SliderFloat("Depth Far", &rs.display.depthFar, 10.0f, 200.0f);
        if (ImGui::Button("Preset: Subtle")) {
          rs.depthFx.depthEffectsEnabled = true;
          rs.depthFx.fogEnabled = true;
          rs.depthFx.fogDensity = 0.08f;
          rs.depthFx.fogStart = 0.6f;
          rs.depthFx.fogEnd = 0.98f;
          rs.depthFx.fogColor[0] = 0.06f;
          rs.depthFx.fogColor[1] = 0.06f;
          rs.depthFx.fogColor[2] = 0.10f;
          rs.depthFx.edgeOutlinesEnabled = false;
          rs.depthFx.edgeThreshold = 0.5f;
          rs.depthFx.edgeWidth = 1.0f;
          rs.depthFx.depthDesatEnabled = true;
          rs.depthFx.desatStrength = 0.10f;
          rs.depthFx.chromaDepthEnabled = false;
          rs.depthFx.motionParallaxHint = false;
          rs.depthFx.dofEnabled = false;
          rs.depthFx.dofFocusNear = 0.3f;
          rs.depthFx.dofFocusFar = 0.9f;
          rs.depthFx.dofMaxRadius = 2.0f;
          rs.depthFx.depthCurve = 1.0f;
          rs.display.depthFar = 100.0f;
        }
        ImGui::SameLine();
        if (ImGui::Button("Preset: Cinematic")) {
          rs.depthFx.depthEffectsEnabled = true;
          rs.depthFx.fogEnabled = true;
          rs.depthFx.fogDensity = 0.3f;
          rs.depthFx.fogStart = 0.25f;
          rs.depthFx.fogEnd = 0.85f;
          rs.depthFx.fogColor[0] = 0.08f;
          rs.depthFx.fogColor[1] = 0.08f;
          rs.depthFx.fogColor[2] = 0.12f;
          rs.depthFx.edgeOutlinesEnabled = true;
          rs.depthFx.edgeThreshold = 0.5f;
          rs.depthFx.edgeWidth = 1.2f;
          rs.depthFx.depthDesatEnabled = true;
          rs.depthFx.desatStrength = 0.35f;
          rs.depthFx.chromaDepthEnabled = true;
          rs.depthFx.motionParallaxHint = false;
          rs.depthFx.dofEnabled = true;
          rs.depthFx.dofFocusNear = 0.25f;
          rs.depthFx.dofFocusFar = 0.75f;
          rs.depthFx.dofMaxRadius = 5.0f;
          rs.depthFx.depthCurve = 0.95f;
          rs.display.depthFar = 100.0f;
        }
        ImGui::SameLine();
        if (ImGui::Button("Preset: Clarity")) {
          rs.depthFx.depthEffectsEnabled = true;
          rs.depthFx.fogEnabled = true;
          rs.depthFx.fogDensity = 0.12f;
          rs.depthFx.fogStart = 0.45f;
          rs.depthFx.fogEnd = 0.95f;
          rs.depthFx.fogColor[0] = 0.05f;
          rs.depthFx.fogColor[1] = 0.05f;
          rs.depthFx.fogColor[2] = 0.08f;
          rs.depthFx.edgeOutlinesEnabled = true;
          rs.depthFx.edgeThreshold = 0.42f;
          rs.depthFx.edgeWidth = 1.4f;
          rs.depthFx.depthDesatEnabled = true;
          rs.depthFx.desatStrength = 0.15f;
          rs.depthFx.chromaDepthEnabled = false;
          rs.depthFx.motionParallaxHint = false;
          rs.depthFx.dofEnabled = false;
          rs.depthFx.dofFocusNear = 0.35f;
          rs.depthFx.dofFocusFar = 0.95f;
          rs.depthFx.dofMaxRadius = 2.5f;
          rs.depthFx.depthCurve = 1.15f;
          rs.display.depthFar = 100.0f;
        }
        ImGui::Separator();

        ImGui::Checkbox("Fog", &rs.depthFx.fogEnabled);
        ImGui::SliderFloat("Fog Density", &rs.depthFx.fogDensity, 0.0f, 1.0f);
        ImGui::SliderFloat("Fog Start", &rs.depthFx.fogStart, 0.0f, 1.0f);
        ImGui::SliderFloat("Fog End", &rs.depthFx.fogEnd, 0.0f, 1.0f);
        rs.depthFx.fogStart = std::min(rs.depthFx.fogStart, rs.depthFx.fogEnd);
        ImGui::ColorEdit3("Fog Color", rs.depthFx.fogColor);

        ImGui::Separator();
        ImGui::Checkbox("Edge Outlines", &rs.depthFx.edgeOutlinesEnabled);
        ImGui::SliderFloat("Edge Threshold", &rs.depthFx.edgeThreshold, 0.0f, 1.0f);
        ImGui::SliderFloat("Edge Width", &rs.depthFx.edgeWidth, 0.5f, 3.0f);
        ImGui::ColorEdit3("Edge Color", rs.depthFx.edgeColor);

        ImGui::Separator();
        ImGui::Checkbox("Depth Desaturation", &rs.depthFx.depthDesatEnabled);
        ImGui::SliderFloat("Desaturation", &rs.depthFx.desatStrength, 0.0f, 1.0f);
        ImGui::Checkbox("Chroma Depth", &rs.depthFx.chromaDepthEnabled);
        ImGui::Checkbox("Motion Parallax Hint", &rs.depthFx.motionParallaxHint);

        ImGui::Separator();
        ImGui::Checkbox("Depth of Field", &rs.depthFx.dofEnabled);
        ImGui::SliderFloat("DoF Focus Near", &rs.depthFx.dofFocusNear, 0.0f, 1.0f);
        ImGui::SliderFloat("DoF Focus Far", &rs.depthFx.dofFocusFar, 0.0f, 1.0f);
        rs.depthFx.dofFocusNear = std::min(rs.depthFx.dofFocusNear, rs.depthFx.dofFocusFar);
        ImGui::SliderFloat("DoF Max Radius", &rs.depthFx.dofMaxRadius, 0.0f, 12.0f);
        ImGui::SliderFloat("Depth Curve", &rs.depthFx.depthCurve, 0.5f, 2.0f);
        ImGui::End();
      }

      GLuint finalTexture = rs.targets.texTonemapped;
      if (rs.depthFx.depthEffectsEnabled) {
        ZONE_SCOPED_N("Depth Cues");
        if (rs.timing.gpuTimers.initialized) {
          rs.timing.gpuTimers.depth.begin();
        }
        RenderToTextureInfo rtti;
        rtti.fragShader = "shader/depth_cues.frag";
        rtti.textureUniforms["texture0"] = rs.targets.texTonemapped;
        rtti.textureUniforms["depthTexture"] = rs.targets.texBlackhole;
        rtti.targetTexture = rs.targets.texDepthEffects;
        rtti.width = rs.targets.renderWidth;
        rtti.height = rs.targets.renderHeight;
        rtti.floatUniforms["depthEffectsEnabled"] = 1.0f;
        rtti.floatUniforms["fogEnabled"] = rs.depthFx.fogEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["fogDensity"] = rs.depthFx.fogDensity;
        rtti.floatUniforms["fogStart"] = rs.depthFx.fogStart;
        rtti.floatUniforms["fogEnd"] = rs.depthFx.fogEnd;
        rtti.floatUniforms["fogColorR"] = rs.depthFx.fogColor[0];
        rtti.floatUniforms["fogColorG"] = rs.depthFx.fogColor[1];
        rtti.floatUniforms["fogColorB"] = rs.depthFx.fogColor[2];
        rtti.floatUniforms["edgeOutlinesEnabled"] = rs.depthFx.edgeOutlinesEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["edgeThreshold"] = rs.depthFx.edgeThreshold;
        rtti.floatUniforms["edgeWidth"] = rs.depthFx.edgeWidth;
        rtti.floatUniforms["edgeColorR"] = rs.depthFx.edgeColor[0];
        rtti.floatUniforms["edgeColorG"] = rs.depthFx.edgeColor[1];
        rtti.floatUniforms["edgeColorB"] = rs.depthFx.edgeColor[2];
        rtti.floatUniforms["depthDesatEnabled"] = rs.depthFx.depthDesatEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["desatStrength"] = rs.depthFx.desatStrength;
        rtti.floatUniforms["chromaDepthEnabled"] = rs.depthFx.chromaDepthEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["motionParallaxHint"] = rs.depthFx.motionParallaxHint ? 1.0f : 0.0f;
        rtti.floatUniforms["dofEnabled"] = rs.depthFx.dofEnabled ? 1.0f : 0.0f;
        rtti.floatUniforms["dofFocusNear"] = rs.depthFx.dofFocusNear;
        rtti.floatUniforms["dofFocusFar"] = rs.depthFx.dofFocusFar;
        rtti.floatUniforms["dofMaxRadius"] = rs.depthFx.dofMaxRadius;
        rtti.floatUniforms["depthCurve"] = rs.depthFx.depthCurve;
        renderToTexture(rtti);
        finalTexture = rs.targets.texDepthEffects;
        if (rs.timing.gpuTimers.initialized) {
          rs.timing.gpuTimers.depth.end();
        }
      }

      // Re-open Viewport to render the scene image
      ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0.0f, 0.0f));
      ImGui::Begin("Viewport", nullptr,
                   ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse |
                       ImGuiWindowFlags_NoTitleBar);
      viewportSize = ImGui::GetContentRegionAvail();

      // ---------------------------------------------------------
      // SCENE COMPOSITION (Post-process overlay passes)
      // ---------------------------------------------------------
      // Render wiregrid and overlays into the final texture before display
      {
        if (rs.targets.sceneFbo == 0) {
          glGenFramebuffers(1, &rs.targets.sceneFbo);
        }
        glBindFramebuffer(GL_FRAMEBUFFER, rs.targets.sceneFbo);
        glFramebufferTexture2D(GL_FRAMEBUFFER, GL_COLOR_ATTACHMENT0, GL_TEXTURE_2D, finalTexture,
                               0);
        glViewport(0, 0, rs.targets.renderWidth, rs.targets.renderHeight);

        // 1. Wiregrid BL-coord overlay -- implemented in task A2 (fragment shader)

        // 2. GRMHD Slice
        if (rs.grmhd.grmhdSliceEnabled && grmhdReady) {
          ZONE_SCOPED_N("GRMHD Slice");
          rs.grmhd.grmhdSliceAxis = std::clamp(rs.grmhd.grmhdSliceAxis, 0, 2);
          rs.grmhd.grmhdSliceChannel = std::clamp(rs.grmhd.grmhdSliceChannel, 0, 3);
          rs.grmhd.grmhdSliceCoord = std::clamp(rs.grmhd.grmhdSliceCoord, 0.0f, 1.0f);
          rs.grmhd.grmhdSliceSize = std::clamp(rs.grmhd.grmhdSliceSize, 64, 1024);

          const auto channelIndex = static_cast<std::size_t>(rs.grmhd.grmhdSliceChannel);
          if (rs.grmhd.grmhdSliceAutoRange && channelIndex < rs.grmhd.grmhdTexture.minValues.size() &&
              channelIndex < rs.grmhd.grmhdTexture.maxValues.size()) {
            rs.grmhd.grmhdSliceMin = rs.grmhd.grmhdTexture.minValues.at(channelIndex);
            rs.grmhd.grmhdSliceMax = rs.grmhd.grmhdTexture.maxValues.at(channelIndex);
          }
          if (rs.grmhd.grmhdSliceMax <= rs.grmhd.grmhdSliceMin) {
            rs.grmhd.grmhdSliceMax = rs.grmhd.grmhdSliceMin + 1.0f;
          }

          if (rs.grmhd.texGrmhdSlice == 0 || rs.grmhd.grmhdSliceSizeCached != rs.grmhd.grmhdSliceSize) {
            if (rs.grmhd.texGrmhdSlice != 0) {
              glDeleteTextures(1, &rs.grmhd.texGrmhdSlice);
              rs.grmhd.texGrmhdSlice = 0;
            }
            rs.grmhd.texGrmhdSlice = createColorTexture32f(rs.grmhd.grmhdSliceSize, rs.grmhd.grmhdSliceSize);
            rs.grmhd.grmhdSliceSizeCached = rs.grmhd.grmhdSliceSize;
          }

          RenderToTextureInfo sliceRtti;
          sliceRtti.fragShader = "shader/grmhd_slice.frag";
          sliceRtti.texture3DUniforms["grmhdTexture"] =
              (rs.grmhd.grmhdTimeSeriesLoaded && rs.grmhd.grmhdPboUploader.ready())
                  ? rs.grmhd.grmhdPboUploader.texture()
                  : rs.grmhd.grmhdTexture.texture;
          sliceRtti.textureUniforms["colorMap"] = rs.background.colorMap;
          sliceRtti.floatUniforms["sliceAxis"] = static_cast<float>(rs.grmhd.grmhdSliceAxis);
          sliceRtti.floatUniforms["sliceCoord"] = rs.grmhd.grmhdSliceCoord;
          sliceRtti.floatUniforms["sliceChannel"] = static_cast<float>(rs.grmhd.grmhdSliceChannel);
          sliceRtti.floatUniforms["sliceMin"] = rs.grmhd.grmhdSliceMin;
          sliceRtti.floatUniforms["sliceMax"] = rs.grmhd.grmhdSliceMax;
          sliceRtti.floatUniforms["useColorMap"] = rs.grmhd.grmhdSliceUseColorMap ? 1.0f : 0.0f;
          sliceRtti.targetTexture = rs.grmhd.texGrmhdSlice;
          sliceRtti.width = rs.grmhd.grmhdSliceSize;
          sliceRtti.height = rs.grmhd.grmhdSliceSize;
          if (rs.timing.gpuTimers.initialized) {
            rs.timing.gpuTimers.grmhdSlice.begin();
          }
          renderToTexture(sliceRtti); // Note: renderToTexture manages its own FBO binding
          if (rs.timing.gpuTimers.initialized) {
            rs.timing.gpuTimers.grmhdSlice.end();
          }

          // Re-bind Scene FBO to draw the slice texture on top?
          // Actually, renderToTexture renders TO texGrmhdSlice.
          // We need to composite texGrmhdSlice onto the scene?
          // The original code rendered the slice to a separate texture, then displayed it in ImGui
          // Image? "ImGui::Image(sliceId, ...)" in the UI panel. So we don't need to composite it
          // here.

          // Restore FBO for subsequent passes if any
          glBindFramebuffer(GL_FRAMEBUFFER, rs.targets.sceneFbo);
        }

        // 3. RmlUi Overlay
        if (rs.overlays.rmluiReady) {
          rs.overlays.rmluiOverlay.render();
        }

        // 4. HUD Overlays (Perf/Controls)
        // Note: These renderers assume default framebuffer dimensions.
        // We set viewport to renderWidth/Height, which matches our FBO.
        if (rs.overlays.controlsOverlayEnabled && !input.isUIVisible()) {
          if (!rs.overlays.controlsOverlayReady) {
            HudOverlayOptions opts;
            opts.scale = rs.overlays.controlsOverlayScale;
            opts.margin = 16.0f;
            opts.align = HudOverlayOptions::Align::Left;
            rs.overlays.controlsOverlay.setOptions(opts);
            rs.overlays.controlsOverlayReady = true;
          }
          if (rs.overlays.controlsOverlayReady) {
            rs.overlays.controlsOverlay.render(rs.targets.renderWidth, rs.targets.renderHeight);
          }
          if (rs.overlays.perfOverlayReady) {
            rs.overlays.perfOverlay.render(rs.targets.renderWidth, rs.targets.renderHeight);
          }
        }

        glBindFramebuffer(GL_FRAMEBUFFER, 0);
      }

      // Draw Final Texture to Viewport
      ImGui::Image(
          reinterpret_cast<void *>(static_cast<intptr_t>(finalTexture)), viewportSize, ImVec2(0, 1),
          ImVec2(
              1,
              0)); // NOLINT(performance-no-int-to-ptr) -- ImGui API requires void* for texture IDs

      // Enable mouse/keyboard interaction when hovering the viewport
      bool const isViewportHovered = ImGui::IsItemHovered();
      InputManager::instance().setIgnoreGuiCapture(isViewportHovered);

      // Gizmo
      if (rs.camera.gizmoEnabled) {
        ImGuizmo::SetDrawlist();
        ImVec2 const windowPos = ImGui::GetWindowPos();
        ImGuizmo::SetRect(windowPos.x, windowPos.y, viewportSize.x, viewportSize.y);
        ImGuizmo::Manipulate(glm::value_ptr(gizmoViewMatrix), glm::value_ptr(projectionMatrix),
                             rs.camera.gizmoOperation, rs.camera.gizmoMode, glm::value_ptr(rs.camera.gizmoTransform));
      }

      ImGui::End();         // End Viewport
      ImGui::PopStyleVar(); // WindowPadding

      // Normal UI panels are hidden in record mode so they don't appear in the video.
      if (input.isUIVisible() && recordFramesDir.empty()) {
        renderControlsHelpPanel();
        renderControlsSettingsPanel(rs.camera.cameraModeIndex, rs.camera.orbitRadius, rs.camera.orbitSpeed);
        renderDisplaySettingsPanel(window, rs.display.swapInterval, rs.display.renderScale, windowWidth, windowHeight);
        renderBackgroundPanel(rs.background.backgroundAssets, rs.background.backgroundIndex,
                              settings.backgroundParallaxStrength, settings.backgroundDriftStrength,
                              rs.background.backgroundLayerDepth, rs.background.backgroundLayerScale, rs.background.backgroundLayerIntensity,
                              rs.background.backgroundLayerLodBias);
        renderWiregridPanel(rs.wiregrid.wiregridEnabled, rs.wiregrid.wiregridParams, rs.wiregrid.wiregridColor);
        renderRmlUiPanel(rs.overlays.rmluiEnabled);
        renderGizmoPanel(rs.camera.gizmoEnabled, rs.camera.gizmoOperation, rs.camera.gizmoMode, rs.camera.gizmoTransform);
        renderPerformancePanel(rs.timing.gpuTimingEnabled, rs.timing.gpuTimers, rs.timing.timingHistory, cpuFrameMs,
                               rs.overlays.perfOverlayEnabled, rs.overlays.perfOverlayScale, rs.probes.depthPrepassEnabled);
      }

      /* --export-frame / --export-raw-frame: export textures before ImGui. */
      if (!exportFramePath.empty() || !exportRawFramePath.empty()) {
        if (++rs.exporting.exportWarmup >= 5 && !rs.exporting.exportPerformed && rs.targets.renderWidth > 0 && rs.targets.renderHeight > 0) {
          if (!exportFramePath.empty() && rs.targets.texTonemapped != 0) {
            glBindTexture(GL_TEXTURE_2D, rs.targets.texTonemapped);
            GLint texW = 0, texH = 0;
            glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_WIDTH, &texW);
            glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_HEIGHT, &texH);
            int const w = (texW > 0) ? texW : rs.targets.renderWidth;
            int const h = (texH > 0) ? texH : rs.targets.renderHeight;
            std::vector<unsigned char> px(static_cast<size_t>(w) * static_cast<size_t>(h) * 3);
            glPixelStorei(GL_PACK_ALIGNMENT, 1);
            glGetTexImage(GL_TEXTURE_2D, 0, GL_RGB, GL_UNSIGNED_BYTE, px.data());
            glPixelStorei(GL_PACK_ALIGNMENT, 4);
            glBindTexture(GL_TEXTURE_2D, 0);
            /* glGetTexImage gives bottom-to-top; flip for PNG. */
            std::vector<unsigned char> flipped(px.size());
            for (int row = 0; row < h; ++row) {
              std::memcpy(
                  flipped.data() + static_cast<size_t>(row) * static_cast<size_t>(w) * 3,
                  px.data() + static_cast<size_t>(h - 1 - row) * static_cast<size_t>(w) * 3,
                  static_cast<size_t>(w) * 3);
            }
            stbi_write_png(exportFramePath.c_str(), w, h, 3, flipped.data(), w * 3);
            std::printf("Exported frame: %s (%dx%d)\n", exportFramePath.c_str(), w, h);
          }

          if (!exportRawFramePath.empty() && rs.targets.texBlackhole != 0) {
            GLint texW = 0;
            GLint texH = 0;
            glBindTexture(GL_TEXTURE_2D, rs.targets.texBlackhole);
            glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_WIDTH, &texW);
            glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_HEIGHT, &texH);
            glBindTexture(GL_TEXTURE_2D, 0);
            int const w = (texW > 0) ? texW : rs.targets.renderWidth;
            int const h = (texH > 0) ? texH : rs.targets.renderHeight;
            std::vector<float> raw;
            if (readTextureRGBA(rs.targets.texBlackhole, w, h, raw) &&
                writePfmRgb(exportRawFramePath, raw, w, h)) {
              std::printf("Exported raw frame: %s (%dx%d)\n", exportRawFramePath.c_str(), w, h);
            } else {
              std::fprintf(stderr, "Failed to export raw frame: %s\n",
                           exportRawFramePath.c_str());
            }
          }
          rs.exporting.exportPerformed = true;
        }
      }

      /* --record-frames: draw cinematic physics HUD via foreground draw list.
       * GetForegroundDrawList() adds to ImGui's draw list, so this must be called
       * before ImGui::Render().  The overlay is composited over the scene by the
       * ImGui backend when RenderDrawData() runs below. */
      if (!recordFramesDir.empty()) {
        ++rs.recording.recordWarmup;
      }
      if (!recordFramesDir.empty() && recordProfile == "cinematic" && rs.recording.recordWarmup >= 15) {
        renderCinematicOverlay(rs.recording.recordCinematic, rs.recording.recordCurrentKf,
                               glm::length(cameraPos),
                               rs.recording.recordCurRs, rs.recording.recordCurIsco,
                               rs.recording.recordFrameIndex, recordFramesTotal);
      }

      // ImGui Render
      ImGui::Render();
      ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());

      /* --record-frames: capture the tonemapped scene texture via glGetTexImage.
       * WHY: glReadPixels(0) reads the window's default framebuffer which is
       * mostly ImGui chrome (black panels).  rs.targets.texTonemapped holds the full
       * rendered scene at rs.targets.renderWidth x rs.targets.renderHeight, identical to the
       * --export-frame path that is known to work.  The cinematic HUD overlay
       * drawn via GetForegroundDrawList() is composited by ffmpeg drawtext later;
       * the overlay is still drawn above in the ImGui frame for live preview. */
      /* WHY: glfwSetWindowSize() is asynchronous; the resize callback fires in
       * glfwPollEvents().  Wait 15 warmup frames (~250ms) to let the window and
       * render targets settle at the requested size before starting capture.
       * If the WM caps the window smaller (e.g., in a desktop session), we accept
       * whatever size the window settled at after the warmup period. */
      if (!recordFramesDir.empty() && rs.recording.recordWarmup >= 15
          && rs.targets.texTonemapped != 0 && rs.targets.renderWidth > 0 && rs.targets.renderHeight > 0) {
        glBindTexture(GL_TEXTURE_2D, rs.targets.texTonemapped);
        // Query actual stored texture dimensions -- these may differ from
        // renderWidth/renderHeight if the texture was created at a different
        // resolution (e.g. before the window settled to its current size).
        // glGetTexImage writes texW*texH*channels bytes; a size mismatch would
        // corrupt the heap metadata of the next allocation.
        GLint texW = 0, texH = 0;
        glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_WIDTH, &texW);
        glGetTexLevelParameteriv(GL_TEXTURE_2D, 0, GL_TEXTURE_HEIGHT, &texH);
        int const w = (texW > 0) ? texW : rs.targets.renderWidth;
        int const h = (texH > 0) ? texH : rs.targets.renderHeight;
        std::vector<unsigned char> px(static_cast<size_t>(w) * static_cast<size_t>(h) * 3);
        // GL_PACK_ALIGNMENT defaults to 4: each row is padded to a 4-byte boundary.
        // For widths like 1343, row bytes = 1343*3=4029 which rounds up to 4032,
        // overflowing our tightly-sized buffer by (4032-4029)*h = 3177 bytes and
        // corrupting the next heap chunk's malloc header (SIGABRT on free).
        // Setting alignment to 1 disables row padding for the download.
        glPixelStorei(GL_PACK_ALIGNMENT, 1);
        glGetTexImage(GL_TEXTURE_2D, 0, GL_RGB, GL_UNSIGNED_BYTE, px.data());
        glPixelStorei(GL_PACK_ALIGNMENT, 4);
        glBindTexture(GL_TEXTURE_2D, 0);
        /* glGetTexImage is bottom-to-top; flip vertically for correct PNG. */
        std::vector<unsigned char> flipped(px.size());
        for (int row = 0; row < h; ++row) {
          std::memcpy(
              flipped.data() + static_cast<size_t>(row) * static_cast<size_t>(w) * 3,
              px.data() + static_cast<size_t>(h - 1 - row) * static_cast<size_t>(w) * 3,
              static_cast<size_t>(w) * 3);
        }
        char framePath[1024];
        std::snprintf(framePath, sizeof(framePath), "%s/frame_%06d.png",
                      recordFramesDir.c_str(), rs.recording.recordFrameIndex);
        stbi_write_png(framePath, w, h, 3, flipped.data(), w * 3);
        if (rs.recording.recordFrameIndex % K_CINEMATIC_FPS == 0) {
          std::printf("Record: frame %d / %d  (t = %.1f s)  [%dx%d]\n",
                      rs.recording.recordFrameIndex, recordFramesTotal,
                      static_cast<double>(rs.recording.recordCinematic), w, h);
        }
        ++rs.recording.recordFrameIndex;
        rs.recording.recordCinematic = static_cast<float>(rs.recording.recordFrameIndex) / static_cast<float>(K_CINEMATIC_FPS);
      }

      // Update Platform Windows (Docking)
      if ((ImGui::GetIO().ConfigFlags & ImGuiConfigFlags_ViewportsEnable) != 0) {
        GLFWwindow *backupCurrentContext = glfwGetCurrentContext();
        ImGui::UpdatePlatformWindows();
        ImGui::RenderPlatformWindowsDefault();
        glfwMakeContextCurrent(backupCurrentContext);
      }

      if (rs.timing.gpuTimingLogEnabled && rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimingLogCounter++;
        if (rs.timing.gpuTimingLogCounter >= rs.timing.gpuTimingLogStride) {
          appendGpuTimingSample(gpuTimingPath(), rs.timing.gpuTimingLogIndex++, rs.targets.renderWidth, rs.targets.renderHeight,
                                cpuFrameMs, rs.timing.gpuTimers, computeActiveForLog, rs.physicsCore.kerrSpin,
                                glfwGetTime());
          rs.timing.gpuTimingLogCounter = 0;
        }
      }

      if (rs.timing.gpuTimers.initialized) {
        rs.timing.gpuTimers.swap();
      }
      FRAME_MARK;
      glfwSwapBuffers(window);

      /* --export-frame / --export-raw-frame: break after the export frame above. */
      if (!exportFramePath.empty() || !exportRawFramePath.empty()) {
        if (++rs.exporting.exportDone >= 6) { /* 5 warmup + 1 export frame */
          break;
        }
      }

      /* --record-frames: break when all requested frames have been captured.
       * rs.recording.recordFrameIndex starts at recordStartFrame; terminate when we have
       * written recordFramesTotal frames (i.e. reached recordStartFrame+total). */
      if (!recordFramesDir.empty()
          && rs.recording.recordFrameIndex >= recordStartFrame + recordFramesTotal) {
        int const written = rs.recording.recordFrameIndex - recordStartFrame;
        std::printf("Record complete: %d frames written to %s\n",
                    written, recordFramesDir.c_str());
        break;
      }
    }

    {
      int finalWindowWidth = 0;
      int finalWindowHeight = 0;
      glfwGetWindowSize(window, &finalWindowWidth, &finalWindowHeight);
      if (!InputManager::instance().isFullscreen()) {
        settings.windowWidth = finalWindowWidth;
        settings.windowHeight = finalWindowHeight;
      }
      settings.fullscreen = InputManager::instance().isFullscreen();
      settings.swapInterval = rs.display.swapInterval;
      settings.renderScale = rs.display.renderScale;
      settings.cameraMode = rs.camera.cameraModeIndex;
      settings.orbitRadius = rs.camera.orbitRadius;
      settings.orbitSpeed = rs.camera.orbitSpeed;
    }

    if (rs.overlays.controlsOverlayReady) {
      rs.overlays.controlsOverlay.shutdown();
    }
    if (rs.overlays.rmluiReady) {
      rs.overlays.rmluiOverlay.shutdown();
    }

    // Explicitly clean up static resources before GL context destruction
    rs.disk.noiseCache.cleanup();
    rs.hawking.hawkingRenderer.cleanup();
    if (rs.grmhd.grmhdTexture.texture != 0) {
      destroyGrmhdPackedTexture(rs.grmhd.grmhdTexture);
    }

#if BLACKHOLE_HAS_CUDA
    rs.dispatch.cudaManager.shutdown();
#endif
    cleanup(window);
    return 0;
#if BLACKHOLE_HAS_CPPTRACE
  } catch (const cpptrace::exception &err) {
    std::fprintf(stderr, "Unhandled cpptrace exception: %s\n",
                 err.what()); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    err.trace().print();
    return 1;
  } catch (const std::exception &err) {
    std::fprintf(stderr, "Unhandled std::exception: %s\n",
                 err.what()); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    cpptrace::generate_trace(1).print();
    return 1;
  } catch (...) {
    std::fprintf(stderr, "Unhandled non-standard exception\n"); // NOLINT(cert-err33-c) --
                                                                // diagnostic output, return unused
    cpptrace::generate_trace(1).print();
    return 1;
  }
#else
  } catch (const std::exception &err) {
    std::fprintf(stderr, "Unhandled std::exception: %s\n", err.what());
    return 1;
  } catch (...) {
    std::fprintf(stderr, "Unhandled non-standard exception\n");
    return 1;
  }
#endif
}
