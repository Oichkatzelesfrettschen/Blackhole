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
#include "render/lut_manager.h"
#include "render/uniform_binding.h"
#include "tools/compare_harness.h"
#include "render/render_state.h"
#include "ui/panels.h"
#include "ui/settings_window.h"
#include "platform/cli_options.h"
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

constexpr bool kAppVariantGlslOnly = BLACKHOLE_APP_VARIANT_GLSL_ONLY != 0;
constexpr bool kAppVariantCudaOnly = BLACKHOLE_APP_VARIANT_CUDA_ONLY != 0;
constexpr const char *kWindowTitle = kAppVariantCudaOnly
                                         ? "BlackholeCUDA"
                                         : (kAppVariantGlslOnly ? "BlackholeGLSL" : "Blackhole");

// Extracted modules keep their call sites unqualified (STATE-2 extraction).
using platform::readTextFile;
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

// BackgroundAsset, WiregridParams, K_BACKGROUND_LAYERS, kMaxBloomIterations,
// and RenderState live in src/render/render_state.h.
using blackhole::BackgroundAsset;
using blackhole::WiregridParams;
using blackhole::K_BACKGROUND_LAYERS;
using blackhole::kMaxBloomIterations;
using blackhole::RenderState;

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

// ImGui panels + style/context/init/dock helpers live in src/ui/panels.*.
using ui::applyWiregridModeProfile;
using ui::initializeImGui;
using ui::renderControlsHelpPanel;
using ui::renderControlsSettingsPanel;
using ui::renderGizmoPanel;
using ui::renderDisplaySettingsPanel;
using ui::renderBackgroundPanel;
using ui::renderWiregridPanel;
using ui::renderRmlUiPanel;
using ui::renderPerformancePanel;
using ui::resetLayout;
using ui::renderSettingsWindow;
using ui::renderCurveOverlayWindow;
using ui::renderBloomPanel;
using ui::renderTonemapPanel;
using ui::renderDepthEffectsPanel;

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

// Shared raytracer uniform binders live in src/render/uniform_binding.*
// (registry-driven fragment/compute float fills + Hawking forwarder).
using blackhole::applyInteropComputeUniforms;
using blackhole::applyHawkingUniforms;
using blackhole::bindComputeUniforms;
using blackhole::bindFragmentUniforms;
using blackhole::FrameBindingInputs;

// Radiative-transfer LUT lifecycle lives in src/render/lut_manager.*.
using blackhole::loadGrbModulationLutAssets;
using blackhole::loadSpectralLutAssets;
using blackhole::updateLuts;
#if BLACKHOLE_HAS_CUDA
using blackhole::bindCudaLaunchParams;
#endif


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







} // anonymous namespace

// NOLINTNEXTLINE(readability-function-cognitive-complexity,readability-function-size) --
// application main loop
int main(int argc, char **argv) {
  platform::installCrashHandlers();
  try {
    platform::CliOptions cli;
    switch (platform::parseCliOptions(argc, argv, cli)) {
    case platform::CliParseOutcome::ExitSuccess:
      return 0;
    case platform::CliParseOutcome::ExitFailure:
      return 2;
    case platform::CliParseOutcome::Run:
      break;
    }

    // Alias the parsed options back to the names the render loop reads. The
    // record-mode consumption sites stay byte-identical; cli is the config
    // object the eventual recording extraction consumes.
    auto &curveTsvPath = cli.curveTsvPath;
    auto &exportFramePath = cli.exportFramePath;
    auto &exportRawFramePath = cli.exportRawFramePath;
    auto &recordFramesDir = cli.recordFramesDir;
    auto &recordProfile = cli.recordProfile;
    auto &recordComposition = cli.recordComposition;
    auto &recordBackgroundId = cli.recordBackgroundId;
    auto &recordFramesTotal = cli.recordFramesTotal;
    auto &recordStartFrame = cli.recordStartFrame;
    auto &recordYawDeg = cli.recordYawDeg;
    auto &hasRecordYaw = cli.hasRecordYaw;
    auto &recordPitchDeg = cli.recordPitchDeg;
    auto &hasRecordPitch = cli.hasRecordPitch;
    auto &recordDistance = cli.recordDistance;
    auto &hasRecordDistance = cli.hasRecordDistance;
    auto &recordFovDeg = cli.recordFovDeg;
    auto &hasRecordFov = cli.hasRecordFov;
    auto &recordExposure = cli.recordExposure;
    auto &hasRecordExposure = cli.hasRecordExposure;
    auto &recordSweepDeg = cli.recordSweepDeg;
    auto &hasRecordSweep = cli.hasRecordSweep;
    auto &recordFrameX = cli.recordFrameX;
    auto &hasRecordFrameX = cli.hasRecordFrameX;
    auto &recordFrameY = cli.recordFrameY;
    auto &hasRecordFrameY = cli.hasRecordFrameY;
    auto &hasRecordBackgroundId = cli.hasRecordBackgroundId;
    auto &recordBackgroundYawDeg = cli.recordBackgroundYawDeg;
    auto &hasRecordBackgroundYaw = cli.hasRecordBackgroundYaw;
    auto &recordBackgroundPitchDeg = cli.recordBackgroundPitchDeg;
    auto &hasRecordBackgroundPitch = cli.hasRecordBackgroundPitch;

    // Semantic validation lives here, where the showcase-orbit table is defined.
    if (recordProfile != "cinematic" && recordProfile != "compare-orbit-near" &&
        recordProfile != "showcase-orbit") {
      std::printf("Unknown record profile: %s\n", recordProfile.c_str());
      platform::printCliUsage(argv[0]);
      return 2;
    }
    if (recordProfile == "showcase-orbit" &&
        findShowcaseOrbitComposition(recordComposition) == nullptr) {
      std::printf("Unknown showcase composition: %s\n", recordComposition.c_str());
      platform::printCliUsage(argv[0]);
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
        // spectralLUT, grbModulationLUT, and the Hawking LUTs are bound in
        // bindFragmentUniforms after the between-passes LUT loads settle.
        for (int i = 0; i < K_BACKGROUND_LAYERS; ++i) {
          const std::string name = "backgroundLayers[" + std::to_string(i) + "]";
          rtti.textureUniforms[name] = rs.background.backgroundTextures.at(static_cast<std::size_t>(i));
        }
        rs.disk.noiseTextureScale = std::max(rs.disk.noiseTextureScale, 0.01f);
        // noiseTexture/grmhdTexture and useNoiseTexture/useGrmhd/backgroundEnabled/
        // time are set in bindFragmentUniforms from post-derivation readiness.
        rtti.floatUniforms["noiseTextureScale"] = rs.disk.noiseTextureScale;
        rtti.floatUniforms["backgroundIntensity"] = settings.backgroundIntensity;
        rtti.floatUniforms["backgroundYawRad"] = rs.background.backgroundYawRad;
        rtti.floatUniforms["backgroundPitchRad"] = rs.background.backgroundPitchRad;
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
          renderSettingsWindow(rs);
        }

        renderCurveOverlayWindow(rs, curveTsvPath);

        updateLuts(rs, rs.physicsCore.kerrSpin, rs.disk.adiskDensityV);
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
        bool const noiseReady = useNoiseTextureEffective && rs.disk.texNoiseVolume != 0;

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

        // Per-frame derived transients shared by the fragment, CUDA, and
        // compute uniform binders (compare-baseline gating, LUT readiness,
        // precomputed record frame shift); see FrameBindingInputs.
        FrameBindingInputs frameInputs;
        frameInputs.adiskEnabledEffective = adiskEnabledEffective;
        frameInputs.enableRedshiftEffective = enableRedshiftEffective;
        frameInputs.backgroundEnabledEffective = backgroundEnabledEffective;
        frameInputs.enablePhotonSphereEffective = enablePhotonSphereEffective;
        frameInputs.backgroundIntensity = settings.backgroundIntensity;
        frameInputs.lutReady = lutReady;
        frameInputs.spectralEnabled = spectralEnabled;
        frameInputs.grbModulationEnabled = grbModulationEnabled;
        frameInputs.noiseReady = noiseReady;
        frameInputs.grmhdEnabled = grmhdEnabled;
        frameInputs.adiskParticleEffective = adiskParticleEffective;
        frameInputs.compareActive = compareActive;
        frameInputs.grmhdTexId = grmhdTexId;
        /* Record-mode showcase-orbit frame offset; defaults (0,0) cover the
         * non-record path via FrameBindingInputs member initializers. */
        if (!recordFramesDir.empty() && recordProfile == "showcase-orbit") {
          const ShowcaseOrbitComposition *const composition =
              findShowcaseOrbitComposition(recordComposition);
          frameInputs.frameShiftX =
              hasRecordFrameX ? recordFrameX
                              : (composition != nullptr ? composition->frameOffsetX : 0.0f);
          frameInputs.frameShiftY =
              hasRecordFrameY ? recordFrameY
                              : (composition != nullptr ? composition->frameOffsetY : 0.0f);
        }

        // Load-order-independent fragment uniforms (the emissivity-family LUT
        // bindings stay above, before updateLuts reassigns their handles).
        bindFragmentUniforms(rtti, rs, interop, frameInputs);

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
            bindCudaLaunchParams(cp, rs, interop, frameInputs);

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

            bindComputeUniforms(computeProgram, rs, frameInputs);

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
          renderBloomPanel(rs);
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
          renderTonemapPanel(rs);
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
        renderDepthEffectsPanel(rs);
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
        renderControlsSettingsPanel(rs);
        renderDisplaySettingsPanel(rs, window, windowWidth, windowHeight);
        renderBackgroundPanel(rs);
        renderWiregridPanel(rs);
        renderRmlUiPanel(rs);
        renderGizmoPanel(rs);
        renderPerformancePanel(rs, cpuFrameMs);
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
