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
#include <charconv>
#include <cmath>
#include <csignal>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <optional>
#include <string_view>
#include <system_error>

#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/boolean.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>

#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/geometric.hpp>
#include <glm/trigonometric.hpp>

// C++ system headers
#include <array>
#include <exception>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <ostream>
#include <stdexcept>
#include <string>
#include <thread>
#include <vector>

// Third-party library headers
#include "constants.h"
#include "kerr.h"
#include "page_thorne.h"
#include "schwarzschild.h"
#ifndef BLACKHOLE_HAS_CPPTRACE
#if __has_include(<cpptrace/cpptrace.hpp>)
// Preprocessor guards select declarations and code for the configured build.
#define BLACKHOLE_HAS_CPPTRACE 1 // NOLINT(cppcoreguidelines-macro-usage)
#else
// Preprocessor guards select declarations and code for the configured build.
#define BLACKHOLE_HAS_CPPTRACE 0 // NOLINT(cppcoreguidelines-macro-usage)
#endif
#endif
#if BLACKHOLE_HAS_CPPTRACE
#include <cpptrace/basic.hpp>
#include <cpptrace/exceptions.hpp>
#include <cpptrace/forward.hpp>
#include <cpptrace/utils.hpp>
#endif
#include <GLFW/glfw3.h>
#include <imgui.h>
#include <imgui_internal.h>
#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

// ImGuizmo declarations require the ImGui types above.
#include <ImGuizmo.h>
#include <implot.h>

#include <glm/gtc/type_ptr.hpp>

// Local headers
#include <stb_image_write.h>

#include "GLDebugMessageCallback.h"
#include "cinematic.h"
#include "game/campaign_session.h"
#include "grmhd_packed_loader.h"
#include "grmhd_pbo_uploader.h"
#include "hud_overlay.h"
#include "imgui_impl_glfw.h"
#include "imgui_impl_opengl3.h"
#include "input.h"
#include "overlay.h"
#include "physics/hawking_renderer.h"
#include "platform/cli_options.h"
#include "platform/crash_handler.h"
#include "platform/resource_paths.h"
#include "render.h"
#include "render/background_loader.h"
#include "render/camera_math.h"
#include "render/compare_sweep.h"
#include "render/env_config.h"
#include "render/gl_capabilities.h"
#include "render/gpu_timing.h"
#include "render/grmhd_tile_upload.h"
#include "render/interop_uniforms.h"
#include "render/lut_manager.h"
#include "render/noise_texture_cache.h"
#include "render/post_pipeline.h"
#include "render/post_process.h"
#include "render/record_mode.h"
#include "render/render_state.h"
#include "render/renderer_contract.h"
#include "render/terminal_counts.h"
#include "../shader/include/ray_terminal.h"
#include "render/render_targets.h"
#include "render/scene_overlays.h"
#include "render/settings_sync.h"
#include "render/observer_sky_view.h"
#include "render/tesseract/tesseract_renderer.h"
#include "render/uniform_binding.h"
#include "rmlui_overlay.h"
#include "settings.h"
#include "shader.h"
#include "shader_manager.h"
#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
#include "shader_watcher.h"
#endif
#include "texture.h"
#include "tracy_support.h"
#include "ui/campaign_panels.h"
#include "ui/constellation_panels.h"
#include "ui/observer_panels.h"
#include "ui/panels.h"
#include "ui/settings_window.h"

#ifndef BLACKHOLE_HAS_CUDA
#define BLACKHOLE_HAS_CUDA 0
#endif
#ifndef BLACKHOLE_APP_VARIANT_GLSL_ONLY
// Preprocessor guards select declarations and code for the configured build.
#define BLACKHOLE_APP_VARIANT_GLSL_ONLY 0 // NOLINT(cppcoreguidelines-macro-usage)
#endif
#ifndef BLACKHOLE_APP_VARIANT_CUDA_ONLY
// Preprocessor guards select declarations and code for the configured build.
#define BLACKHOLE_APP_VARIANT_CUDA_ONLY 0 // NOLINT(cppcoreguidelines-macro-usage)
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

namespace {

constexpr bool K_APP_VARIANT_GLSL_ONLY = BLACKHOLE_APP_VARIANT_GLSL_ONLY != 0;
constexpr bool K_APP_VARIANT_CUDA_ONLY = BLACKHOLE_APP_VARIANT_CUDA_ONLY != 0;
constexpr const char *windowTitle() {
  if (K_APP_VARIANT_CUDA_ONLY) {
    return "BlackholeCUDA";
  }
  return K_APP_VARIANT_GLSL_ONLY ? "BlackholeGLSL" : "Blackhole";
}

// Module imports name the lifecycle operations used by the application loop.
using blackhole::appendGpuTimingSample;
using blackhole::gpuTimingPath;
using blackhole::PostProcessPass;
using platform::resourcePath;

// Camera pose math lives in src/render/camera_math.*.
using blackhole::buildCameraBasis;
using blackhole::selectCameraPosition;

// Settings <-> RenderState load-once and write-back live in src/render/settings_sync.*.
using blackhole::loadSettingsIntoRenderState;
using blackhole::syncRenderStateToSettings;

// Bloom/tonemap/depth post chain lives in src/render/post_pipeline.*.
using blackhole::runPostProcessPipeline;

// Per-frame GRMHD PBO tile upload lives in src/render/grmhd_tile_upload.*.
using blackhole::uploadGrmhdStreamingTiles;

// Scene-composition overlay passes live in src/render/scene_overlays.*.
using blackhole::composeSceneOverlays;

// Startup env-var configuration lives in src/render/env_config.*.
using blackhole::applyEnvironmentConfig;

// Render-target lifecycle lives in src/render/render_targets.*.
using blackhole::recreateRenderTargets;

// Compare-sweep advance/restore state machine lives in src/render/compare_sweep.*.
using blackhole::captureCompareParity;
using blackhole::CompareParityInputs;
using blackhole::restoreCompareSweepState;
using blackhole::updateComparePresetSweep;

// Speculative tesseract scene pass lives in src/render/tesseract/*.
using blackhole::renderTesseractScene;
using blackhole::tesseractFocusTangent;
using blackhole::TesseractRecordFrame;
using blackhole::tesseractViewDistanceAfterInput;

// Observer-sky scene pass lives in src/render/observer_sky_view.*.
using blackhole::renderObserverSkyScene;

// GL feature queries live in src/render/gl_capabilities.*.
using blackhole::hasExtension;

// BackgroundAsset, WiregridParams, K_BACKGROUND_LAYERS, K_MAX_BLOOM_ITERATIONS,
// and RenderState live in src/render/render_state.h.
using blackhole::K_BACKGROUND_LAYERS;
using blackhole::RenderState;
using blackhole::RenderBackend;
using blackhole::rendererStepBudget;
using blackhole::rendererStepSize;
using blackhole::WiregridParams;

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
using ui::renderBackgroundPanel;
using ui::renderControlsHelpPanel;
using ui::renderControlsSettingsPanel;
using ui::renderCurveOverlayWindow;
using ui::renderDisplaySettingsPanel;
using ui::renderGizmoPanel;
using ui::renderPerformancePanel;
using ui::renderRmlUiPanel;
using ui::renderSettingsWindow;
using ui::renderTesseractPanel;
using ui::renderWiregridPanel;
using ui::resetLayout;

// Background manifest parsing + active-texture swap lives in
// src/render/background_loader.*.
using blackhole::updateActiveBackground;

// Compare/parity harness (DiffStats, preset table) lives in
// src/tools/compare_harness.*; InteropUniforms in
// src/render/interop_uniforms.h. The snapshot + CSV writers are reached
// through captureCompareParity in render/compare_sweep.*.
using blackhole::InteropUniforms;

// Shared raytracer uniform binders live in src/render/uniform_binding.*
// (registry-driven fragment/compute float fills + Hawking forwarder).
using blackhole::applyHawkingUniforms;
using blackhole::applyInteropComputeUniforms;
using blackhole::bindComputeUniforms;
using blackhole::bindFragmentUniforms;
using blackhole::FrameBindingInputs;

// Radiative-transfer LUT lifecycle lives in src/render/lut_manager.*.
using blackhole::loadGrbModulationLut;
using blackhole::loadSpectralSynchHawkingLuts;
using blackhole::updateLuts;

// Showcase-orbit record framing lives in src/render/record_mode.*.
using blackhole::applyRecordCameraPath;
using blackhole::applyRecordProfileSetup;
using blackhole::applyShowcaseBeautyWiregridTuning;
using blackhole::captureRecordFrame;
using blackhole::exportFrameOnce;
using blackhole::findShowcaseOrbitComposition;
using blackhole::frameContentSeconds;
using blackhole::observerCaptureClock;
using blackhole::recordOutputSeconds;
using blackhole::ShowcaseOrbitComposition;
#if BLACKHOLE_HAS_CUDA
using blackhole::bindCudaLaunchParams;
#endif

void glfwErrorCallback(int error, const char *description) {
  (void)std::fprintf(stderr, "Glfw Error %d: %s\n", error,
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
    const std::string_view configuredThreads(threadEnv);
    unsigned int requestedThreads = 0;
    const auto result =
        std::from_chars(configuredThreads.data(),
                        configuredThreads.data() + configuredThreads.size(), requestedThreads);
    if (result.ec != std::errc{} ||
        result.ptr != configuredThreads.data() + configuredThreads.size() ||
        requestedThreads == 0) {
      throw std::invalid_argument("BLACKHOLE_SHADER_COMPILE_THREADS requires a positive integer");
    }
    threads = requestedThreads;
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

  GLFWwindow *window = glfwCreateWindow(width, height, windowTitle(), nullptr, nullptr);
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
    (void)std::fprintf(stderr, "OpenGL 4.6 required, found %d.%d\n", glMajor,
                       glMinor); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    glfwDestroyWindow(window);
    return nullptr;
  }

  // Initialize GL debug context after loader init
  initializeGLDebugContext();
  configureParallelShaderCompile();

  return window;
}

void sizeWorkspaceFramebuffer(GLFWwindow *window, int framebufferWidth, int framebufferHeight) {
  int windowWidth = 0;
  int windowHeight = 0;
  int actualWidth = 0;
  int actualHeight = 0;
  glfwGetWindowSize(window, &windowWidth, &windowHeight);
  glfwGetFramebufferSize(window, &actualWidth, &actualHeight);
  if (actualWidth <= 0 || actualHeight <= 0) {
    throw std::runtime_error("Workspace framebuffer has zero size");
  }
  if (actualWidth != framebufferWidth || actualHeight != framebufferHeight) {
    const int logicalWidth = static_cast<int>(std::lround(
        static_cast<double>(framebufferWidth) * windowWidth / actualWidth));
    const int logicalHeight = static_cast<int>(std::lround(
        static_cast<double>(framebufferHeight) * windowHeight / actualHeight));
    glfwSetWindowSize(window, logicalWidth, logicalHeight);
    glfwPollEvents();
  }
  glfwGetFramebufferSize(window, &actualWidth, &actualHeight);
  if (actualWidth != framebufferWidth || actualHeight != framebufferHeight) {
    throw std::runtime_error("GLFW cannot provide the requested workspace framebuffer size");
  }
}

// Configure custom ImGui style for "Blackhole" theme (16-bit Voxel Aesthetic)

// Cleanup resources. saveSettings is false for a record run: its profile
// writes post, background and camera state that belong to the capture, and
// saving would carry them into the interactive settings.json.
void cleanup(GLFWwindow *window, bool saveSettings) {
  if (saveSettings) {
    InputManager::instance().syncToSettings();
    SettingsManager::instance().save();
  }

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

float recordOverride(bool hasValue, float value, float defaultValue) {
  return hasValue ? value : defaultValue;
}

std::array<ui::CampaignBackdrop, 5> loadCampaignBackdrops(GLFWwindow *window) {
  int campaignFbW = 0;
  int campaignFbH = 0;
  glfwGetFramebufferSize(window, &campaignFbW, &campaignFbH);
  const auto ladderRendition = [campaignFbW, campaignFbH](const char *basename) -> std::string {
    const std::string dir = std::string("assets/backgrounds/generated/") + basename + "-";
    const double aspect = campaignFbH > 0 ? static_cast<double>(campaignFbW) / campaignFbH : 1.78;
    if (aspect > 2.1) {
      return dir + (campaignFbH >= 1200 ? "ultrawide-3440x1440.jpg" : "ultrawide-2560x1080.jpg");
    }
    if (campaignFbW >= 2000) {
      return dir + "2k.jpg";
    }
    if (campaignFbW >= 1000) {
      return dir + "1024.jpg";
    }
    return dir + "512.jpg";
  };
  const char *const nasaCredit = "NASA, ESA, CSA, STScI";
  const std::array<ui::CampaignBackdrop, 5> campaignBackdrops = {{
      {.name = "Cosmic Cliffs (Carina)",
       .textureId = loadTexture2D(resourcePath(ladderRendition("carina-cosmic-cliffs"))),
       .credit = nasaCredit},
      {.name = "Crab Nebula",
       .textureId = loadTexture2D(resourcePath(ladderRendition("crab-nebula"))),
       .credit = nasaCredit},
      {.name = "Southern Ring Nebula",
       .textureId =
           loadTexture2D(resourcePath("assets/backgrounds/source/southern-ring-nebula-2k.jpg")),
       .credit = nasaCredit},
      {.name = "Cartwheel Galaxy",
       .textureId =
           loadTexture2D(resourcePath("assets/backgrounds/source/cartwheel-galaxy-2k.jpg")),
       .credit = nasaCredit},
      {.name = "Starfield (procedural)", .textureId = 0U, .credit = ""},
  }};
  return campaignBackdrops;
}

/**
 * @brief Run InputManager::update for the active scene.
 *
 * The tesseract scene takes zoom input for its own view distance
 * (tesseractZoom), so the black-hole camera keeps its orbit radius; a
 * recording frames the tesseract from the record camera and drops the zoom.
 * Reset Camera returns that distance to its default with the camera pose in
 * either scene (tesseractViewDistanceAfterInput).
 */
void updateInput(RenderState &rs, const platform::CliOptions &cli, InputManager &input,
                 float deltaTime) {
  const bool tesseractActive = rs.scene.mode == RenderState::SceneMode::Tesseract;
  input.setZoomRedirect(tesseractActive);
  input.update(deltaTime);
  const float zoomDelta = input.takeZoomDelta();
  const bool cameraReset = input.takeCameraReset();
  if (cameraReset || (tesseractActive && cli.recordFramesDir.empty())) {
    rs.tesseract.viewDistance =
        tesseractViewDistanceAfterInput(rs.tesseract.viewDistance, zoomDelta, cameraReset);
  }
}

void updateFrameTiming(RenderState &rs, float cpuFrameMs) {
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
    // A stage the sampled frame skipped plots nothing rather than its last value.
    // TRACY_PLOT expands to nothing without Tracy, leaving name unread.
    const auto plot = []([[maybe_unused]] const char *name, const blackhole::GpuTimer &timer) {
      if (timer.hasSample) {
        TRACY_PLOT(name, timer.lastMs);
      }
    };
    const blackhole::GpuTimerSet &timers = rs.timing.gpuTimers;
    plot("gpu_fragment_ms", timers.blackholeFragment);
    plot("gpu_compute_ms", timers.blackholeCompute);
    plot("gpu_bloom_ms", timers.bloom);
    plot("gpu_tonemap_ms", timers.tonemap);
    plot("gpu_depth_ms", timers.depth);
    plot("gpu_grmhd_slice_ms", timers.grmhdSlice);
    plot("gpu_tesseract_ms", timers.tesseract);
  }
}

void updateRmlUiOverlay(RenderState &rs, GLFWwindow *window, int windowWidth, int windowHeight) {
  if (rs.overlays.rmluiEnabled) {
    if (!rs.overlays.rmluiReady) {
      rs.overlays.rmluiReady = rs.overlays.rmluiOverlay.init(window, windowWidth, windowHeight);
    }
    if (rs.overlays.rmluiReady &&
        (windowWidth != rs.overlays.rmluiWidth || windowHeight != rs.overlays.rmluiHeight)) {
      rs.overlays.rmluiOverlay.resize(windowWidth, windowHeight);
      rs.overlays.rmluiWidth = windowWidth;
      rs.overlays.rmluiHeight = windowHeight;
    }
  } else if (rs.overlays.rmluiReady) {
    rs.overlays.rmluiOverlay.shutdown();
    rs.overlays.rmluiReady = false;
  }
}

void configureFrameBackground(RenderState &rs, const platform::CliOptions &cli) {
  if (!rs.background.baseTexturesLoaded) {
    if (cli.referenceScene.empty()) {
      rs.background.galaxy = loadCubemap(resourcePath("assets/skybox_nebula_dark"));
    }
    rs.background.colorMap = loadTexture2D(resourcePath("assets/color_map.png"));
    rs.background.baseTexturesLoaded = true;
  }
  if (!cli.recordFramesDir.empty() && cli.recordProfile == "showcase-orbit") {
    const ShowcaseOrbitComposition *const composition =
        findShowcaseOrbitComposition(cli.recordComposition);
    rs.background.backgroundLayerScale = {1.0f, 1.18f, 1.42f};
    rs.background.backgroundLayerIntensity = {1.0f, 0.94f, 0.72f};
    rs.background.backgroundLayerLodBias = {0.45f, 1.2f, 1.9f};
    rs.background.backgroundLayerGlobalOffset =
        composition != nullptr
            ? glm::vec2(composition->backgroundOffsetX, composition->backgroundOffsetY)
            : glm::vec2(0.0f);
    rs.background.backgroundYawRad =
        glm::radians(recordOverride(cli.hasRecordBackgroundYaw, cli.recordBackgroundYawDeg,
                                    composition != nullptr ? composition->backgroundYawDeg : 0.0f));
    rs.background.backgroundPitchRad = glm::radians(
        recordOverride(cli.hasRecordBackgroundPitch, cli.recordBackgroundPitchDeg,
                       composition != nullptr ? composition->backgroundPitchDeg : 0.0f));
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
}

void initializeExportDebugStage(RenderState &rs) {
  if (!rs.debug.debugPreShapingBackgroundEnvApplied) {
    if (const char *stage = std::getenv("BLACKHOLE_EXPORT_RAW_STAGE")) {
      rs.debug.debugPreRedshiftBackground = (std::strcmp(stage, "pre-redshift-background") == 0);
      rs.debug.debugPreShapingBackground = (std::strcmp(stage, "pre-shaping-background") == 0);
      rs.debug.debugPostShapingBackground = (std::strcmp(stage, "post-shaping-background") == 0);
      rs.debug.debugShaperInputs = (std::strcmp(stage, "shaper-inputs") == 0);
      rs.debug.debugClosestApproachState = (std::strcmp(stage, "closest-approach-state") == 0);
      rs.debug.debugClosestApproachTimeline =
          (std::strcmp(stage, "closest-approach-timeline") == 0);
      rs.debug.debugClosestApproachDirection =
          (std::strcmp(stage, "closest-approach-direction") == 0);
      rs.debug.debugEscapedDirection = (std::strcmp(stage, "escaped-direction") == 0);
    }
    rs.debug.debugPreShapingBackgroundEnvApplied = true;
  }
}

void initializeWiregridEnvironment(RenderState &rs) {
  if (!rs.wiregrid.wiregridEnvApplied) {
    auto parseEnvFloat = [](const char *name, float &out) {
      if (const char *value = std::getenv(name)) {
        char *end = nullptr;
        const float parsed = std::strtof(value, &end);
        if (end != value) {
          out = parsed;
        }
      }
    };
    if (const char *enabled = std::getenv("BLACKHOLE_WIREGRID_ENABLED")) {
      rs.wiregrid.wiregridEnabled = (std::strcmp(enabled, "0") != 0);
    }
    applyWiregridModeProfile(WiregridParams::Mode::Beauty, rs.wiregrid.wiregridParams,
                             rs.wiregrid.wiregridColor);
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
}

void dispatchComputeFrame(RenderState &rs, GLuint computeTarget, GLuint &computeProgram,
                          const InteropUniforms &interop, const FrameBindingInputs &frameInputs) {
  if (computeProgram == 0) {
    computeProgram = createComputeProgram(std::string("shader/geodesic_trace.comp"));
  }

  glUseProgram(computeProgram);
  applyInteropComputeUniforms(computeProgram, interop, rs.targets.renderWidth,
                              rs.targets.renderHeight);
  glUniform1f(glGetUniformLocation(computeProgram, "terminalWriteEnabled"),
              computeTarget == rs.targets.texBlackhole ? 1.0f : 0.0f);
  glUniform1f(glGetUniformLocation(computeProgram, "terminalDebugEnabled"),
              rs.terminalDiagnostics.showDebugView ? 1.0f : 0.0f);

  // Apply Hawking radiation uniforms
  double const bhMass = static_cast<double>(rs.physicsCore.blackHoleMass) * physics::M_SUN;
  applyHawkingUniforms(computeProgram, rs.hawking.hawkingRenderer, rs.hawking.hawkingGlowEnabled,
                       rs.hawking.hawkingTempScale, rs.hawking.hawkingGlowIntensity,
                       rs.hawking.hawkingUseLUTs, bhMass);

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
        auto const groupsX = static_cast<GLuint>((tileWidth + kGroupSize - 1) / kGroupSize);
        auto const groupsY = static_cast<GLuint>((tileHeight + kGroupSize - 1) / kGroupSize);
        glDispatchCompute(groupsX, groupsY, 1);
        glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
      }
    }
  } else {
    if (tileOffsetLoc != -1) {
      glUniform2i(tileOffsetLoc, 0, 0);
    }
    auto const groupsX =
        static_cast<GLuint>((rs.targets.renderWidth + kGroupSize - 1) / kGroupSize);
    auto const groupsY =
        static_cast<GLuint>((rs.targets.renderHeight + kGroupSize - 1) / kGroupSize);
    glDispatchCompute(groupsX, groupsY, 1);
    glMemoryBarrier(GL_SHADER_IMAGE_ACCESS_BARRIER_BIT);
  }
  glUseProgram(0);
}

void renderGlslFrame(RenderState &rs, RenderToTextureInfo &rtti, GLuint &computeProgram,
                     const InteropUniforms &interop, const FrameBindingInputs &frameInputs,
                     bool computeActive, bool compareBaselineActive, float grbTimeSeconds) {
  const bool compareActive = frameInputs.compareActive;
  const bool backgroundEnabledEffective = frameInputs.backgroundEnabledEffective;
  const bool noiseReady = frameInputs.noiseReady;
  const bool grmhdEnabled = frameInputs.grmhdEnabled;
  const bool spectralEnabled = frameInputs.spectralEnabled;
  const bool grbModulationEnabled = frameInputs.grbModulationEnabled;
  const bool enablePhotonSphereEffective = frameInputs.enablePhotonSphereEffective;
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
  auto &terminals = rs.terminalDiagnostics;
  if (terminals.codesBuffer != 0) {
    constexpr std::uint32_t unwrittenCode = BH_TERMINAL_OUTSIDE_DOMAIN;
    glClearNamedBufferData(terminals.codesBuffer, GL_R32UI, GL_RED_INTEGER, GL_UNSIGNED_INT,
                           &unwrittenCode);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 7, terminals.codesBuffer);
    glBindImageTexture(1, terminals.debugTexture, 0, GL_FALSE, 0, GL_WRITE_ONLY, GL_RGBA8);
  }
  if (rs.timing.gpuTimers.initialized && fragmentTarget != 0) {
    rs.timing.gpuTimers.blackholeFragment.begin();
  }
  if (fragmentTarget != 0) {
    ZONE_SCOPED_N("Blackhole Fragment");
    rtti.targetTexture = fragmentTarget;
    rtti.floatUniforms["terminalWriteEnabled"] =
        fragmentTarget == rs.targets.texBlackhole ? 1.0f : 0.0f;
    rtti.floatUniforms["terminalDebugEnabled"] = terminals.showDebugView ? 1.0f : 0.0f;
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
    dispatchComputeFrame(rs, computeTarget, computeProgram, interop, frameInputs);
  }
  if (rs.timing.gpuTimers.initialized && computeTarget != 0) {
    rs.timing.gpuTimers.blackholeCompute.end();
  }
  if (terminals.codesBuffer != 0 && !terminals.codes.empty()) {
    glMemoryBarrier(GL_ALL_BARRIER_BITS);
    glGetNamedBufferSubData(terminals.codesBuffer, 0,
                            static_cast<GLsizeiptr>(terminals.codes.size() * sizeof(std::uint32_t)),
                            terminals.codes.data());
    terminals.counts = blackhole::foldTerminalCodes(terminals.codes);
    terminals.valid = true;
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 7, 0);
    glBindImageTexture(1, 0, 0, GL_FALSE, 0, GL_WRITE_ONLY, GL_RGBA8);
  }

  CompareParityInputs parityInputs;
  parityInputs.fragmentTarget = fragmentTarget;
  parityInputs.computeTarget = computeTarget;
  parityInputs.compareActive = compareActive;
  parityInputs.compareBaselineActive = compareBaselineActive;
  parityInputs.backgroundEnabledEffective = backgroundEnabledEffective;
  parityInputs.noiseReady = noiseReady;
  parityInputs.grmhdEnabled = grmhdEnabled;
  parityInputs.spectralEnabled = spectralEnabled;
  parityInputs.grbModulationEnabled = grbModulationEnabled;
  parityInputs.enablePhotonSphereEffective = enablePhotonSphereEffective;
  parityInputs.grbTimeSeconds = grbTimeSeconds;
  parityInputs.timeSec = glfwGetTime();
  parityInputs.interop = interop;
  captureCompareParity(rs, parityInputs);
}

struct RenderDispatchOptions {
  bool computeActive;
  bool compareActive;
  bool compareBaselineActive;
  bool adiskEnabledEffective;
  bool adiskParticleEffective;
  bool enableRedshiftEffective;
  bool useNoiseTextureEffective;
  bool useGrmhdEffective;
  bool useSpectralLutEffective;
  bool useGrbModulationEffective;
  bool enablePhotonSphereEffective;
  bool backgroundEnabledEffective;
  int compareSteps;
  float compareStepSize;
};
RenderDispatchOptions deriveRenderDispatch(RenderState &rs, const Settings &settings) {
  blackhole::normalizeRendererContract(rs.dispatch.contract);
  bool const computeSupported = ShaderManager::instance().canUseComputeShaders();
  bool const computeActive = rs.dispatch.contract.backend == RenderBackend::Compute && computeSupported;
  bool const compareActive =
      rs.compare.compareComputeFragment && computeSupported && !K_APP_VARIANT_CUDA_ONLY;
  bool const compareBaselineActive = rs.compare.compareBaselineEnabled && compareActive;
  bool const adiskEnabledEffective = rs.disk.adiskEnabled && !compareBaselineActive &&
      rs.dispatch.contract.radiative != blackhole::RadiativeModel::BackgroundOnly;
  bool const adiskParticleEffective = rs.disk.adiskParticle && !compareBaselineActive;
  bool const enableRedshiftEffective = rs.physicsCore.enableRedshift && !compareBaselineActive;
  bool const useNoiseTextureEffective = rs.disk.useNoiseTexture && !compareBaselineActive;
  bool const useGrmhdEffective = rs.grmhd.useGrmhd && !compareBaselineActive;
  bool const useSpectralLutEffective = rs.luts.useSpectralLut && !compareBaselineActive;
  bool const useGrbModulationEffective = rs.luts.useGrbModulation && !compareBaselineActive;
  bool const enablePhotonSphereEffective =
      rs.physicsCore.enablePhotonSphere && !compareBaselineActive;
  bool const backgroundEnabledEffective = settings.backgroundEnabled && !compareBaselineActive;

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
  int compareSteps = rendererStepBudget(rs.dispatch.contract.quality, rs.dispatch.computeMaxSteps,
                                         rs.dispatch.computeStepSize);
  float compareStepSize = rendererStepSize(rs.dispatch.contract.quality, rs.dispatch.computeStepSize);
  if (rs.compare.compareOverridesEnabled) {
    if (rs.compare.compareMaxStepsOverride > 0) {
      compareSteps = rs.compare.compareMaxStepsOverride;
    }
    if (rs.compare.compareStepSizeOverride > 0.0f) {
      compareStepSize = rs.compare.compareStepSizeOverride;
    }
  }

  return {.computeActive = computeActive,
          .compareActive = compareActive,
          .compareBaselineActive = compareBaselineActive,
          .adiskEnabledEffective = adiskEnabledEffective,
          .adiskParticleEffective = adiskParticleEffective,
          .enableRedshiftEffective = enableRedshiftEffective,
          .useNoiseTextureEffective = useNoiseTextureEffective,
          .useGrmhdEffective = useGrmhdEffective,
          .useSpectralLutEffective = useSpectralLutEffective,
          .useGrbModulationEffective = useGrbModulationEffective,
          .enablePhotonSphereEffective = enablePhotonSphereEffective,
          .backgroundEnabledEffective = backgroundEnabledEffective,
          .compareSteps = compareSteps,
          .compareStepSize = compareStepSize};
}

struct BlackholeFrameResult {
  bool grmhdReady = false;
  bool computeActiveForLog = false;
};

BlackholeFrameResult renderBlackholeFrame(RenderState &rs, const Settings &settings,
                                          const glm::vec3 &cameraPos, const glm::mat3 &cameraBasis,
                                          float fovScale, float frameTime, double currentTime,
                                          GLuint &computeProgram) {
  bool computeActiveForLog = false;
  uploadGrmhdStreamingTiles(rs);

  /* grmhdReady: true when packed texture OR PBO streaming path is valid. */
  bool const grmhdReady = (rs.grmhd.grmhdLoaded && rs.grmhd.grmhdTexture.texture != 0) ||
                          (rs.grmhd.grmhdTimeSeriesLoaded && rs.grmhd.grmhdPboUploader.ready());
  /* grmhdTexId: prefer PBO streaming texture when the streamer is running;
   * fall back to the packed static texture otherwise. */
  GLuint const grmhdTexId = (rs.grmhd.grmhdTimeSeriesLoaded && rs.grmhd.grmhdPboUploader.ready())
                                ? rs.grmhd.grmhdPboUploader.texture()
                                : rs.grmhd.grmhdTexture.texture;
  bool const spectralReady = rs.luts.spectralLutLoaded && rs.luts.texSpectralLUT != 0;
  rs.luts.spectralRadiusMin = std::max(0.0f, rs.luts.spectralRadiusMin);
  rs.luts.spectralRadiusMax =
      std::max(rs.luts.spectralRadiusMax, rs.luts.spectralRadiusMin + 0.001f);

  loadGrbModulationLut(rs);
  bool const grbModulationReady = rs.luts.grbModulationLoaded && rs.luts.texGrbModulationLUT != 0;
  float const grbSpan = std::max(rs.luts.grbTimeMax - rs.luts.grbTimeMin, 0.001f);
  float grbTimeSeconds = 0.0f;
  if (grbModulationReady) {
    if (rs.luts.grbTimeManual) {
      grbTimeSeconds =
          std::clamp(rs.luts.grbTimeManualValue, rs.luts.grbTimeMin, rs.luts.grbTimeMax);
    } else {
      grbTimeSeconds = rs.luts.grbTimeMin + std::fmod(static_cast<float>(currentTime), grbSpan);
    }
  }

  bool const lutReady = rs.luts.texEmissivityLUT != 0 && rs.luts.texRedshiftLUT != 0;

  {
    RenderToTextureInfo rtti;
    rtti.fragShader = "shader/blackhole_main.frag";
    rtti.cubemapUniforms["galaxy"] =
        rs.background.galaxy != 0 ? rs.background.galaxy : rs.background.fallbackCubemap;
    rtti.textureUniforms["colorMap"] =
        rs.background.colorMap != 0 ? rs.background.colorMap : rs.background.fallback2D;
    rtti.textureUniforms["emissivityLUT"] =
        lutReady ? rs.luts.texEmissivityLUT : rs.background.fallback2D;
    rtti.textureUniforms["redshiftLUT"] =
        lutReady ? rs.luts.texRedshiftLUT : rs.background.fallback2D;
    rtti.textureUniforms["photonGlowLUT"] =
        rs.luts.texPhotonGlowLUT != 0 ? rs.luts.texPhotonGlowLUT : rs.background.fallback2D;
    rtti.textureUniforms["diskDensityLUT"] =
        rs.luts.texDiskDensityLUT != 0 ? rs.luts.texDiskDensityLUT : rs.background.fallback2D;
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

    const float effectiveSpin =
        rs.dispatch.contract.geodesic == blackhole::GeodesicModel::SchwarzschildReference
            ? 0.0f : rs.physicsCore.kerrSpin;
    updateLuts(rs, effectiveSpin, rs.disk.adiskDensityV);
    loadSpectralSynchHawkingLuts(rs);

    const double referenceMass = physics::M_SUN;
    const double referenceRs = physics::schwarzschildRadius(referenceMass);
    const double referenceRg = physics::G * referenceMass / physics::C2;
    const double referenceA = static_cast<double>(effectiveSpin) * referenceRg;
    // The disk orbits along +z; a negative kerrSpin makes that orbit counter-rotate.
    const double iscoRatio = physics::kerrIscoRadius(referenceMass, referenceA, true) / referenceRs;

    float const schwarzschildRadius = 2.0f * rs.physicsCore.blackHoleMass;
    float const iscoRadius = static_cast<float>(iscoRatio) * schwarzschildRadius;
    // Keep record-mode copies accessible outside this inner block
    rs.recording.recordCurRs = schwarzschildRadius;
    rs.recording.recordCurIsco = iscoRadius;
#if BLACKHOLE_HAS_CUDA
    if (K_APP_VARIANT_CUDA_ONLY) {
      rs.dispatch.contract.backend = RenderBackend::Cuda;
      rs.compare.compareComputeFragment = false;
    }
    rs.dispatch.cudaManager.setEnabled(rs.dispatch.contract.backend == RenderBackend::Cuda);
#endif
    const auto dispatch = deriveRenderDispatch(rs, settings);
    const auto computeActive = dispatch.computeActive;
    const auto compareActive = dispatch.compareActive;
    const auto compareBaselineActive = dispatch.compareBaselineActive;
    const auto adiskEnabledEffective = dispatch.adiskEnabledEffective;
    const auto adiskParticleEffective = dispatch.adiskParticleEffective;
    const auto enableRedshiftEffective = dispatch.enableRedshiftEffective;
    const auto useNoiseTextureEffective = dispatch.useNoiseTextureEffective;
    const auto useGrmhdEffective = dispatch.useGrmhdEffective;
    const auto useSpectralLutEffective = dispatch.useSpectralLutEffective;
    const auto useGrbModulationEffective = dispatch.useGrbModulationEffective;
    const auto enablePhotonSphereEffective = dispatch.enablePhotonSphereEffective;
    const auto backgroundEnabledEffective = dispatch.backgroundEnabledEffective;
    const auto compareSteps = dispatch.compareSteps;
    const auto compareStepSize = dispatch.compareStepSize;
    computeActiveForLog = computeActive;

    const bool grmhdEnabled = useGrmhdEffective && grmhdReady;
    const bool spectralEnabled = useSpectralLutEffective && spectralReady;
    const bool grbModulationEnabled = useGrbModulationEffective && grbModulationReady;
    bool const noiseReady = useNoiseTextureEffective && rs.disk.texNoiseVolume != 0;

    InteropUniforms interop;
    interop.cameraPos = cameraPos;
    interop.cameraBasis = cameraBasis;
    interop.fovScale = fovScale;
    interop.timeSec = frameTime;
    interop.schwarzschildRadius = schwarzschildRadius;
    interop.iscoRadius = iscoRadius;
    interop.kerrSpin = effectiveSpin;
    interop.depthFar = rs.display.depthFar;
    if (compareActive) {
      interop.maxSteps = compareSteps;
      interop.stepSize = compareStepSize;
    } else {
      interop.maxSteps = rendererStepBudget(rs.dispatch.contract.quality, rs.dispatch.computeMaxSteps,
                                         rs.dispatch.computeStepSize);
      interop.stepSize = rendererStepSize(rs.dispatch.contract.quality, rs.dispatch.computeStepSize);
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
    // Volumetric radiative transfer
    interop.rteEnabled = rs.dispatch.contract.radiative == blackhole::RadiativeModel::VolumetricRte
                             ? 1.0f : 0.0f;
    interop.rteOpacityScale = rs.rte.rteOpacityScale;
    interop.debugPreRedshiftBackground = rs.debug.debugPreRedshiftBackground ? 1.0f : 0.0f;
    interop.debugPreShapingBackground = rs.debug.debugPreShapingBackground ? 1.0f : 0.0f;
    interop.debugPostShapingBackground = rs.debug.debugPostShapingBackground ? 1.0f : 0.0f;
    interop.debugShaperInputs = rs.debug.debugShaperInputs ? 1.0f : 0.0f;
    interop.debugClosestApproachState = rs.debug.debugClosestApproachState ? 1.0f : 0.0f;
    interop.debugClosestApproachTimeline = rs.debug.debugClosestApproachTimeline ? 1.0f : 0.0f;
    interop.debugClosestApproachDirection = rs.debug.debugClosestApproachDirection ? 1.0f : 0.0f;
    interop.debugEscapedDirection = rs.debug.debugEscapedDirection ? 1.0f : 0.0f;
    interop.diskPeakTemperature = rs.disk.diskPeakTemperature;
    interop.diskBrightness = rs.disk.diskBrightness;
    interop.diskTransferMode = static_cast<float>(rs.disk.diskTransferMode);
    // Page-Thorne flux peak at the rendered spin, the normalization of the
    // shaders' flux (the GLSL disk_profile isco_radius clamps to the same range).
    interop.diskFluxPeak = static_cast<float>(physics::pageThorneFluxPeak(
        std::clamp(static_cast<double>(effectiveSpin), -0.9999, 0.9999)));

    // Per-frame derived transients shared by the fragment, CUDA, and
    // compute uniform binders (compare-baseline gating, LUT readiness); see
    // FrameBindingInputs.
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
      rs.dispatch.cudaManager.ensureInit(rs.targets.texBlackhole, rs.targets.renderWidth,
                                         rs.targets.renderHeight);
      if (!wasReady && rs.dispatch.cudaManager.isReady()) {
        /* Register rs.background.galaxy cubemap as CUDA texture object (slot 4 = BhLutGalaxy).
         * Done exactly once on the frame that init first succeeds.
         * Registration failure is non-fatal: kernels fall back to no background. */
        GLuint const galaxyTexForCuda =
            (rs.background.galaxy != 0) ? rs.background.galaxy : rs.background.fallbackCubemap;
        if (galaxyTexForCuda != 0) {
          rs.dispatch.cudaManager.registerLut(4, galaxyTexForCuda,
                                              static_cast<unsigned int>(GL_TEXTURE_CUBE_MAP));
        }
        /* Register the layered desktop background equirect texture so the CUDA
         * lane samples the same 2D scene asset class as the GLSL desktop lane. */
        GLuint const backgroundTexForCuda = (rs.background.backgroundBase != 0)
                                                ? rs.background.backgroundBase
                                                : rs.background.fallback2D;
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

      renderGlslFrame(rs, rtti, computeProgram, interop, frameInputs, computeActive,
                      compareBaselineActive, grbTimeSeconds);
    } /* end of GLSL fragment/compute else block */
  }
  return {.grmhdReady = grmhdReady, .computeActiveForLog = computeActiveForLog};
}

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
void reloadChangedShaders(RenderState &rs, GLuint &computeProgram) {
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

    // The tesseract pass owns its program outside shaderProgramMap.
    rs.tesseract.renderer.reloadShaders();
  }
}
#endif

struct FrameCamera {
  glm::vec3 position{0.0f};
  glm::mat3 basis{1.0f};
  /// Unit direction from the camera to its focus; basis[2] turns from it
  /// toward a showcase-orbit aim point.
  glm::vec3 focusDirection{0.0f, 0.0f, 1.0f};
  float fovScale = 1.0f;
  glm::mat4 projection{1.0f};
  glm::mat4 gizmoView{1.0f};
};

FrameCamera updateFrameCamera(RenderState &rs, InputManager &input, const platform::CliOptions &cli,
                              const Settings &settings, float deltaTime, double currentTime) {
  // Get camera state for shader
  const auto &cam = input.camera();

  glm::vec3 const focusTarget =
      rs.gizmoTargetActive()
          ? glm::vec3(rs.camera.gizmoTransform[3])
          : glm::vec3(
                0.0f); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                       // -- glm::mat has no .at()

  rs.camera.orbitTime += input.getEffectiveDeltaTime(deltaTime);
  const glm::vec3 cameraPos = selectCameraPosition(rs, cam, focusTarget);

  glm::vec3 aimTarget = focusTarget;
  if (!cli.referenceScene.empty()) {
    aimTarget = blackhole::referenceSceneAimTarget(cli.referenceScene, cameraPos, focusTarget);
  }
  if (!cli.recordFramesDir.empty() && cli.recordProfile == "showcase-orbit") {
    const ShowcaseOrbitComposition *const composition =
        findShowcaseOrbitComposition(cli.recordComposition);
    float const frameX = recordOverride(cli.hasRecordFrameX, cli.recordFrameX,
                                        composition != nullptr ? composition->frameOffsetX : 0.0f);
    float const frameY = recordOverride(cli.hasRecordFrameY, cli.recordFrameY,
                                        composition != nullptr ? composition->frameOffsetY : 0.0f);
    if (std::abs(frameX) > 0.0001f || std::abs(frameY) > 0.0001f) {
      glm::mat3 const baseBasis = buildCameraBasis(cameraPos, focusTarget, cam.roll);
      float const halfHeight = std::tan(glm::radians(cam.fov) * 0.5f) * cam.distance;
      float const aspect = static_cast<float>(std::max(rs.targets.renderWidth, 1)) /
                           static_cast<float>(std::max(rs.targets.renderHeight, 1));
      float const halfWidth = halfHeight * aspect;
      aimTarget =
          focusTarget + baseBasis[0] * (frameX * halfWidth) + baseBasis[1] * (frameY * halfHeight);
    }
  }

  glm::mat3 cameraBasis = buildCameraBasis(cameraPos, aimTarget, cam.roll);
  float const fovScale = std::tan(glm::radians(cam.fov) * 0.5f);
  glm::vec2 const parallaxBase =
      glm::vec2(cameraPos.x, cameraPos.y) * settings.backgroundParallaxStrength;
  glm::vec2 const drift = glm::vec2(std::cos(static_cast<float>(currentTime) * 0.02f),
                                    std::sin(static_cast<float>(currentTime) * 0.02f)) *
                          settings.backgroundDriftStrength;
  for (std::size_t i = 0; i < static_cast<std::size_t>(K_BACKGROUND_LAYERS); ++i) {
    glm::vec2 const offset = drift + parallaxBase * rs.background.backgroundLayerDepth.at(i);
    rs.background.backgroundLayerParams.at(i) = glm::vec4(
        offset + rs.background.backgroundLayerGlobalOffset,
        rs.background.backgroundLayerScale.at(i), rs.background.backgroundLayerIntensity.at(i));
  }
  const glm::mat4 projectionMatrix = glm::perspective(
      glm::radians(cam.fov),
      static_cast<float>(rs.targets.renderWidth) / static_cast<float>(rs.targets.renderHeight),
      0.1f, rs.display.depthFar);
  const glm::mat4 gizmoViewMatrix = glm::lookAt(
      cameraPos, aimTarget,
      cameraBasis[1]); // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access)
                       // -- glm::mat has no .at()
  return {.position = cameraPos,
          .basis = cameraBasis,
          .focusDirection = glm::normalize(focusTarget - cameraPos),
          .fovScale = fovScale,
          .projection = projectionMatrix,
          .gizmoView = gizmoViewMatrix};
}

/**
 * @brief Render the active scene into rs.targets.texBlackhole.
 *
 * The black-hole scene runs the geodesic integrator and restores any compare
 * sweep state it changed; the tesseract scene runs its own pass and reports
 * no GRMHD or compute activity.
 */
BlackholeFrameResult renderSceneFrame(RenderState &rs, const platform::CliOptions &cli,
                                      const Settings &settings, InputManager &input,
                                      const FrameCamera &frameCamera, float frameTime,
                                      float deltaTime, double currentTime, GLuint &computeProgram) {
  rs.terminalDiagnostics.valid = false;
  if (rs.scene.mode == RenderState::SceneMode::ObserverSky) {
    // The observer's clock runs on wall time, which pause stops; its own sky
    // time scale replaces the global one, so the panel's rate is the rate. A
    // recording, and a one-shot --export-frame's warmup, run it on a fixed
    // capture clock instead (observerCaptureClock), so neither drifts the
    // exported phase away from BLACKHOLE_OBSERVER_PROPER_SECONDS on wall time.
    std::optional<blackhole::ObserverRecordClock> record;
    if (const auto clock = observerCaptureClock(cli, rs.recording.recordFrameIndex)) {
      record = blackhole::ObserverRecordClock{.outputSeconds = clock->first,
                                              .frameSeconds = clock->second};
    }
    renderObserverSkyScene(rs, frameCamera.basis, input.isPaused() ? 0.0F : deltaTime, record);
    return {};
  }
  if (rs.scene.mode == RenderState::SceneMode::Tesseract) {
    // Recording advances on the output frame clock, frameIndex / fps, so the
    // frames depend on their index alone, not on render throughput, and
    // frames the scene with the camera applyRecordCameraPath set.
    std::optional<TesseractRecordFrame> record;
    if (const auto outputSeconds = recordOutputSeconds(cli, rs.recording.recordFrameIndex)) {
      const auto &recordCamera = input.camera();
      record = TesseractRecordFrame{.outputClockSeconds = *outputSeconds,
                                    .camera = {.fovDeg = recordCamera.fov,
                                               .focusTangent = tesseractFocusTangent(
                                                   frameCamera.basis, frameCamera.focusDirection)}};
    }
    if (rs.timing.gpuTimers.initialized) {
      rs.timing.gpuTimers.tesseract.begin();
    }
    // Interactive frames step by the effective delta, which pause and the
    // time scale govern as they do the black-hole orbit clock.
    renderTesseractScene(rs, frameCamera.basis, frameCamera.focusDirection,
                         input.getEffectiveDeltaTime(deltaTime), record);
    if (rs.timing.gpuTimers.initialized) {
      rs.timing.gpuTimers.tesseract.end();
    }
    return {};
  }
  const auto result =
      renderBlackholeFrame(rs, settings, frameCamera.position, frameCamera.basis,
                           frameCamera.fovScale, frameTime, currentTime, computeProgram);
  restoreCompareSweepState(rs, input);
  return result;
}

void writeWorkspaceLayout(const platform::CliOptions &cli, bool first) {
  nlohmann::json layout;
  const ImGuiViewport *const viewport = ImGui::GetMainViewport();
  layout["workspace"] = cli.workspaceName;
  layout["viewport"] = {viewport->Pos.x, viewport->Pos.y, viewport->Size.x,
                        viewport->Size.y};
  layout["ui_scale"] = cli.uiScale;
  layout["windows"] = nlohmann::json::array();
  // A docked window is rooted at its dock host, and an unselected tab is
  // hidden while its node shows a sibling, so both enter the record through
  // DockIsActive with "visible" telling the selected tab from the others.
  for (const ImGuiWindow *const window : ImGui::GetCurrentContext()->Windows) {
    const bool docked = window->DockIsActive;
    const bool topLevel = window->RootWindow == window &&
                          (window->Flags & ImGuiWindowFlags_ChildWindow) == 0;
    if (window->IsFallbackWindow || !(docked || (topLevel && window->Active))) {
      continue;
    }
    layout["windows"].push_back({{"name", window->Name},
                                  {"position", {window->Pos.x, window->Pos.y}},
                                  {"size", {window->Size.x, window->Size.y}},
                                  {"dock_node_id", window->DockId},
                                  {"visible", window->Active && !window->Hidden},
                                  {"collapsed", window->Collapsed}});
  }
  const std::string path = cli.workspaceScreenshotPath + (first ? ".first.json" : ".json");
  std::ofstream output(path);
  if (!output || !(output << layout.dump(2) << '\n')) {
    throw std::runtime_error("Cannot write workspace layout: " + path);
  }
}

void writeWorkspaceScreenshot(const platform::CliOptions &cli, GLFWwindow *window) {
  int width = 0;
  int height = 0;
  glfwGetFramebufferSize(window, &width, &height);
  if (width != cli.windowWidth || height != cli.windowHeight) {
    throw std::runtime_error("Workspace framebuffer size differs from --window-size");
  }
  const size_t stride = static_cast<size_t>(width) * 4;
  std::vector<unsigned char> pixels(stride * static_cast<size_t>(height));
  std::vector<unsigned char> topDown(pixels.size());
  glPixelStorei(GL_PACK_ALIGNMENT, 1);
  glReadBuffer(GL_BACK);
  glReadPixels(0, 0, width, height, GL_RGBA, GL_UNSIGNED_BYTE, pixels.data());
  glPixelStorei(GL_PACK_ALIGNMENT, 4);
  for (int row = 0; row < height; ++row) {
    std::memcpy(topDown.data() + (static_cast<size_t>(row) * stride),
                pixels.data() + (static_cast<size_t>(height - row - 1) * stride), stride);
  }
  const std::string path = cli.workspaceScreenshotPath + ".png";
  if (stbi_write_png(path.c_str(), width, height, 4, topDown.data(),
                     static_cast<int>(stride)) == 0) {
    throw std::runtime_error("Cannot write workspace screenshot: " + path);
  }
}

bool completeFrame(RenderState &rs, const platform::CliOptions &cli, GLFWwindow *window,
                   const glm::vec3 &cameraPos, float cpuFrameMs, bool computeActiveForLog,
                   bool sceneSettled, int &workspaceCaptureFrame) {
  /* --record-frames: draw cinematic physics HUD via foreground draw list.
   * GetForegroundDrawList() adds to ImGui's draw list, so this must be called
   * before ImGui::Render().  The overlay is composited over the scene by the
   * ImGui backend when RenderDrawData() runs below. Warmup counts only frames
   * that show the scene (sceneCaptureState). */
  if (!cli.recordFramesDir.empty() && sceneSettled) {
    ++rs.recording.recordWarmup;
  }
  if (!cli.recordFramesDir.empty() && cli.recordProfile == "cinematic" &&
      rs.scene.mode == RenderState::SceneMode::Blackhole && rs.recording.recordWarmup >= 15) {
    renderCinematicOverlay(rs.recording.recordCinematic, rs.recording.recordCurrentKf,
                           glm::length(cameraPos), rs.recording.recordCurRs,
                           rs.recording.recordCurIsco, rs.recording.recordFrameIndex,
                           cli.recordFramesTotal);
  }

  // ImGui Render
  ImGui::Render();
  ImGui_ImplOpenGL3_RenderDrawData(ImGui::GetDrawData());

  if (!cli.workspaceScreenshotPath.empty()) {
    ++workspaceCaptureFrame;
    if (workspaceCaptureFrame == 3) {
      writeWorkspaceLayout(cli, true);
      rs.overlays.firstLayout = true;
    } else if (workspaceCaptureFrame == 6) {
      writeWorkspaceLayout(cli, false);
      writeWorkspaceScreenshot(cli, window);
    }
  }

  /* --record-frames: capture the tonemapped scene texture and advance the
   * frame index. The cinematic HUD drawn above is composited later by ffmpeg;
   * here we grab the clean scene texture, not the ImGui-chrome framebuffer. */
  captureRecordFrame(rs, cli);

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
      appendGpuTimingSample(gpuTimingPath(), rs.timing.gpuTimingLogIndex++, rs.targets.renderWidth,
                            rs.targets.renderHeight, cpuFrameMs, rs.timing.gpuTimers,
                            computeActiveForLog, rs.physicsCore.kerrSpin, glfwGetTime());
      rs.timing.gpuTimingLogCounter = 0;
    }
  }

  if (rs.timing.gpuTimers.initialized) {
    rs.timing.gpuTimers.swap();
  }
  FRAME_MARK;
  glfwSwapBuffers(window);

  if (!cli.workspaceScreenshotPath.empty() && workspaceCaptureFrame == 6) {
    return true;
  }

  /* --export-frame / --export-raw-frame: break after the export frame above. */
  if ((!cli.exportFramePath.empty() || !cli.exportRawFramePath.empty()) && sceneSettled) {
    const int exitFrame = cli.exportFrames > 0 ? cli.exportFrames : 6;
    if (++rs.exporting.exportDone >= exitFrame) {
      return true;
    }
  }

  /* --record-frames: break when all requested frames have been captured.
   * rs.recording.recordFrameIndex starts at cli.recordStartFrame; terminate when we have
   * written cli.recordFramesTotal frames (i.e. reached cli.recordStartFrame+total). */
  if (!cli.recordFramesDir.empty() &&
      rs.recording.recordFrameIndex >= cli.recordStartFrame + cli.recordFramesTotal) {
    int const written = rs.recording.recordFrameIndex - cli.recordStartFrame;
    std::printf("Record complete: %d frames written to %s\n", written, cli.recordFramesDir.c_str());
    return true;
  }
  return false;
}

/** @brief How the frame loop goes on after finishFrame. */
enum class FrameOutcome : std::uint8_t { Continue = 0, Finished = 1, CaptureFailed = 2 };

/**
 * @brief Exports, presents, and counts one frame. Captures count and write only
 *        frames that show the scene (sceneCaptureState), and an observer-sky
 *        capture ends with CaptureFailed when its sky cannot appear: an invalid
 *        observer or a failed load or build.
 */
FrameOutcome finishFrame(RenderState &rs, const platform::CliOptions &cli, GLFWwindow *window,
                         const glm::vec3 &cameraPos, float cpuFrameMs, bool computeActiveForLog,
                         int &workspaceCaptureFrame) {
  const blackhole::SceneCaptureState captureState = blackhole::sceneCaptureState(rs);
  const bool sceneSettled = captureState == blackhole::SceneCaptureState::Ready;
  const bool capturing = !cli.exportFramePath.empty() || !cli.exportRawFramePath.empty() ||
                         !cli.recordFramesDir.empty();
  if (sceneSettled) {
    exportFrameOnce(rs, cli);
  }
  if (completeFrame(rs, cli, window, cameraPos, cpuFrameMs, computeActiveForLog, sceneSettled,
                    workspaceCaptureFrame)) {
    return FrameOutcome::Finished;
  }
  if (capturing && captureState == blackhole::SceneCaptureState::Failed) {
    (void)std::fprintf(stderr, "Capture aborted: %s\n", rs.observerView.renderer.message().c_str());
    return FrameOutcome::CaptureFailed;
  }
  return FrameOutcome::Continue;
}

void prepareFrameTextures(RenderState &rs, const platform::CliOptions &cli,
                          const Settings &settings) {
  if (!cli.recordFramesDir.empty() && cli.recordProfile == "showcase-orbit" &&
      rs.wiregrid.wiregridEnabled &&
      rs.wiregrid.wiregridParams.mode == WiregridParams::Mode::Beauty) {
    applyShowcaseBeautyWiregridTuning(cli.recordComposition, rs.wiregrid.wiregridParams,
                                      rs.wiregrid.wiregridColor);
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
  updateActiveBackground(rs, settings.backgroundId);
  GLuint const backgroundFallback =
      rs.background.backgroundBase != 0 ? rs.background.backgroundBase : rs.background.fallback2D;
  rs.background.backgroundTextures.fill(backgroundFallback);
  if (!rs.disk.noiseTextureReady) {
    bool const noiseOk = rs.disk.noiseCache.initialize();
    rs.disk.noiseTextureReady = true; // don't retry regardless; FastNoise2 may be disabled
    if (noiseOk) {
      rs.disk.texNoiseVolume = rs.disk.noiseCache.getTurbulenceTexture();
    }
  }
}

void initializeWorkspaceLayout(Settings &settings, const ui::CampaignUiState &campaignUi,
                               RenderState &rs, bool freshLayout) {
  if (campaignUi.windowsOpen) {
    settings.workspaceKind = static_cast<int>(ui::WorkspaceKind::Diagnostics);
  }
  rs.overlays.firstLayout = freshLayout ||
                            settings.workspaceSchemaVersion != ui::K_WORKSPACE_SCHEMA_VERSION ||
                            !std::filesystem::exists(ImGui::GetIO().IniFilename);
}

void prepareWorkspaceDockspace(ImGuiID dockspaceId, Settings &settings, RenderState &rs) {
  ImGui::DockSpaceOverViewport(dockspaceId, ImGui::GetMainViewport(), ImGuiDockNodeFlags_None);
  if (rs.overlays.firstLayout) {
    resetLayout(dockspaceId, static_cast<ui::WorkspaceKind>(settings.workspaceKind));
    rs.overlays.firstLayout = false;
    settings.workspaceSchemaVersion = ui::K_WORKSPACE_SCHEMA_VERSION;
  }
  rs.overlays.diagnosticsVisible = settings.advancedControls ||
                                   settings.workspaceKind ==
                                       static_cast<int>(ui::WorkspaceKind::Diagnostics);
}

void renderModeMenu(Settings &settings, RenderState &rs) {
  if (!ImGui::BeginMainMenuBar()) {
    return;
  }
  if (ImGui::BeginMenu("Blackhole")) {
    if (ImGui::MenuItem("Simulator / Workbench", nullptr,
                        settings.workspaceKind == static_cast<int>(ui::WorkspaceKind::Simulator))) {
      settings.workspaceKind = static_cast<int>(ui::WorkspaceKind::Simulator);
      rs.overlays.firstLayout = true;
    }
    if (ImGui::MenuItem("Singularity: GOROROBA", nullptr,
                        settings.workspaceKind == static_cast<int>(ui::WorkspaceKind::Gororoba))) {
      settings.workspaceKind = static_cast<int>(ui::WorkspaceKind::Gororoba);
      rs.overlays.firstLayout = true;
    }
    ImGui::EndMenu();
  }
  ImGui::EndMainMenuBar();
}

void renderWorkspacePanels(RenderState &rs, const Settings &settings, GLFWwindow *window,
                           int windowWidth, int windowHeight, float cpuFrameMs,
                           game::CampaignSession &campaignSession,
                           ui::CampaignUiState &campaignUi,
                           ui::ConstellationUiState &constellationUi,
                           const std::array<ui::CampaignBackdrop, 5> &campaignBackdrops,
                           bool panelsVisible) {
  if (!panelsVisible) {
    return;
  }
  if (settings.workspaceKind != static_cast<int>(ui::WorkspaceKind::Gororoba)) {
    renderControlsSettingsPanel(rs);
    renderDisplaySettingsPanel(rs, window, windowWidth, windowHeight);
    renderBackgroundPanel(rs);
  }
  if (rs.overlays.diagnosticsVisible) {
    renderControlsHelpPanel();
    renderWiregridPanel(rs);
    ui::renderObserverWindows(rs);
    renderTesseractPanel(rs);
    renderRmlUiPanel(rs);
    renderGizmoPanel(rs);
    renderPerformancePanel(rs, cpuFrameMs);
  }
  if (settings.workspaceKind == static_cast<int>(ui::WorkspaceKind::Gororoba)) {
    ui::renderConstellationPanels(constellationUi, rs);
  } else if (settings.workspaceKind == static_cast<int>(ui::WorkspaceKind::Diagnostics)) {
    ui::renderCampaignWindows(campaignSession, campaignUi, campaignBackdrops.data(),
                              static_cast<int>(campaignBackdrops.size()));
  }
}

GLuint viewportDisplayTexture(const RenderState &rs, GLuint finalTexture) {
  return rs.terminalDiagnostics.showDebugView && rs.terminalDiagnostics.valid
             ? rs.terminalDiagnostics.debugTexture
             : finalTexture;
}

// Workspace captures take a canonical workspace and an explicit framebuffer
// size, and exclude the scene exports, which own the frame loop's exit.
bool workspaceCaptureOptionsValid(const platform::CliOptions &cli) {
  const bool capture = !cli.workspaceScreenshotPath.empty();
  const bool options = !cli.workspaceName.empty() || cli.windowWidth != 0 ||
                       cli.windowHeight != 0 || cli.uiScale != 1.0f;
  if (!capture) {
    return !options;
  }
  const bool known = cli.workspaceName == "simulator" || cli.workspaceName == "gororoba" ||
                     cli.workspaceName == "diagnostics";
  const bool sized = cli.windowWidth != 0 && cli.windowHeight != 0;
  const bool exclusive = cli.exportFramePath.empty() && cli.exportRawFramePath.empty() &&
                         cli.recordFramesDir.empty() && cli.referenceScene.empty();
  return known && sized && exclusive;
}

ui::WorkspaceKind workspaceKindFromName(std::string_view name) {
  if (name == "gororoba") {
    return ui::WorkspaceKind::Gororoba;
  }
  if (name == "diagnostics") {
    return ui::WorkspaceKind::Diagnostics;
  }
  return ui::WorkspaceKind::Simulator;
}

bool referenceOptionsValid(const platform::CliOptions &cli) {
  if (cli.referenceScene.empty()) {
    return true;
  }
  const bool sceneValid = cli.referenceScene == "A" || cli.referenceScene == "B" ||
                          cli.referenceScene == "C+" || cli.referenceScene == "C-" ||
                          cli.referenceScene == "Cd+" || cli.referenceScene == "Cd-" ||
                          cli.referenceScene == "D";
  const bool backendValid = cli.referenceBackend == "fragment" ||
                            cli.referenceBackend == "compute" || cli.referenceBackend == "cuda";
  const bool qualityValid = cli.referenceQuality == "balanced" ||
                            cli.referenceQuality == "reference";
  const bool exportValid = !cli.exportFramePath.empty() || !cli.exportRawFramePath.empty();
  if (!sceneValid || !backendValid || !qualityValid || !exportValid) {
    (void)std::fprintf(stderr, "Invalid reference scene, backend, quality, or missing export path\n");
    return false;
  }
#if !BLACKHOLE_HAS_CUDA
  if (cli.referenceBackend == "cuda") {
    (void)std::fprintf(stderr, "CUDA reference backend is unavailable in this build\n");
    return false;
  }
#endif
  return true;
}

} // anonymous namespace

// The entry point coordinates the desktop resource and frame lifecycles.
// NOLINTNEXTLINE(readability-function-cognitive-complexity)
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

    // Semantic validation lives here, where the showcase-orbit table is defined.
    if (cli.recordProfile != "cinematic" && cli.recordProfile != "compare-orbit-near" &&
        cli.recordProfile != "showcase-orbit") {
      std::printf("Unknown record profile: %s\n", cli.recordProfile.c_str());
      platform::printCliUsage(argv[0]);
      return 2;
    }
    if (cli.recordProfile == "showcase-orbit" &&
        findShowcaseOrbitComposition(cli.recordComposition) == nullptr) {
      std::printf("Unknown showcase composition: %s\n", cli.recordComposition.c_str());
      platform::printCliUsage(argv[0]);
      return 2;
    }
    if (!referenceOptionsValid(cli)) {
      return 2;
    }
    const bool workspaceCapture = !cli.workspaceScreenshotPath.empty();
    if (!workspaceCaptureOptionsValid(cli)) {
      (void)std::fprintf(stderr, "Workspace screenshot requires --workspace and --window-size "
                                 "and cannot combine with scene exports\n");
      return 2;
    }

    if (const auto conflict = blackhole::recordCameraConflict(cli)) {
      std::printf("%s\n", conflict->c_str());
      return 2;
    }
    if (const auto conflict =
            blackhole::exportConflictForScene(cli, blackhole::startupSceneMode())) {
      std::printf("%s\n", conflict->c_str());
      return 2;
    }

    platform::initResourceRoot(argv[0]);
    setShaderBaseDir(platform::resourceRoot().string() + "/");

    // Load settings first
    if (workspaceCapture) {
      SettingsManager::instance().setPersistenceEnabled(false);
      SettingsManager::instance().resetToDefaults();
    } else {
      SettingsManager::instance().load();
    }
    auto &settings = SettingsManager::instance().get();
    if (workspaceCapture) {
      settings.windowWidth = cli.windowWidth;
      settings.windowHeight = cli.windowHeight;
      settings.fullscreen = false;
      settings.swapInterval = 0;
      settings.workspaceKind = static_cast<int>(workspaceKindFromName(cli.workspaceName));
    }
    settings.workspaceKind = std::clamp(settings.workspaceKind, 0, 2);

    // Initialize window and OpenGL context
    GLFWwindow *window = initializeWindow(
        cli.exportWidth > 0 ? cli.exportWidth : settings.windowWidth,
        cli.exportHeight > 0 ? cli.exportHeight : settings.windowHeight);
    if (window == nullptr) {
      return 1;
    }
    if (workspaceCapture) {
      sizeWorkspaceFramebuffer(window, cli.windowWidth, cli.windowHeight);
    }

    glfwSwapInterval(settings.swapInterval);

    // Initialize shader manager (must be after OpenGL context)
    ShaderManager::instance().init();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
    // Initialize shader hot-reload watcher
    ShaderWatcher::instance().start(
        (std::filesystem::path(getShaderBaseDir()) / "shader").string());
#endif

    // Initialize input manager and sync with settings
    InputManager::instance().init(window);
    InputManager::instance().syncFromSettings();
    if (settings.fullscreen) {
      InputManager::instance().toggleFullscreen();
    }

    // Initialize ImGui
    initializeImGui(window);
    if (workspaceCapture) {
      ImGui::GetIO().IniFilename = nullptr;
      ImGui::GetIO().FontGlobalScale = cli.uiScale;
      ImGui::GetStyle().ScaleAllSizes(cli.uiScale);
    }

    // Curve overlay for plotting (e.g., critical curves)
    RenderState rs;

    // The simulator campaign and GOROROBA session own independent game state.
    game::CampaignSession campaignSession;
    ui::CampaignUiState campaignUi;
    ui::ConstellationUiState constellationUi;
    ui::initCampaignUiFromEnv(campaignUi);
    if (workspaceCapture) {
      campaignUi.windowsOpen = false;
    }
    initializeWorkspaceLayout(settings, campaignUi, rs, workspaceCapture);
    // Selectable NASA nebula backdrops for the strategic map. Each entry's
    // texture is 0 when its asset is absent, in which case the map draws its
    // procedural starfield for that choice. Loaded once; the Campaign panel
    // picks which one the map uses, and the map draws its credit.
    //
    // Sources with a build-generated resolution ladder pick the rendition that
    // matches the window: an ultrawide framebuffer takes a 21:9 crop, otherwise
    // the nearest width tier -- crisp on large displays, light on small ones.
    // The selector is keyed by the source base name, so every laddered backdrop
    // shares it.
    const auto campaignBackdrops = loadCampaignBackdrops(window);
    rs.recording.recordFrameIndex = cli.recordStartFrame;
    rs.recording.recordCinematic =
        static_cast<float>(cli.recordStartFrame) / static_cast<float>(K_CINEMATIC_FPS);

    if (!cli.curveTsvPath.empty()) {
      rs.overlays.curveOverlayLoaded = rs.overlays.curveOverlay.loadFromTsv(cli.curveTsvPath);
      if (!rs.overlays.curveOverlayLoaded) {
        (void)std::fprintf(stderr,
                           "curve overlay load failed: %s\n", // NOLINT(cert-err33-c) --
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
      const std::string packedPath = resourcePath("assets/grmhd/grmhd_pack.json");
      if (packedPath.size() >= rs.grmhd.grmhdPathBuffer.size()) {
        throw std::length_error("GRMHD metadata path exceeds the input buffer");
      }
      std::ranges::copy(packedPath, rs.grmhd.grmhdPathBuffer.begin());
      rs.grmhd.grmhdPathBuffer.at(packedPath.size()) = '\0';
      rs.grmhd.grmhdPathInit = true;
    }

    // Settings seed the render state once, before the first frame, so the
    // record profile applied on frame 1 (applyRecordProfileSetup) and the
    // environment overrides below replace them rather than being replaced.
    loadSettingsIntoRenderState(rs, settings);
    if (cli.exportWidth > 0) {
      rs.display.renderScale = 1.0f;
    }
    applyEnvironmentConfig(rs);
    if (K_APP_VARIANT_CUDA_ONLY) {
      rs.dispatch.contract.backend = RenderBackend::Cuda;
    }
    if (const auto backend = blackhole::rendererBackendFromName(cli.rendererBackend)) {
      rs.dispatch.contract.backend = *backend;
    }
    if (const auto geodesic = blackhole::geodesicModelFromName(cli.rendererGeodesic)) {
      rs.dispatch.contract.geodesic = *geodesic;
    }
    blackhole::normalizeRendererContract(rs.dispatch.contract);
    std::printf("Renderer startup: %.*s / %.*s / %.*s / %.*s; %d steps, %.3f step size\n",
                static_cast<int>(blackhole::rendererName(rs.dispatch.contract.backend).size()),
                blackhole::rendererName(rs.dispatch.contract.backend).data(),
                static_cast<int>(blackhole::rendererName(rs.dispatch.contract.geodesic).size()),
                blackhole::rendererName(rs.dispatch.contract.geodesic).data(),
                static_cast<int>(blackhole::rendererName(rs.dispatch.contract.radiative).size()),
                blackhole::rendererName(rs.dispatch.contract.radiative).data(),
                static_cast<int>(blackhole::rendererName(rs.dispatch.contract.quality).size()),
                blackhole::rendererName(rs.dispatch.contract.quality).data(),
                blackhole::rendererStepBudget(rs.dispatch.contract, rs.dispatch.computeMaxSteps,
                                              rs.dispatch.computeStepSize),
                static_cast<double>(blackhole::rendererStepSize(rs.dispatch.contract,
                                                                 rs.dispatch.computeStepSize)));

    /* WHY: computeProgram is hoisted here (rather than a static local inside the
     * frame loop) so the hot-reload handler at the top of each frame can delete
     * and reset it to 0, triggering lazy re-creation on the next iteration. */
    GLuint computeProgram = 0;
    int exitCode = 0;
    int workspaceCaptureFrame = 0;

    while (glfwWindowShouldClose(window) == 0) {
      // Clear default framebuffer (essential for ImGui Docking over Viewport)
      glClearColor(0.0f, 0.0f, 0.0f, 1.0f);
      glClear(GL_COLOR_BUFFER_BIT | GL_DEPTH_BUFFER_BIT);

      // std::cout << "Frame start" << std::endl; // Debug instrumentation
      ZONE_SCOPED_N("Frame");
      // ...
      // Calculate delta time
      double const wallTime = glfwGetTime();
      auto const deltaTime = workspaceCapture ? 0.0f : static_cast<float>(wallTime - lastTime);
      lastTime = wallTime;
      // Time-driven shading reads content time: the record output clock
      // under --record-frames, the wall clock otherwise.
      double const currentTime = workspaceCapture
                                     ? 0.0
                                     : frameContentSeconds(cli, rs.recording.recordFrameIndex, wallTime);
      auto const frameTime = static_cast<float>(currentTime);
      const float cpuFrameMs = deltaTime * 1000.0f;

      glfwPollEvents();

#ifdef BLACKHOLE_ENABLE_SHADER_WATCHER
      reloadChangedShaders(rs, computeProgram);
#endif
      auto &input = InputManager::instance();
      updateInput(rs, cli, input, deltaTime);

      updateFrameTiming(rs, cpuFrameMs);
      // --record-frames: one-time initialization (cinematic quality, 1920x1080, no vsync)
      if (!cli.recordFramesDir.empty() && !rs.recording.recordInitDone) {
        if (!applyRecordProfileSetup(rs, cli, input, window)) {
          return 1;
        }
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
      prepareWorkspaceDockspace(dockspaceId, settings, rs);

      ImGui::PushStyleVar(ImGuiStyleVar_WindowPadding, ImVec2(0.0f, 0.0f));
      ImGui::Begin("Viewport", nullptr,
                   ImGuiWindowFlags_NoScrollbar | ImGuiWindowFlags_NoScrollWithMouse |
                       ImGuiWindowFlags_NoTitleBar);
      ImVec2 viewportSize = ImGui::GetContentRegionAvail();

      // Resize render targets to match viewport
      const int targetWidth = cli.exportWidth > 0 ? cli.exportWidth
          : (cli.referenceScene.empty() ? static_cast<int>(viewportSize.x)
                                        : blackhole::K_REFERENCE_SCENE_EXTENT);
      const int targetHeight = cli.exportHeight > 0 ? cli.exportHeight
          : (cli.referenceScene.empty() ? static_cast<int>(viewportSize.y)
                                        : blackhole::K_REFERENCE_SCENE_EXTENT);
      if (targetWidth > 0 && targetHeight > 0 &&
          (targetWidth != rs.targets.renderWidth || targetHeight != rs.targets.renderHeight)) {
        recreateRenderTargets(rs, targetWidth, targetHeight);
      }
      ImGui::End();
      ImGui::PopStyleVar();

      updateRmlUiOverlay(rs, window, windowWidth, windowHeight);
      configureFrameBackground(rs, cli);
      if (!cli.referenceScene.empty() && !rs.recording.referenceBackgroundReady) {
        if (rs.background.galaxy != 0) {
          glDeleteTextures(1, &rs.background.galaxy);
        }
        const std::uint8_t sky = blackhole::referenceSceneBacklit(cli.referenceScene) ? 255 : 16;
        rs.background.galaxy = createSolidCubemap1x1(sky, sky, sky);
        rs.recording.referenceBackgroundReady = true;
      }
      initializeExportDebugStage(rs);
      initializeWiregridEnvironment(rs);
      prepareFrameTextures(rs, cli, settings);

      rs.display.renderScale = std::clamp(rs.display.renderScale, 0.25f, 1.5f);
      // Legacy resize logic disabled in favor of Viewport-based sizing
      /*
      int targetWidth =
          std::max(1, static_cast<int>(static_cast<float>(windowWidth) * rs.display.renderScale));
      int targetHeight =
          std::max(1, static_cast<int>(static_cast<float>(windowHeight) * rs.display.renderScale));
      if (targetWidth != rs.targets.renderWidth || targetHeight != rs.targets.renderHeight) {
        recreateRenderTargets(rs, targetWidth, targetHeight);
      }
      */
      if (cli.exportWidth == 0 && !cli.hasExportExposure &&
          !cli.hasExportBloomStrength && !cli.hasExportToneMapping) {
        syncRenderStateToSettings(rs, settings, input);
      }

      if (input.isUIVisible()) {
        renderModeMenu(settings, rs);
      }

      // The Settings window owns the Scene selector, so it draws before any
      // code reads rs.scene.mode: dispatch, post-processing, and overlays then
      // see one scene for the whole frame.
      if (input.isUIVisible() &&
          settings.workspaceKind != static_cast<int>(ui::WorkspaceKind::Gororoba)) {
        renderSettingsWindow(rs);
      }
      // The --curve-tsv plot is independent of the scene.
      renderCurveOverlayWindow(rs, cli.curveTsvPath);

      // The compare sweep drives the geodesic integrator; another scene
      // cancels it and restores the live camera.
      updateComparePresetSweep(rs, input, ShaderManager::instance().canUseComputeShaders());
      blackhole::applyReferenceSceneSetup(rs, cli, input, window);
      if (cli.hasExportExposure) {
        rs.post.toneExposure = cli.exportExposure;
      }
      if (cli.hasExportBloomStrength) {
        rs.post.bloomStrength = cli.exportBloomStrength;
      }
      if (cli.hasExportToneMapping) {
        rs.post.tonemappingEnabled = cli.exportToneMapping;
      }

      // --record-frames: drive camera and spin from the selected record path
      applyRecordCameraPath(rs, cli, input);

      const auto frameCamera = updateFrameCamera(rs, input, cli, settings, deltaTime, currentTime);
      const auto &cameraPos = frameCamera.position;
      auto projectionMatrix = frameCamera.projection;
      auto gizmoViewMatrix = frameCamera.gizmoView;
      const auto blackholeFrame = renderSceneFrame(rs, cli, settings, input, frameCamera, frameTime,
                                                   deltaTime, currentTime, computeProgram);
      const bool grmhdReady = blackholeFrame.grmhdReady;
      const bool computeActiveForLog = blackholeFrame.computeActiveForLog;

      GLuint const finalTexture = runPostProcessPipeline(rs, input, currentTime);

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
      composeSceneOverlays(rs, input, finalTexture, grmhdReady);

      // Draw Final Texture to Viewport
      const GLuint viewportTexture = viewportDisplayTexture(rs, finalTexture);
      ImGui::Image(static_cast<ImTextureID>(viewportTexture), viewportSize, ImVec2(0, 1),
                   ImVec2(1, 0));

      // Enable mouse/keyboard interaction when hovering the viewport
      bool const isViewportHovered = ImGui::IsItemHovered();
      InputManager::instance().setIgnoreGuiCapture(isViewportHovered);

      // Gizmo
      if (rs.gizmoTargetActive()) {
        ImGuizmo::SetDrawlist();
        ImVec2 const windowPos = ImGui::GetWindowPos();
        ImGuizmo::SetRect(windowPos.x, windowPos.y, viewportSize.x, viewportSize.y);
        ImGuizmo::Manipulate(glm::value_ptr(gizmoViewMatrix), glm::value_ptr(projectionMatrix),
                             rs.camera.gizmoOperation, rs.camera.gizmoMode,
                             glm::value_ptr(rs.camera.gizmoTransform));
      }

      ImGui::End();         // End Viewport
      ImGui::PopStyleVar(); // WindowPadding

      // Normal UI panels are hidden in record mode so they don't appear in the video.
      renderWorkspacePanels(rs, settings, window, windowWidth, windowHeight, cpuFrameMs,
                            campaignSession, campaignUi, constellationUi, campaignBackdrops,
                            input.isUIVisible() && cli.recordFramesDir.empty());
      // The diagnostic campaign clock follows wall time only in its workspace.
      if (settings.workspaceKind == static_cast<int>(ui::WorkspaceKind::Diagnostics)) {
        ui::pumpCampaignRealtime(campaignSession, campaignUi,
                                 workspaceCapture ? 0.0 : static_cast<double>(deltaTime));
      }

      /* --export-frame / --export-raw-frame export before ImGui renders. */
      const FrameOutcome outcome =
          finishFrame(rs, cli, window, cameraPos, cpuFrameMs, computeActiveForLog,
                      workspaceCaptureFrame);
      if (outcome != FrameOutcome::Continue) {
        exitCode = static_cast<int>(outcome == FrameOutcome::CaptureFailed);
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
    rs.observerView.renderer.shutdown();
    rs.observerView.disclosureLabel.shutdown();
    rs.observerView.viewGuide.shutdown();
    rs.overlays.simulatorExplanation.shutdown();
    rs.tesseract.renderer.shutdown();
    rs.tesseract.speculativeLabel.shutdown();
    if (rs.grmhd.grmhdTexture.texture != 0) {
      destroyGrmhdPackedTexture(rs.grmhd.grmhdTexture);
    }

#if BLACKHOLE_HAS_CUDA
    rs.dispatch.cudaManager.shutdown();
#endif
    // Scene exports, record runs, and workspace captures run from overridden
    // state, so only an ordinary session writes settings back.
    cleanup(window, !workspaceCapture && cli.recordFramesDir.empty() &&
                        cli.referenceScene.empty() && cli.exportWidth == 0 &&
                        !cli.hasExportExposure && !cli.hasExportBloomStrength &&
                        !cli.hasExportToneMapping);
    return (exitCode != 0 || rs.exporting.exportFailed) ? 1 : 0;
#if BLACKHOLE_HAS_CPPTRACE
  } catch (const cpptrace::exception &err) {
    (void)std::fprintf(stderr, "Unhandled cpptrace exception: %s\n",
                       err.what()); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    err.trace().print();
    return 1;
  } catch (const std::exception &err) {
    (void)std::fprintf(stderr, "Unhandled std::exception: %s\n",
                       err.what()); // NOLINT(cert-err33-c) -- diagnostic output, return unused
    cpptrace::generate_trace(1).print();
    return 1;
  } catch (...) {
    (void)std::fprintf(stderr,
                       "Unhandled non-standard exception\n"); // NOLINT(cert-err33-c) --
                                                              // diagnostic output, return unused
    cpptrace::generate_trace(1).print();
    return 1;
  }
#else
  } catch (const std::exception &err) {
    (void)std::fprintf(stderr, "Unhandled std::exception: %s\n", err.what());
    return 1;
  } catch (...) {
    (void)std::fprintf(stderr, "Unhandled non-standard exception\n");
    return 1;
  }
#endif
}
