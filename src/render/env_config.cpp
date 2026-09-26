/**
 * @file env_config.cpp
 * @brief BLACKHOLE_* environment-variable startup configuration.
 */

#include "render/env_config.h"

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <utility>

#include "physics/safe_limits.h"
#include "render/gl_capabilities.h"
#include "render/observer_sky_view.h"
#include "render/render_state.h"
#include "tools/compare_harness.h" // K_COMPARE_PRESETS

#if BLACKHOLE_HAS_CUDA
#include "cuda/cuda_render_manager.h" // BH_KERNEL_COUNT
#endif

namespace blackhole {
#if BLACKHOLE_HAS_CUDA
// The CUDA-only desktop variant is selected per target via
// target_compile_definitions; other targets fall back to 0, matching main.
#ifndef BLACKHOLE_APP_VARIANT_CUDA_ONLY
#define BLACKHOLE_APP_VARIANT_CUDA_ONLY 0
#endif
namespace {

constexpr bool kAppVariantCudaOnly = BLACKHOLE_APP_VARIANT_CUDA_ONLY != 0;

} // namespace
#endif

namespace {

float parseEnvironmentFloat(const char *value) {
  char *end = nullptr;
  const double parsed = std::strtod(value, &end);
  if (end == value || !std::isfinite(parsed) ||
      std::abs(parsed) > static_cast<double>(std::numeric_limits<float>::max())) {
    return 0.0f;
  }
  return static_cast<float>(parsed);
}

void applyCompareEnvironment(RenderState &rs) {
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
        rs.compare.compareMaxOutlierFrac = std::max(
            0.0f,
            parseEnvironmentFloat(
                outlierFracEnv)); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
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
        rs.compare.compareStepSizeOverride = parseEnvironmentFloat(
            stepSizeEnv); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
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
}

void applyProbeEnvironment(RenderState &rs) {

#if BLACKHOLE_HAS_CUDA
  if (!rs.dispatch.cudaVariantEnvApplied) {
    if (const char *variantEnv = std::getenv("BLACKHOLE_CUDA_KERNEL_VARIANT")) {
      int requestedVariant = std::atoi(variantEnv); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c) -- env var, validated below
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
}

void applyOverlayEnvironment(RenderState &rs) {
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
      auto const scale = parseEnvironmentFloat(
          scaleEnv); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
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
      auto const scale = parseEnvironmentFloat(
          scaleEnv); // NOLINT(bugprone-unchecked-string-to-number-conversion,cert-err34-c)
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
}

void applySceneEnvironment(RenderState &rs) {
  if (rs.scene.envApplied) {
    return;
  }
  if (const char *sceneEnv = std::getenv("BLACKHOLE_SCENE")) {
    if (!parseSceneName(sceneEnv).has_value()) {
      std::cerr << "BLACKHOLE_SCENE='" << sceneEnv
                << "' is not a scene; expected blackhole or observer-sky\n";
    }
  }
  rs.scene.mode = startupSceneMode();
  rs.scene.envApplied = true;
}

/** @brief Two numbers written "<a>,<b>", or nothing. */
std::optional<std::pair<double, double>> parseNumberPair(const char *text) {
  char *end = nullptr;
  const double first = std::strtod(text, &end);
  if (end == text || *end != ',') {
    return std::nullopt;
  }
  const char *second = end + 1;
  const double value = std::strtod(second, &end);
  if (end == second || *end != '\0') {
    return std::nullopt;
  }
  return std::pair{first, value};
}

/** @brief A finite double from an environment variable, or nothing. */
std::optional<double> environmentDouble(const char *name) {
  const char *value = std::getenv(name);
  if (value == nullptr) {
    return std::nullopt;
  }
  char *end = nullptr;
  const double parsed = std::strtod(value, &end);
  if (end == value || !physics::safeIsfinite(parsed)) {
    std::cerr << name << "='" << value << "' is not a number; ignored\n";
    return std::nullopt;
  }
  return parsed;
}

/**
 * Observer-sky view for scripted captures: BLACKHOLE_OBSERVER_EPSILON (1 - a),
 * BLACKHOLE_OBSERVER_X (r - 1, or "isco"), BLACKHOLE_OBSERVER_KIND
 * (prograde|retrograde|zamo|static), BLACKHOLE_OBSERVER_MASS (M_sun),
 * BLACKHOLE_OBSERVER_TIME_SCALE, BLACKHOLE_OBSERVER_PROPER_SECONDS (start
 * clock), BLACKHOLE_OBSERVER_FOV (deg), BLACKHOLE_OBSERVER_LUMINANCE_RANGE
 * ("<log10 min>,<log10 max>" in cd/m^2), and BLACKHOLE_OBSERVER_LOOK: hole,
 * forward, back, outward, patch, or "<longitude>,<latitude>" in degrees.
 */
void applyObserverEnvironment(RenderState &rs) {
  RenderState::ObserverViewGroup &view = rs.observerView;
  if (view.envApplied) {
    return;
  }
  view.envApplied = true;
  view.epsilon = environmentDouble("BLACKHOLE_OBSERVER_EPSILON").value_or(view.epsilon);
  if (const char *xEnv = std::getenv("BLACKHOLE_OBSERVER_X")) {
    if (std::string_view(xEnv) == "isco") {
      view.atIsco = true;
    } else if (const auto x = environmentDouble("BLACKHOLE_OBSERVER_X")) {
      view.atIsco = false;
      view.x = *x;
    }
  }
  if (const char *kindEnv = std::getenv("BLACKHOLE_OBSERVER_KIND")) {
    const std::string_view kind(kindEnv);
    if (kind == "prograde") {
      view.kind = ObserverKind::Prograde;
    } else if (kind == "retrograde") {
      view.kind = ObserverKind::Retrograde;
    } else if (kind == "zamo") {
      view.kind = ObserverKind::Zamo;
    } else if (kind == "static") {
      view.kind = ObserverKind::Static;
    } else {
      std::cerr << "BLACKHOLE_OBSERVER_KIND='" << kindEnv
                << "' is not prograde, retrograde, zamo, or static\n";
    }
  }
  view.massSolar = environmentDouble("BLACKHOLE_OBSERVER_MASS").value_or(view.massSolar);
  view.skyTimeScale =
      environmentDouble("BLACKHOLE_OBSERVER_TIME_SCALE").value_or(view.skyTimeScale);
  view.properSeconds =
      environmentDouble("BLACKHOLE_OBSERVER_PROPER_SECONDS").value_or(view.properSeconds);
  view.fovDeg = environmentDouble("BLACKHOLE_OBSERVER_FOV").value_or(view.fovDeg);
  if (const char *rangeEnv = std::getenv("BLACKHOLE_OBSERVER_LUMINANCE_RANGE")) {
    const auto range = parseNumberPair(rangeEnv);
    if (range && range->first < range->second) {
      view.logLuminanceMin = static_cast<float>(range->first);
      view.logLuminanceMax = static_cast<float>(range->second);
    } else {
      std::cerr << "BLACKHOLE_OBSERVER_LUMINANCE_RANGE='" << rangeEnv
                << "' is not <log10 min>,<log10 max>\n";
    }
  }
  if (const char *lookEnv = std::getenv("BLACKHOLE_OBSERVER_LOOK")) {
    const std::string_view look(lookEnv);
    view.lookAtPatch = look == "patch";
    view.followCamera = false;
    if (look == "hole") {
      view.lookLongitudeDeg = 0.0;
    } else if (look == "forward") {
      view.lookLongitudeDeg = 90.0;
    } else if (look == "back") {
      view.lookLongitudeDeg = -90.0;
    } else if (look == "outward") {
      view.lookLongitudeDeg = 180.0;
    } else if (look != "patch") {
      if (const auto angles = parseNumberPair(lookEnv)) {
        view.lookLongitudeDeg = angles->first;
        view.lookLatitudeDeg = angles->second;
      } else {
        std::cerr << "BLACKHOLE_OBSERVER_LOOK='" << lookEnv << "' is not understood\n";
      }
    }
  }
}

} // namespace

std::optional<RenderState::SceneMode> parseSceneName(std::string_view name) {
  if (name == "observer-sky") {
    return RenderState::SceneMode::ObserverSky;
  }
  if (name == "blackhole") {
    return RenderState::SceneMode::Blackhole;
  }
  return std::nullopt;
}

RenderState::SceneMode startupSceneMode() {
  const char *sceneEnv = std::getenv("BLACKHOLE_SCENE");
  if (sceneEnv == nullptr) {
    return RenderState::SceneMode::Blackhole;
  }
  return parseSceneName(sceneEnv).value_or(RenderState::SceneMode::Blackhole);
}

void applyEnvironmentConfig(RenderState &rs) {
  applySceneEnvironment(rs);
  applyObserverEnvironment(rs);
  applyCompareEnvironment(rs);
  applyProbeEnvironment(rs);
  applyOverlayEnvironment(rs);
}

} // namespace blackhole
