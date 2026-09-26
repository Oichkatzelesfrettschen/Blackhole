/**
 * @file env_config.cpp
 * @brief BLACKHOLE_* environment-variable startup configuration.
 */

#include "render/env_config.h"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <string>
#include <string_view>
#include <system_error>

#include "physics/safe_limits.h"
#include "render/gl_capabilities.h"
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

// std::from_chars writes the parsed value through a reference, so an "inf" or
// "nan" input reaches memory from the IEEE-compiled library and the bit-level
// physics::safeIsfinite classifies it. A by-value std::strtod result carries
// clang's nofpclass(nan inf) return annotation under -ffinite-math-only, which
// makes a parsed NaN poison before any check can reject it.
float parseEnvironmentFloat(const char *value) {
  if (value == nullptr) {
    return 0.0f;
  }
  const auto isSpace = [](char c) { return std::isspace(static_cast<unsigned char>(c)) != 0; };
  std::string_view text(value);
  while (!text.empty() && isSpace(text.front())) {
    text.remove_prefix(1);
  }
  while (!text.empty() && isSpace(text.back())) {
    text.remove_suffix(1);
  }
  // One optional '+' precedes the digits; std::from_chars accepts only '-', so
  // "+-1" or "++1" would otherwise reach it with a sign it then consumes.
  if (!text.empty() && text.front() == '+') {
    text.remove_prefix(1);
    if (!text.empty() && (text.front() == '+' || text.front() == '-')) {
      return 0.0f;
    }
  }
  double parsed = 0.0;
  const char *const end = text.data() + text.size();
  const std::from_chars_result result = std::from_chars(text.data(), end, parsed);
  if (result.ec != std::errc{} || result.ptr != end || text.empty() ||
      !physics::safeIsfinite(parsed) ||
      std::abs(parsed) > static_cast<double>(std::numeric_limits<float>::max())) {
    return 0.0f;
  }
  return static_cast<float>(parsed);
}

namespace {

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

} // namespace

void applyEnvironmentConfig(RenderState &rs) {
  applyCompareEnvironment(rs);
  applyProbeEnvironment(rs);
  applyOverlayEnvironment(rs);
}

} // namespace blackhole
