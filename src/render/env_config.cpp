/**
 * @file env_config.cpp
 * @brief BLACKHOLE_* environment-variable startup configuration.
 */

#include "render/env_config.h"
#include "render/renderer_contract.h"

#include <algorithm>
#include <cctype>
#include <charconv>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <iostream>
#include <limits>
#include <optional>
#include <string>
#include <string_view>
#include <system_error>
#include <utility>

#include "physics/safe_limits.h"
#include "render/gl_capabilities.h"
#include "render/observer_sky_view.h"
#include "render/render_state.h"
#include "render/tesseract/algebra_lattice.h"
#include "tools/compare_harness.h" // K_COMPARE_PRESETS

#if BLACKHOLE_HAS_CUDA
#include "cuda/cuda_render_manager.h" // BH_KERNEL_COUNT
#endif

namespace blackhole {
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
  // NOLINTNEXTLINE(bugprone-suspicious-stringview-data-usage): from_chars is bounded
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
      rs.dispatch.contract.backend = RenderBackend::Compute;
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
      rs.dispatch.contract.backend = RenderBackend::Fragment;
#if BLACKHOLE_HAS_CUDA
      rs.dispatch.cudaManager.setEnabled(false);
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

void applySceneEnvironment(RenderState &rs, std::string_view sceneName) {
  if (rs.scene.envApplied) {
    return;
  }
  if (sceneName.empty()) {
    if (const char *sceneEnv = std::getenv("BLACKHOLE_SCENE")) {
      if (!parseSceneName(sceneEnv).has_value()) {
        std::cerr << "BLACKHOLE_SCENE='" << sceneEnv
                  << "' is not a scene; expected blackhole, observer-sky, or tesseract\n";
      }
    }
  }
  rs.scene.mode = startupSceneMode(sceneName);
  rs.scene.envApplied = true;
  // BLACKHOLE_TESSERACT_STRUT=S pins the algebra strut and stops the ride;
  // BLACKHOLE_TESSERACT_WALLS=0 and BLACKHOLE_TESSERACT_KITES=0 hide the walls
  // and the box-kite glyphs.
  if (const char *strutEnv = std::getenv("BLACKHOLE_TESSERACT_STRUT")) {
    char *end = nullptr;
    const long strut = std::strtol(strutEnv, &end, 10);
    if (end != strutEnv && *end == '\0' && strut >= 1 && strut <= tesseract::ALGEBRA_MAX_STRUT) {
      rs.tesseract.algebraStrut = static_cast<int>(strut);
      rs.tesseract.algebraRide = false;
    } else {
      std::cerr << "BLACKHOLE_TESSERACT_STRUT='" << strutEnv << "' is not an integer in [1, "
                << tesseract::ALGEBRA_MAX_STRUT << "]; ignored\n";
    }
  }
  if (const char *wallsEnv = std::getenv("BLACKHOLE_TESSERACT_WALLS")) {
    rs.tesseract.wallsEnabled = std::string_view(wallsEnv) != "0";
  }
  if (const char *kitesEnv = std::getenv("BLACKHOLE_TESSERACT_KITES")) {
    rs.tesseract.kitesEnabled = std::string_view(kitesEnv) != "0";
  }
}

/** @brief A finite double from an environment variable, or nothing. */
std::optional<double> environmentDouble(const char *name) {
  const char *value = std::getenv(name);
  if (value == nullptr) {
    return std::nullopt;
  }
  char *end = nullptr;
  const double parsed = std::strtod(value, &end);
  if (end == value || *end != '\0' || !physics::safeIsfinite(parsed)) {
    std::cerr << name << "='" << value << "' is not a number; ignored\n";
    return std::nullopt;
  }
  return parsed;
}

/** @brief environmentDouble inside [low, high] (the matching panel slider's
 *         range), or nothing. */
std::optional<double> environmentDoubleIn(const char *name, double low, double high) {
  const std::optional<double> parsed = environmentDouble(name);
  if (parsed && (*parsed < low || *parsed > high)) {
    std::cerr << name << "=" << *parsed << " is outside [" << low << ", " << high << "]; ignored\n";
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
  view.epsilon = environmentDoubleIn("BLACKHOLE_OBSERVER_EPSILON", K_OBSERVER_EPSILON_MIN,
                                     K_OBSERVER_EPSILON_MAX)
                     .value_or(view.epsilon);
  if (const char *xEnv = std::getenv("BLACKHOLE_OBSERVER_X")) {
    if (std::string_view(xEnv) == "isco") {
      view.atIsco = true;
    } else if (const auto x = environmentDoubleIn("BLACKHOLE_OBSERVER_X", K_OBSERVER_X_MIN,
                                                  K_OBSERVER_X_MAX)) {
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
  view.massSolar =
      environmentDoubleIn("BLACKHOLE_OBSERVER_MASS", K_OBSERVER_MASS_MIN, K_OBSERVER_MASS_MAX)
          .value_or(view.massSolar);
  view.skyTimeScale = environmentDoubleIn("BLACKHOLE_OBSERVER_TIME_SCALE",
                                          K_OBSERVER_TIME_SCALE_MIN, K_OBSERVER_TIME_SCALE_MAX)
                          .value_or(view.skyTimeScale);
  view.properSeconds =
      environmentDouble("BLACKHOLE_OBSERVER_PROPER_SECONDS").value_or(view.properSeconds);
  view.fovDeg =
      environmentDoubleIn("BLACKHOLE_OBSERVER_FOV", K_OBSERVER_FOV_MIN_DEG, K_OBSERVER_FOV_MAX_DEG)
          .value_or(view.fovDeg);
  if (const char *rangeEnv = std::getenv("BLACKHOLE_OBSERVER_LUMINANCE_RANGE")) {
    const auto range = parseFinitePair(rangeEnv);
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
    view.navigation = look == "patch" ? RenderState::ObserverViewGroup::Navigation::TrackPatch
                                      : RenderState::ObserverViewGroup::Navigation::ManualAngles;
    if (look == "hole") {
      view.lookLongitudeDeg = 0.0;
    } else if (look == "forward") {
      view.lookLongitudeDeg = 90.0;
    } else if (look == "back") {
      view.lookLongitudeDeg = -90.0;
    } else if (look == "outward") {
      view.lookLongitudeDeg = 180.0;
    } else if (look != "patch") {
      if (const auto angles = parseFinitePair(lookEnv)) {
        view.lookLongitudeDeg = angles->first;
        view.lookLatitudeDeg = angles->second;
      } else {
        std::cerr << "BLACKHOLE_OBSERVER_LOOK='" << lookEnv << "' is not understood\n";
      }
    }
  }
}

// Startup disk overrides. BLACKHOLE_PHYSICAL_TRACER=0 selects the legacy
// fragment tracer and 1 the Kerr tracer, for A/B captures of the two paths;
// BLACKHOLE_DISK_TRANSFER=interstellar forces g = 1 (the film's disk) and
// =physical keeps the g-factor.
void applyDiskEnvironment(RenderState &rs) {
  if (const char *tracerEnv = std::getenv("BLACKHOLE_PHYSICAL_TRACER")) {
    rs.dispatch.contract.geodesic = std::string(tracerEnv) != "0"
                                        ? GeodesicModel::KerrReference : GeodesicModel::LegacyBeauty;
  }
  const char *transferEnv = std::getenv("BLACKHOLE_DISK_TRANSFER");
  if (transferEnv == nullptr) {
    return;
  }
  std::string const mode(transferEnv);
  if (mode == "interstellar") {
    rs.disk.diskTransferMode = 1;
  } else if (mode == "physical") {
    rs.disk.diskTransferMode = 0;
  } else {
    (void)std::fprintf(stderr, "Ignoring BLACKHOLE_DISK_TRANSFER=%s (expected physical|interstellar)\n",
                       transferEnv);
  }
}

} // namespace

// std::from_chars writes each parsed value through a reference, so a "nan" or
// "inf" component reaches memory the bit-level physics::safeIsfinite can
// classify; a by-value std::strtod result carries clang's nofpclass(nan inf)
// return annotation under -ffinite-math-only (ENABLE_FAST_MATH's default-on
// release preset), which makes a parsed NaN poison before either check runs.
std::optional<std::pair<double, double>> parseFinitePair(const char *text) {
  if (text == nullptr) {
    return std::nullopt;
  }
  // Each component accepts what strtod did for these overrides: surrounding
  // spaces or tabs and a leading '+'; the value itself must be finite.
  const auto parseComponent = [](std::string_view part) -> std::optional<double> {
    const std::size_t first = part.find_first_not_of(" \t");
    if (first == std::string_view::npos) {
      return std::nullopt;
    }
    part = part.substr(first, part.find_last_not_of(" \t") - first + 1);
    if (part.starts_with('+')) {
      part.remove_prefix(1);
    }
    double value = 0.0;
    const std::from_chars_result result =
        std::from_chars(part.data(), part.data() + part.size(), value);
    if (result.ec != std::errc{} || result.ptr != part.data() + part.size() ||
        !physics::safeIsfinite(value)) {
      return std::nullopt;
    }
    return value;
  };
  const std::string_view view(text);
  const std::size_t comma = view.find(',');
  if (comma == std::string_view::npos) {
    return std::nullopt;
  }
  const std::optional<double> first = parseComponent(view.substr(0, comma));
  const std::optional<double> second = parseComponent(view.substr(comma + 1));
  if (!first || !second) {
    return std::nullopt;
  }
  return std::pair{*first, *second};
}

std::optional<RenderState::SceneMode> parseSceneName(std::string_view name) {
  if (name == "observer-sky" || name == "observer") {
    return RenderState::SceneMode::ObserverSky;
  }
  if (name == "tesseract") {
    return RenderState::SceneMode::Tesseract;
  }
  if (name == "blackhole") {
    return RenderState::SceneMode::Blackhole;
  }
  return std::nullopt;
}

RenderState::SceneMode startupSceneMode(std::string_view sceneName) {
  if (!sceneName.empty()) {
    return parseSceneName(sceneName).value_or(RenderState::SceneMode::Blackhole);
  }
  const char *sceneEnv = std::getenv("BLACKHOLE_SCENE");
  if (sceneEnv == nullptr) {
    return RenderState::SceneMode::Blackhole;
  }
  return parseSceneName(sceneEnv).value_or(RenderState::SceneMode::Blackhole);
}

void applyEnvironmentConfig(RenderState &rs, std::string_view sceneName) {
  applySceneEnvironment(rs, sceneName);
  applyObserverEnvironment(rs);
  applyCompareEnvironment(rs);
  applyProbeEnvironment(rs);
  applyOverlayEnvironment(rs);
  applyDiskEnvironment(rs);
}

} // namespace blackhole
