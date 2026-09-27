/**
 * @file observer_sky_lut_options.h
 * @brief Argument parsing and observer resolution for observer_sky_lut_main,
 *        pulled into a header so a test can drive them without a process.
 */

#ifndef BLACKHOLE_TOOLS_OBSERVER_SKY_LUT_OPTIONS_H
#define BLACKHOLE_TOOLS_OBSERVER_SKY_LUT_OPTIONS_H

#include <charconv>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <filesystem>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <system_error>

#include "physics/kerr_observer.h"
#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"
#include "physics/safe_limits.h"

namespace blackhole::observer_sky_lut_cli {

namespace ko = physics::kerr_observer;
namespace sky = physics::observer_sky;

inline constexpr double K_CANON_DEFICIT = 1.33e-14;
/// Widest axis --width, --height, and --tile accept; the texel count of each
/// image is further bounded by sky::K_MAX_IMAGE_TEXELS.
inline constexpr std::size_t K_MAX_AXIS = std::size_t{1} << 16U;
inline constexpr std::size_t K_MAX_THREADS = 4096;

struct Options {
  double epsilon = K_CANON_DEFICIT;
  std::optional<double> x;
  std::string observer = "orbit";
  std::optional<double> velocity;
  sky::LutDimensions dimensions;
  sky::TraceSettings settings;
  unsigned threads = 0;
  std::filesystem::path out; ///< Empty until --out: main picks the shared cache.
  /// Set once --height is given explicitly, so a later --width derives the
  /// default height (width / 2) only when nothing has fixed it yet.
  bool heightExplicit = false;
};

inline void printUsage() {
  std::puts("usage: observer_sky_lut [--canon] [--epsilon E] [--x X | --isco]\n"
            "                        [--observer orbit|retrograde|zamo|static | --velocity V]\n"
            "                        [--width W] [--height H] [--tile N] [--step F]\n"
            "                        [--threads N] [--out DIR]\n"
            "W, H, N in [1, 65536] with at most 2^26 texels per image; threads in [0, 4096];\n"
            "E in [0, 1]; X > 0; |V| < 1; F in (0, 1]");
}

/** @brief `text` as a whole decimal count in [low, high], or nothing. Signs
 *         are refused (strtoull reads "-1" as 2^64 - 1), as are overflow and
 *         trailing characters. */
inline std::optional<std::size_t> parseCount(std::string_view text, std::size_t low,
                                             std::size_t high) {
  std::size_t value = 0;
  const char *last = text.data() + text.size();
  const auto [end, error] = std::from_chars(text.data(), last, value);
  if (error != std::errc{} || end != last || value < low || value > high) {
    return std::nullopt;
  }
  return value;
}

/** @brief `text` as a whole finite decimal number, or nothing. */
inline std::optional<double> parseNumber(std::string_view text) {
  double value = 0.0;
  const char *last = text.data() + text.size();
  const auto [end, error] = std::from_chars(text.data(), last, value);
  if (error != std::errc{} || end != last || !physics::safeIsfinite(value)) {
    return std::nullopt;
  }
  return value;
}

/** @brief Applies one valued flag; false for an unknown flag or a value
 *         outside the flag's range. */
inline bool applyValue(Options &options, std::string_view flag, std::string_view text) {
  if (flag == "--observer") {
    options.observer = std::string(text);
    return true;
  }
  if (flag == "--out") {
    options.out = std::string(text);
    return true;
  }
  if (flag == "--width" || flag == "--height" || flag == "--tile" || flag == "--threads") {
    const bool threads = flag == "--threads";
    const auto count = parseCount(text, threads ? 0 : 1, threads ? K_MAX_THREADS : K_MAX_AXIS);
    if (!count) {
      return false;
    }
    if (threads) {
      options.threads = static_cast<unsigned>(*count);
    } else if (flag == "--width") {
      options.dimensions.width = *count;
      if (!options.heightExplicit) {
        options.dimensions.height = std::max<std::size_t>(*count / 2, 1);
      }
    } else if (flag == "--height") {
      options.dimensions.height = *count;
      options.heightExplicit = true;
    } else {
      options.dimensions.tileRadial = *count;
      options.dimensions.tileAzimuth = *count;
    }
    return true;
  }
  const std::optional<double> number = parseNumber(text);
  if (!number) {
    return false;
  }
  if (flag == "--epsilon" && *number >= 0.0 && *number <= 1.0) {
    options.epsilon = *number;
  } else if (flag == "--x" && *number > 0.0) {
    options.x = number;
  } else if (flag == "--velocity" && std::fabs(*number) < 1.0) {
    options.velocity = number;
  } else if (flag == "--step" && *number > 0.0 && *number <= 1.0) {
    options.settings.stepFraction = *number;
  } else {
    return false;
  }
  return true;
}

/** @brief Both images fit a readable bundle (sky::K_MAX_IMAGE_TEXELS). */
inline bool dimensionsFit(const sky::LutDimensions &dimensions) {
  return dimensions.width * dimensions.height <= sky::K_MAX_IMAGE_TEXELS &&
         dimensions.tileRadial * dimensions.tileAzimuth <= sky::K_MAX_IMAGE_TEXELS;
}

inline std::optional<Options> parseOptions(std::span<char *> args) {
  Options options;
  for (std::size_t index = 1; index < args.size(); ++index) {
    const std::string_view flag = args[index];
    const bool hasValue = index + 1 < args.size();
    if (flag == "--canon" || flag == "--isco") {
      // Both put the observer on the ISCO; --canon also fixes Gargantua's
      // spin and resets an earlier --velocity, so the preset always names a
      // ZAMO-comoving orbiting observer rather than an inherited override.
      options.x.reset();
      if (flag == "--canon") {
        options.epsilon = K_CANON_DEFICIT;
        options.observer = "orbit";
        options.velocity.reset();
      }
      continue;
    }
    if (!hasValue) {
      return std::nullopt;
    }
    const std::string_view text = args[++index];
    if (!applyValue(options, flag, text)) {
      (void)std::fprintf(stderr, "observer_sky_lut: %.*s %.*s is not accepted\n",
                         static_cast<int>(flag.size()), flag.data(), static_cast<int>(text.size()),
                         text.data());
      return std::nullopt;
    }
  }
  if (!dimensionsFit(options.dimensions)) {
    (void)std::fprintf(stderr, "observer_sky_lut: an image exceeds %zu texels\n",
                       sky::K_MAX_IMAGE_TEXELS);
    return std::nullopt;
  }
  return options;
}

/** @brief The key an option set names, or nothing when it names no timelike
 *         observer: an explicit --velocity or --observer zamo at or inside
 *         the outer horizon (x <= horizonOffset(epsilon), the renderer's own
 *         observerKeyFor gate in observer_sky_view.cpp), or a --observer
 *         static faster than light. */
inline std::optional<sky::ObserverKey> resolveObserver(const Options &options) {
  const ko::OrbitSense sense =
      options.observer == "retrograde" ? ko::OrbitSense::Retrograde : ko::OrbitSense::Prograde;
  const double x = options.x.value_or(ko::iscoOffset(options.epsilon, sense));
  const bool outsideHorizon = x > ko::horizonOffset(options.epsilon);
  if (options.velocity) {
    if (!outsideHorizon) {
      return std::nullopt;
    }
    return sky::ObserverKey{.epsilon = options.epsilon, .x = x, .velocity = *options.velocity};
  }
  if (options.observer == "zamo") {
    if (!outsideHorizon) {
      return std::nullopt;
    }
    return sky::ObserverKey{.epsilon = options.epsilon, .x = x, .velocity = 0.0};
  }
  if (options.observer == "static") {
    if (!outsideHorizon) {
      return std::nullopt;
    }
    const double velocity = ko::staticObserverVelocity(ko::equatorialFrame(options.epsilon, x));
    if (!(std::fabs(velocity) < 1.0)) {
      return std::nullopt;
    }
    return sky::ObserverKey{.epsilon = options.epsilon, .x = x, .velocity = velocity};
  }
  if (options.observer == "orbit" || options.observer == "retrograde") {
    return sky::orbitingObserver(options.epsilon, x, sense);
  }
  return std::nullopt;
}

} // namespace blackhole::observer_sky_lut_cli

#endif // BLACKHOLE_TOOLS_OBSERVER_SKY_LUT_OPTIONS_H
