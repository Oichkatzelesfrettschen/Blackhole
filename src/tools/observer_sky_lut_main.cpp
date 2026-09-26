/**
 * @file observer_sky_lut_main.cpp
 * @brief Command-line builder for the observer-sky lookup bundle
 *        (physics/observer_sky_lut.h): traces the sky of one equatorial Kerr
 *        observer, writes observer_sky_<hash>.bin and its JSON sidecar, and
 *        prints the measured statistics.
 *
 * Usage:
 *   observer_sky_lut [--canon] [--epsilon E] [--x X | --isco]
 *                    [--observer orbit|retrograde|zamo|static | --velocity V]
 *                    [--width W] [--height H] [--tile N] [--step F]
 *                    [--threads N] [--out DIR]
 *
 * --canon selects Gargantua's spin deficit 1.33e-14 with the observer on the
 * prograde ISCO (Miller's planet). The default output directory is the
 * renderer's bundle cache, <user cache>/observer_sky ($XDG_CACHE_HOME or
 * ~/.cache), falling back to assets/luts under the current directory.
 */

#include <algorithm>
#include <charconv>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <numbers>
#include <optional>
#include <span>
#include <string>
#include <string_view>
#include <system_error>

#include "physics/kerr_observer.h"
#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"
#include "physics/safe_limits.h"
#include "platform/resource_paths.h"

namespace {

namespace ko = physics::kerr_observer;
namespace sky = physics::observer_sky;

constexpr double K_CANON_DEFICIT = 1.33e-14;
constexpr double K_ARCSECONDS_PER_RADIAN = 180.0 * 3600.0 / std::numbers::pi;
/// Widest axis --width, --height, and --tile accept; the texel count of each
/// image is further bounded by sky::K_MAX_IMAGE_TEXELS.
constexpr std::size_t K_MAX_AXIS = std::size_t{1} << 16U;
constexpr std::size_t K_MAX_THREADS = 4096;

struct Options {
  double epsilon = K_CANON_DEFICIT;
  std::optional<double> x;
  std::string observer = "orbit";
  std::optional<double> velocity;
  sky::LutDimensions dimensions;
  sky::TraceSettings settings;
  unsigned threads = 0;
  std::filesystem::path out = [] {
    const std::filesystem::path cache = platform::writableCacheSubdirectory("observer_sky");
    return cache.empty() ? std::filesystem::path("assets/luts") : cache;
  }();
};

void printUsage() {
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
std::optional<std::size_t> parseCount(std::string_view text, std::size_t low, std::size_t high) {
  std::size_t value = 0;
  const char *last = text.data() + text.size();
  const auto [end, error] = std::from_chars(text.data(), last, value);
  if (error != std::errc{} || end != last || value < low || value > high) {
    return std::nullopt;
  }
  return value;
}

/** @brief `text` as a whole finite decimal number, or nothing. */
std::optional<double> parseNumber(std::string_view text) {
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
bool applyValue(Options &options, std::string_view flag, std::string_view text) {
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
      options.dimensions.height = std::max<std::size_t>(*count / 2, 1);
    } else if (flag == "--height") {
      options.dimensions.height = *count;
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
bool dimensionsFit(const sky::LutDimensions &dimensions) {
  return dimensions.width * dimensions.height <= sky::K_MAX_IMAGE_TEXELS &&
         dimensions.tileRadial * dimensions.tileAzimuth <= sky::K_MAX_IMAGE_TEXELS;
}

std::optional<Options> parseOptions(std::span<char *> args) {
  Options options;
  for (std::size_t index = 1; index < args.size(); ++index) {
    const std::string_view flag = args[index];
    const bool hasValue = index + 1 < args.size();
    if (flag == "--canon" || flag == "--isco") {
      // Both put the observer on the ISCO; --canon also fixes Gargantua's spin.
      options.x.reset();
      if (flag == "--canon") {
        options.epsilon = K_CANON_DEFICIT;
        options.observer = "orbit";
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

std::optional<sky::ObserverKey> resolveObserver(const Options &options) {
  const ko::OrbitSense sense =
      options.observer == "retrograde" ? ko::OrbitSense::Retrograde : ko::OrbitSense::Prograde;
  const double x = options.x.value_or(ko::iscoOffset(options.epsilon, sense));
  if (options.velocity) {
    return sky::ObserverKey{.epsilon = options.epsilon, .x = x, .velocity = *options.velocity};
  }
  if (options.observer == "zamo") {
    return sky::ObserverKey{.epsilon = options.epsilon, .x = x, .velocity = 0.0};
  }
  if (options.observer == "static") {
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

void printStatistics(const sky::ObserverSkyLut &lut, double seconds) {
  const sky::LutStatistics &s = lut.statistics;
  const sky::SkyAngles peak = sky::lookAngles(lut.peak.look);
  constexpr double degreesPerRadian = 180.0 / std::numbers::pi;
  std::printf("observer: epsilon %.6g  x %.9g  v %.15g\n", lut.key.epsilon, lut.key.x,
              lut.key.velocity);
  std::printf("traced %zux%zu + tile %zux%zu in %.2f s\n", lut.dimensions.width,
              lut.dimensions.height, lut.dimensions.tileRadial, lut.dimensions.tileAzimuth,
              seconds);
  std::printf("shadow fraction %.5f (trapped %.2e)\n", s.capturedFraction, s.trappedFraction);
  std::printf("g range %.6g .. %.6g (peak at longitude %.6f deg, latitude %.6f deg)\n", s.gMin,
              s.gMax, peak.longitude * degreesPerRadian, peak.latitude * degreesPerRadian);
  std::printf("99%% energy region: longitude span %.4f arcsec, latitude span %.4f arcsec, "
              "solid angle %.4g sr, g >= %.6g\n",
              s.patch99LongitudeSpan * K_ARCSECONDS_PER_RADIAN,
              s.patch99LatitudeSpan * K_ARCSECONDS_PER_RADIAN, s.patch99SolidAngle,
              s.patch99ThresholdG);
  std::printf("energy (int g^4 dOmega): tile %.6g, outside tile %.6g; equivalent isotropic g "
              "%.6g; energy-weighted g %.6g\n",
              s.tileEnergy, s.energyOutsideTile, s.equivalentIsotropicG, s.energyWeightedG);
  std::printf("CMB 2.725 K -> equivalent isotropic %.4g K, energy-weighted %.4g K, peak %.4g K\n",
              2.725 * s.equivalentIsotropicG, 2.725 * s.energyWeightedG, 2.725 * s.gMax);
  std::printf("photonConstants connectivity disagreements: %llu\n",
              static_cast<unsigned long long>(s.connectivityDisagreements));
}

} // namespace

int main(int argc, char **argv) {
  const auto options = parseOptions(std::span<char *>(argv, static_cast<std::size_t>(argc)));
  if (!options) {
    printUsage();
    return 2;
  }
  const auto key = resolveObserver(*options);
  if (!key) {
    std::puts("no timelike observer of that kind at that radius");
    return 2;
  }
  const auto start = std::chrono::steady_clock::now();
  const sky::ObserverSkyLut lut =
      sky::buildObserverSkyLut(*key, options->dimensions, options->settings, options->threads);
  const double seconds =
      std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
  printStatistics(lut, seconds);
  if (!sky::writeObserverSkyLut(lut, options->out)) {
    std::printf("could not write %s\n", options->out.string().c_str());
    return 1;
  }
  const std::uint64_t hash = sky::lutHash(lut.key, lut.dimensions, lut.settings);
  // The default output is the renderer's shared cache, so it keeps its budget.
  sky::evictObserverSkyBundles(options->out, sky::K_OBSERVER_SKY_CACHE_BYTES, hash);
  const std::string stem = sky::lutStem(hash);
  std::printf("wrote %s/%s.{bin,json}\n", options->out.string().c_str(), stem.c_str());
  return 0;
}
