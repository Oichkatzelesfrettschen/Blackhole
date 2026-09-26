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
 * prograde ISCO (Miller's planet). The default output directory is
 * assets/luts under the current directory; the renderer looks there first.
 */

#include <chrono>
#include <cmath>
#include <cstdio>
#include <cstdlib>
#include <filesystem>
#include <numbers>
#include <optional>
#include <span>
#include <string>
#include <string_view>

#include "physics/kerr_observer.h"
#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"

namespace {

namespace ko = physics::kerr_observer;
namespace sky = physics::observer_sky;

constexpr double K_CANON_DEFICIT = 1.33e-14;
constexpr double K_ARCSECONDS_PER_RADIAN = 180.0 * 3600.0 / std::numbers::pi;

struct Options {
  double epsilon = K_CANON_DEFICIT;
  std::optional<double> x;
  std::string observer = "orbit";
  std::optional<double> velocity;
  sky::LutDimensions dimensions;
  sky::TraceSettings settings;
  unsigned threads = 0;
  std::filesystem::path out = "assets/luts";
};

void printUsage() {
  std::puts("usage: observer_sky_lut [--canon] [--epsilon E] [--x X | --isco]\n"
            "                        [--observer orbit|retrograde|zamo|static | --velocity V]\n"
            "                        [--width W] [--height H] [--tile N] [--step F]\n"
            "                        [--threads N] [--out DIR]");
}

std::optional<Options> parseOptions(std::span<char *> args) {
  Options options;
  for (std::size_t index = 1; index < args.size(); ++index) {
    const std::string_view flag = args[index];
    const bool hasValue = index + 1 < args.size();
    const auto value = [&]() -> std::string_view { return args[++index]; };
    const auto number = [&]() { return std::strtod(value().data(), nullptr); };
    const auto count = [&]() {
      return static_cast<std::size_t>(std::strtoull(value().data(), nullptr, 10));
    };
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
    if (flag == "--epsilon") {
      options.epsilon = number();
    } else if (flag == "--x") {
      options.x = number();
    } else if (flag == "--observer") {
      options.observer = std::string(value());
    } else if (flag == "--velocity") {
      options.velocity = number();
    } else if (flag == "--width") {
      options.dimensions.width = count();
      options.dimensions.height = options.dimensions.width / 2;
    } else if (flag == "--height") {
      options.dimensions.height = count();
    } else if (flag == "--tile") {
      options.dimensions.tileRadial = count();
      options.dimensions.tileAzimuth = options.dimensions.tileRadial;
    } else if (flag == "--step") {
      options.settings.stepFraction = number();
    } else if (flag == "--threads") {
      options.threads = static_cast<unsigned>(count());
    } else if (flag == "--out") {
      options.out = std::string(value());
    } else {
      return std::nullopt;
    }
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
  const std::string stem = sky::lutStem(sky::lutHash(lut.key, lut.dimensions, lut.settings));
  std::printf("wrote %s/%s.{bin,json}\n", options->out.string().c_str(), stem.c_str());
  return 0;
}
