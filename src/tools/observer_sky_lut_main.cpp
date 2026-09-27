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
 * ~/.cache), falling back to the resource tree's assets/luts; only that
 * shared cache is evicted to its budget, never an explicit --out directory.
 */

#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <numbers>
#include <optional>
#include <span>
#include <string>

#include "physics/observer_sky_lut.h"
#include "physics/observer_sky_map.h"
#include "platform/resource_paths.h"
#include "tools/observer_sky_lut_options.h"

namespace {

namespace sky = physics::observer_sky;
using blackhole::observer_sky_lut_cli::parseOptions;
using blackhole::observer_sky_lut_cli::printUsage;
using blackhole::observer_sky_lut_cli::resolveObserver;

constexpr double K_ARCSECONDS_PER_RADIAN = 180.0 * 3600.0 / std::numbers::pi;

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
  platform::initResourceRoot(argv[0]);
  auto options = parseOptions(std::span<char *>(argv, static_cast<std::size_t>(argc)));
  if (!options) {
    printUsage();
    return 2;
  }
  // Default output: the renderer's shared cache, else the resource tree's
  // assets/luts, the directory the renderer falls back to.
  // Only a resolved user cache is managed; the source-tree fallback may hold
  // explicit --out bundles and is never pruned.
  bool sharedCache = false;
  if (options->out.empty()) {
    const std::filesystem::path cache = platform::writableCacheSubdirectory("observer_sky");
    sharedCache = !cache.empty();
    options->out = sharedCache ? cache : platform::resourceRoot() / "assets" / "luts";
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
  const bool written = sky::writeObserverSkyLut(
      lut, options->out,
      sharedCache ? std::optional<std::uintmax_t>(sky::K_OBSERVER_SKY_CACHE_BYTES) : std::nullopt);
  const std::uint64_t hash = sky::lutHash(lut.key, lut.dimensions, lut.settings);
  if (!written) {
    std::printf("could not write %s\n", options->out.string().c_str());
    return 1;
  }
  const std::string stem = sky::lutStem(hash);
  std::printf("wrote %s/%s.{bin,json}\n", options->out.string().c_str(), stem.c_str());
  return 0;
}
