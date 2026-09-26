/**
 * @file observer_sky_lut.h
 * @brief The observer-sky lookup bundle: an equirectangular sky map plus a
 *        log-polar tile on the peak-blueshift patch, their statistics, and a
 *        content-addressed binary cache with a JSON sidecar.
 *
 * The bundle is keyed only by the observer (epsilon, x, v), the map
 * dimensions, and the trace settings; lutHash folds exactly those inputs, so
 * a file whose name carries the hash can be reused without re-tracing. The
 * binary is little-endian: an 8-byte magic, the format version, the key,
 * dimensions and settings, the tile frame, the statistics, then the two
 * RGBA32F images row-major (equirectangular first). Every double is written
 * through its bit pattern, so a read reproduces the build bit for bit on the
 * same host.
 */

#ifndef BLACKHOLE_PHYSICS_OBSERVER_SKY_LUT_H
#define BLACKHOLE_PHYSICS_OBSERVER_SKY_LUT_H

#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <optional>
#include <string>

#include "observer_sky_map.h"

namespace physics::observer_sky {

/** @brief Resolution of both images and the tile's radial range (radians). */
struct LutDimensions {
  std::size_t width = 1024;
  std::size_t height = 512;
  std::size_t tileRadial = 512;
  std::size_t tileAzimuth = 512;
  double tileRhoMin = 1.0e-9;
  double tileRhoMax = 0.25;
};

/** @brief Statistics carried in the bundle for the UI and the sidecar. */
struct LutStatistics {
  double capturedFraction = 0.0; ///< Shadow solid-angle fraction (equirect map).
  double trappedFraction = 0.0;
  double gMin = 0.0;                 ///< Over escaping equirect pixels.
  double gMax = 0.0;                 ///< Refined peak (findPeakBlueshift).
  double patch99LongitudeSpan = 0.0; ///< Radians; the 99% bolometric-energy region.
  double patch99LatitudeSpan = 0.0;
  double patch99SolidAngle = 0.0;
  double patch99ThresholdG = 0.0;
  double tileEnergy = 0.0;        ///< Integral of g^4 dOmega over the tile.
  double energyOutsideTile = 0.0; ///< The same over the equirect map outside the tile.
  /// (Integral g^4 dOmega / 4 pi)^(1/4): an isotropic blackbody at g T0
  /// delivers the same energy density as the whole observed sky.
  double equivalentIsotropicG = 0.0;
  /// Integral g^5 dOmega / Integral g^4 dOmega: the mean g of received energy.
  double energyWeightedG = 0.0;
  std::uint64_t connectivityDisagreements = 0;
};

struct ObserverSkyLut {
  ObserverKey key;
  LutDimensions dimensions;
  TraceSettings settings;
  LogPolarTile tile;
  PeakResult peak;
  LutStatistics statistics;
  SkyImage sky;       ///< width x height equirectangular.
  SkyImage tileImage; ///< tileAzimuth x tileRadial log-polar.
};

/** @brief Increments whenever the binary layout or the traced content changes. */
inline constexpr std::uint32_t K_LUT_FORMAT_VERSION = 1;

/** @brief FNV-1a over the format version and every input that shapes the bundle. */
[[nodiscard]] std::uint64_t lutHash(const ObserverKey &key, const LutDimensions &dimensions,
                                    const TraceSettings &settings);

/** @brief "observer_sky_<16 hex digits>", the bundle's file stem. */
[[nodiscard]] std::string lutStem(std::uint64_t hash);

/** @brief Traces both images, locates the peak, and fills the statistics.
 *         Deterministic for a given host and binary; `threads` 0 uses the
 *         hardware concurrency. */
[[nodiscard]] ObserverSkyLut buildObserverSkyLut(const ObserverKey &key,
                                                 const LutDimensions &dimensions,
                                                 const TraceSettings &settings,
                                                 unsigned threads = 0);

/** @brief Writes <dir>/<stem>.bin and <dir>/<stem>.json; false on any I/O error. */
bool writeObserverSkyLut(const ObserverSkyLut &lut, const std::filesystem::path &directory);

/** @brief Reads a bundle; nothing when the file is missing, truncated, of
 *         another format version, or its stored inputs do not hash to `expectedHash`. */
[[nodiscard]] std::optional<ObserverSkyLut> readObserverSkyLut(const std::filesystem::path &file,
                                                               std::uint64_t expectedHash);

/** @brief The JSON sidecar text (key, settings, tile frame, statistics). */
[[nodiscard]] std::string lutSidecarJson(const ObserverSkyLut &lut);

} // namespace physics::observer_sky

#endif // BLACKHOLE_PHYSICS_OBSERVER_SKY_LUT_H
