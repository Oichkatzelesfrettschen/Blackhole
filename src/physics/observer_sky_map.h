/**
 * @file observer_sky_map.h
 * @brief The sky seen by an equatorial Kerr observer: backward null geodesics
 *        from the observer's local celestial sphere to infinity, in the spin
 *        deficit parameterization of kerr_observer.h.
 *
 * Units are G = c = M = 1. An observer is keyed by (epsilon, x, v): the spin
 * deficit epsilon = 1 - a, the radial offset x = r - 1, and the azimuthal speed
 * v it moves with relative to the local ZAMO (0 for the ZAMO itself,
 * circularOrbit().zamoVelocity for a circular geodesic,
 * staticObserverVelocity() for a static observer).
 *
 * A pixel of the local sky is traced backward along the photon it receives,
 * with the second-order Mino-time system r'' = R'(r)/2, theta'' =
 * Theta'(theta)/2 of kerr.h, rewritten in x and in the constant
 * k0 = 1 + a^2 - a lambda so that the radial potential R = P^2 - Delta Q,
 * P = x (2 + x) + k0, keeps its digits where P and Delta are both of order
 * 1e-5 (the canon Miller orbit at 1 - a = 1.3e-14). A float or a (r, a)
 * formulation cannot: there the horizon offset is 1.6e-7 and the ZAMO lapse
 * squared is 3.5e-10, so r = 1 + x and 1 - a^2 round the physics away.
 *
 * Local sky coordinates follow Opatrny, Richterek & Bakala (arXiv:1601.02897,
 * Fig. 3): longitude 0 looks at the hole (-e_r), longitude +90 deg looks along
 * the observer's motion (+e_phi), 180 deg looks straight out; latitude is
 * positive toward the spin axis (-e_theta). The escape direction is the
 * direction of the source at infinity, as a unit vector in a frame with X
 * toward the observer's azimuth phi_obs, Z along the spin axis, and
 * Y = Z x X. A sky fixed at infinity then appears rotated about Z by the
 * observer's accumulated azimuth, which the renderer applies as
 * skyPhiOffset = Omega t mod 2 pi.
 */

#ifndef BLACKHOLE_PHYSICS_OBSERVER_SKY_MAP_H
#define BLACKHOLE_PHYSICS_OBSERVER_SKY_MAP_H

#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

#include "kerr_observer.h"

namespace physics::observer_sky {

using kerr_observer::Tetrad;
using kerr_observer::Vec3;

/** @brief An equatorial observer: spin deficit, radial offset, and azimuthal
 *         ZAMO-frame speed along +phi (|velocity| < 1). */
struct ObserverKey {
  double epsilon = 1.0;
  double x = 5.0;
  double velocity = 0.0;
};

/** @brief ZAMO-frame speed of the circular geodesic of one sense at (epsilon, x),
 *         or nothing where no timelike circular orbit exists. */
[[nodiscard]] std::optional<ObserverKey> orbitingObserver(double epsilon, double x,
                                                          kerr_observer::OrbitSense sense);

/** @brief The observer's tetrad: the ZAMO tetrad boosted by `velocity` along e_phi. */
[[nodiscard]] Tetrad observerTetrad(const ObserverKey &key);

/** @brief Look direction on the tetrad's (r, theta, phi) legs for a local sky
 *         longitude and latitude in radians (conventions in the file comment). */
[[nodiscard]] Vec3 lookDirection(double longitude, double latitude);

/** @brief Local sky longitude and latitude (radians) of a unit look direction. */
struct SkyAngles {
  double longitude = 0.0;
  double latitude = 0.0;
};
[[nodiscard]] SkyAngles lookAngles(const Vec3 &look);

/** @brief Integration and termination controls for one backward ray. */
struct TraceSettings {
  /// Fraction of the local length scale one step may cover: the offset from
  /// the outer horizon x - h radially, one radian in theta. RK4 error per
  /// step scales as stepFraction^5.
  double stepFraction = 0.02;
  /// A ray moving outward (backward in time) beyond this radius has left
  /// every turning point: outside the photon region R has no zero ahead of
  /// an outgoing photon.
  double escapeRadius = 1.0e4;
  /// A ray moving inward closer than captureFraction * h to the outer
  /// horizon is captured; at h = 0 (extremal spin) captureFloor applies.
  double captureFraction = 1.0e-3;
  double captureFloor = 1.0e-12;
  /// Rays still bound after this many steps wind on the photon shell; they
  /// are reported Trapped and drawn with the shadow.
  int maxSteps = 200000;
};

/** @brief Where a pixel's backward ray ends. */
enum class RayFate : std::uint8_t {
  Escaped = 0,  ///< Reached infinity: the pixel shows the sky.
  Captured = 1, ///< Traced back to the horizon, or the photon has E <= 0.
  Trapped = 2,  ///< Hit maxSteps near the photon shell, or left the finite range.
};

/** @brief One traced pixel. */
struct SkyRay {
  RayFate fate = RayFate::Captured;
  /// Unit direction of the source at infinity (frame in the file comment).
  Vec3 sourceDirection{0.0, 0.0, 0.0};
  /// nu_observed / nu_infinity = 1 / E for a photon of unit observed energy.
  double g = 0.0;
  /// Boyer-Lindquist azimuth swept from the observer to the escape point.
  double sweptPhi = 0.0;
  int steps = 0;
};

/** @brief Traces the photon received along `look` backward from the observer. */
[[nodiscard]] SkyRay traceSkyRay(const Tetrad &tetrad, const Vec3 &look,
                                 const TraceSettings &settings);

/** @brief ln g stored for a Captured pixel and for a Trapped one; neither
 *         shows sky, and every real ln g exceeds both by orders of magnitude,
 *         so any stored value below K_NO_SKY_THRESHOLD marks a shadow pixel. */
inline constexpr float K_CAPTURED_LOG_G = -1.0e4F;
inline constexpr float K_TRAPPED_LOG_G = -2.0e4F;
inline constexpr float K_NO_SKY_THRESHOLD = -5.0e3F;

/** @brief Look direction of equirectangular pixel (column, row): longitude
 *         -pi + 2 pi (column + 1/2) / width, latitude pi/2 - pi (row + 1/2) / height,
 *         so row 0 is the northern edge. */
[[nodiscard]] Vec3 equirectLook(std::size_t column, std::size_t row, std::size_t width,
                                std::size_t height);

/** @brief Solid angle (sr) of an equirectangular pixel in `row`. */
[[nodiscard]] double equirectPixelSolidAngle(std::size_t row, std::size_t width,
                                             std::size_t height);

/**
 * @brief A log-polar tile centered on one look direction: texel (radial i,
 *        azimuthal j) looks along cos(rho) center + sin(rho) (cos(psi) axisEast
 *        + sin(psi) axisNorth), with ln rho uniform on [ln rhoMin, ln rhoMax]
 *        and psi uniform on [0, 2 pi). It resolves features from rhoMin to
 *        rhoMax with a constant relative pitch, which an equirectangular map
 *        cannot do for a patch of arcseconds.
 */
struct LogPolarTile {
  Vec3 center{1.0, 0.0, 0.0};
  Vec3 axisEast{0.0, 0.0, 1.0};   ///< Unit tangent toward increasing longitude.
  Vec3 axisNorth{0.0, -1.0, 0.0}; ///< Unit tangent toward increasing latitude.
  double rhoMin = 1.0e-10;
  double rhoMax = 0.2;
  std::size_t radialCount = 512;
  std::size_t azimuthCount = 512;
};

/** @brief Tile with its axes set to the local east and north at `center`. */
[[nodiscard]] LogPolarTile tileAround(const Vec3 &center, double rhoMin, double rhoMax,
                                      std::size_t radialCount, std::size_t azimuthCount);

/** @brief Look direction of tile texel (radial, azimuthal). */
[[nodiscard]] Vec3 tileLook(const LogPolarTile &tile, std::size_t radial, std::size_t azimuthal);

/** @brief Solid angle (sr) of any texel in radial ring `radial`. */
[[nodiscard]] double tileTexelSolidAngle(const LogPolarTile &tile, std::size_t radial);

/** @brief RGBA32F texels: rgb = source direction, a = ln g, K_CAPTURED_LOG_G, or K_TRAPPED_LOG_G.
 */
struct SkyImage {
  std::size_t width = 0;
  std::size_t height = 0;
  std::vector<float> rgba;
  /// Rays whose deficit-form fate disagrees with photonConstants' static
  /// radial-potential connectivity (fromInfinity), counted for review.
  std::size_t connectivityDisagreements = 0;
};

/** @brief Traces every pixel of a width x height equirectangular sky. Rows are
 *         independent; `threads` 0 uses the hardware concurrency. The result
 *         does not depend on the thread count. */
[[nodiscard]] SkyImage traceEquirect(const ObserverKey &key, std::size_t width, std::size_t height,
                                     const TraceSettings &settings, unsigned threads = 0);

/** @brief Traces every texel of a log-polar tile (width = azimuthCount,
 *         height = radialCount). */
[[nodiscard]] SkyImage traceTile(const ObserverKey &key, const LogPolarTile &tile,
                                 const TraceSettings &settings, unsigned threads = 0);

/** @brief Look direction of the photon that falls radially inward in the ZAMO
 *         frame, aberrated into the observer's frame: longitude pi - asin(v),
 *         latitude 0. Near an extremal horizon every photon from the
 *         distant universe arrives within a few x of this direction. */
[[nodiscard]] Vec3 zamoZenithLook(double velocity);

/**
 * @brief The escaping look direction of greatest g, refined from `seeds` by
 *        successively finer grid searches in the tangent plane (each level
 *        shrinks the half-width by `shrink`, down to `finestHalfWidth`).
 *        The supremum of g sits on the shadow boundary, so the result is the
 *        escaping direction nearest it at the finest level.
 */
struct PeakSearch {
  double initialHalfWidth = 0.02;
  double finestHalfWidth = 1.0e-10;
  double shrink = 4.0;
  std::size_t gridPoints = 17;
};
struct PeakResult {
  Vec3 look{1.0, 0.0, 0.0};
  double g = 0.0;
};
[[nodiscard]] PeakResult findPeakBlueshift(const Tetrad &tetrad, const std::vector<Vec3> &seeds,
                                           const PeakSearch &search, const TraceSettings &settings);

/** @brief Whole-sky statistics of an equirectangular image. */
struct SkyStatistics {
  double capturedFraction = 0.0; ///< Solid-angle fraction showing no sky (Captured + Trapped).
  double trappedFraction = 0.0;  ///< Solid-angle fraction that hit maxSteps.
  double gMin = 0.0;             ///< Over escaping pixels.
  double gMax = 0.0;
};
[[nodiscard]] SkyStatistics equirectStatistics(const SkyImage &image);

/**
 * @brief The smallest set of tile texels that carries `fraction` of the
 *        bolometric energy g^4 dOmega received from an isotropic sky over the
 *        tile, and its extent in local longitude and latitude (radians).
 *        Texels are ranked by g^4 dOmega / dOmega = g^4 (brightest first), so
 *        the set is the region above an intensity threshold -- the natural
 *        reading of "the strip that delivers 99% of the energy".
 */
struct EnergyRegion {
  double tileEnergy = 0.0; ///< Integral of g^4 dOmega over the tile (sr).
  double longitudeSpan = 0.0;
  double latitudeSpan = 0.0;
  double solidAngle = 0.0; ///< Of the selected texels (sr).
  double thresholdG = 0.0; ///< Smallest g in the selected set.
};
[[nodiscard]] EnergyRegion tileEnergyRegion(const SkyImage &image, const LogPolarTile &tile,
                                            double fraction);

} // namespace physics::observer_sky

#endif // BLACKHOLE_PHYSICS_OBSERVER_SKY_MAP_H
