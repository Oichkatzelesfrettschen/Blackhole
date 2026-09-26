/**
 * @file observer_sky_map_test.cpp
 * @brief Falsification gates for physics/observer_sky_map.h and
 *        observer_sky_lut.h: special-relativistic limits far from the hole,
 *        Synge's shadow for a static Schwarzschild observer, and the three
 *        orbiting observers of Opatrny, Richterek & Bakala, "Life under a
 *        black sun" (arXiv:1601.02897v2, Am. J. Phys. 85, 14 (2017)).
 *
 * Paper values come from two places. The text states shadow fractions
 * (12.2%, 26%, 40%), peak blueshifts (3/sqrt(2), 6.90, 275,000), and a 99%
 * energy strip (2.3 x 5.8 arcsec). Figures 3 and 4 are vector graphics: the
 * shadow polygons, the Fig. 4 boundary curve, and the Fig. 4 contour
 * segments were read from `pdftocairo -svg -f 4 -l 4` of the arXiv PDF, with
 * the Mollweide ellipse and the Fig. 4 axis ticks as the calibration, so
 * those numbers carry the figure's drawing precision (about 0.3 deg in
 * Fig. 3, 0.05 arcsec in Fig. 4) rather than a pixel reading. Where the text
 * and the figure disagree (Miller's shadow: 40% in the text, 45.7% in
 * Fig. 3(c)) the gate asserts the figure and says so.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <numbers>
#include <optional>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include "kerr_observer.h"
#include "observer_sky_lut.h"
#include "observer_sky_map.h"

namespace {

namespace ko = physics::kerr_observer;
namespace sky = physics::observer_sky;

constexpr double K_PI = std::numbers::pi;
constexpr double K_DEGREE = K_PI / 180.0;
constexpr double K_ARCSECOND = K_DEGREE / 3600.0;

/// The paper's Miller orbit: a = 1 - 1.3e-14, r = 1.0000379 M (Sec. IV B).
constexpr double K_PAPER_DEFICIT = 1.3e-14;
constexpr double K_PAPER_MILLER_X = 3.79e-5;

sky::TraceSettings defaultSettings() {
  return sky::TraceSettings{};
}

double dot3(const sky::Vec3 &a, const sky::Vec3 &b) {
  return (a.at(0) * b.at(0)) + (a.at(1) * b.at(1)) + (a.at(2) * b.at(2));
}

double angleBetween(const sky::Vec3 &a, const sky::Vec3 &b) {
  const sky::Vec3 cross{(a.at(1) * b.at(2)) - (a.at(2) * b.at(1)),
                        (a.at(2) * b.at(0)) - (a.at(0) * b.at(2)),
                        (a.at(0) * b.at(1)) - (a.at(1) * b.at(0))};
  return std::atan2(std::sqrt(dot3(cross, cross)), dot3(a, b));
}

bool escapes(const sky::Tetrad &tetrad, double longitude, double latitude) {
  return sky::traceSkyRay(tetrad, sky::lookDirection(longitude, latitude), defaultSettings())
             .fate == sky::RayFate::Escaped;
}

/** @brief Longitude in [low, high] where a ray's fate flips at one latitude,
 *         by bisection; `low` and `high` must bracket exactly one flip. */
double fateEdge(const sky::Tetrad &tetrad, double low, double high, double latitude) {
  const bool lowEscapes = escapes(tetrad, low, latitude);
  EXPECT_NE(lowEscapes, escapes(tetrad, high, latitude)) << "bracket holds no edge";
  for (int iteration = 0; iteration < 60; ++iteration) {
    const double middle = 0.5 * (low + high);
    (escapes(tetrad, middle, latitude) == lowEscapes ? low : high) = middle;
  }
  return 0.5 * (low + high);
}

sky::ObserverKey orbiting(double epsilon, double x) {
  const auto key = sky::orbitingObserver(epsilon, x, ko::OrbitSense::Prograde);
  EXPECT_TRUE(key.has_value());
  return key.value_or(sky::ObserverKey{});
}

// ---------------------------------------------------------------------------
// Special relativity far from the hole
// ---------------------------------------------------------------------------

/**
 * At r = 1e8 M the metric differs from Minkowski by 2M/r = 2e-8 and light
 * bends by at most 4M/b, so an observer moving at v along e_phi relative to
 * the static frame sees pure aberration and Doppler shift. With th the angle
 * between the look direction and the motion in the static frame and th' the
 * same angle in the moving frame,
 *   cos th' = (cos th + v) / (1 + v cos th),
 *   g = gamma (1 + v cos th) = 1 / (gamma (1 - v cos th')),
 * times the static blueshift 1/sqrt(1 - 2/r). The source of the pixel lies
 * along the static-frame look direction, whose Cartesian components follow
 * from e_r = X, e_theta = -Z, e_phi = Y at the observer's azimuth.
 */
TEST(ObserverSkyMap, FarObserverSeesSpecialRelativisticAberration) {
  constexpr double r = 1.0e8;
  constexpr double v = 0.6;
  const double gamma = 1.0 / std::sqrt(1.0 - (v * v));
  const double staticBlueshift = 1.0 / std::sqrt(1.0 - (2.0 / r));
  // a = 0: the ZAMO is the static observer.
  const sky::ObserverKey key{.epsilon = 1.0, .x = r - 1.0, .velocity = v};
  const sky::Tetrad tetrad = sky::observerTetrad(key);
  // Look directions at least 20 deg from the hole (longitude 0), where the
  // bending 4M/b stays below 1.2e-7 rad.
  const std::array<std::pair<double, double>, 7> looks{{{90.0, 0.0},
                                                        {-90.0, 0.0},
                                                        {150.0, 0.0},
                                                        {45.0, 30.0},
                                                        {-120.0, -45.0},
                                                        {180.0, 60.0},
                                                        {30.0, -10.0}}};
  for (const auto &[longitudeDeg, latitudeDeg] : looks) {
    const sky::Vec3 look = sky::lookDirection(longitudeDeg * K_DEGREE, latitudeDeg * K_DEGREE);
    const sky::SkyRay ray = sky::traceSkyRay(tetrad, look, defaultSettings());
    ASSERT_EQ(ray.fate, sky::RayFate::Escaped) << longitudeDeg << " " << latitudeDeg;
    const double cosPrime = look.at(2); // Angle to e_phi, the direction of motion.
    const double cosStatic = (cosPrime - v) / (1.0 - (v * cosPrime));
    EXPECT_NEAR(cosPrime, (cosStatic + v) / (1.0 + (v * cosStatic)), 1e-15);
    const double gExpected = staticBlueshift / (gamma * (1.0 - (v * cosPrime)));
    EXPECT_NEAR(ray.g / gExpected, 1.0, 1e-12) << longitudeDeg << " " << latitudeDeg;
    EXPECT_NEAR(gamma * (1.0 + (v * cosStatic)) * staticBlueshift / gExpected, 1.0, 1e-12);
    // Static-frame look direction: the transverse part keeps its direction
    // and the component along e_phi becomes cosStatic; along the motion
    // itself (no transverse part) the direction is unchanged.
    const double transverse = std::sqrt(1.0 - (cosPrime * cosPrime));
    const double scale =
        transverse > 0.0 ? std::sqrt(1.0 - (cosStatic * cosStatic)) / transverse : 0.0;
    const sky::Vec3 staticLook{look.at(0) * scale, look.at(1) * scale, cosStatic};
    const sky::Vec3 source{staticLook.at(0), staticLook.at(2), -staticLook.at(1)};
    // Bending contributes under 2e-7 rad; RK4 at stepFraction 0.02 adds about
    // 1e-6 rad across periapsis, three orders below a LUT pixel (6e-3 rad).
    EXPECT_LT(angleBetween(ray.sourceDirection, source), 3.0e-6)
        << longitudeDeg << " " << latitudeDeg;
  }
}

// ---------------------------------------------------------------------------
// Synge's shadow for a static Schwarzschild observer
// ---------------------------------------------------------------------------

/**
 * A static observer at radius r >= 3M around a Schwarzschild hole sees a
 * circular shadow of angular radius psi, sin psi = 3 sqrt(3) sqrt(1 - 2/r) / r
 * (Synge 1966), centered on the hole, covering (1 - cos psi)/2 of the sky.
 * At a = 0 the ZAMO is the static observer. The equatorial edge is located
 * by bisection to 1e-12 rad and the solid-angle fraction from an
 * equal-area-weighted 256 x 128 map, whose boundary pixels bound the error
 * at about 2 pi psi / 256 / (4 pi) of the sky.
 */
TEST(ObserverSkyMap, StaticSchwarzschildShadowMatchesSynge) {
  for (const double r : {4.0, 6.0, 10.0, 20.0}) {
    const sky::ObserverKey key{.epsilon = 1.0, .x = r - 1.0, .velocity = 0.0};
    const sky::Tetrad tetrad = sky::observerTetrad(key);
    const double psi = std::asin(3.0 * std::numbers::sqrt3 * std::sqrt(1.0 - (2.0 / r)) / r);
    EXPECT_NEAR(fateEdge(tetrad, 0.5 * psi, 1.5 * psi, 0.0), psi, 2.0e-5) << "r = " << r;
    EXPECT_NEAR(-fateEdge(tetrad, -1.5 * psi, -0.5 * psi, 0.0), psi, 2.0e-5) << "r = " << r;
    const sky::SkyImage image = sky::traceEquirect(key, 256, 128, defaultSettings());
    const sky::SkyStatistics stats = sky::equirectStatistics(image);
    EXPECT_NEAR(stats.capturedFraction, 0.5 * (1.0 - std::cos(psi)), 0.004) << "r = " << r;
    EXPECT_EQ(stats.trappedFraction, 0.0);
    // Light from infinity reaches a static observer with g = 1/sqrt(1 - 2/r)
    // whatever its direction; the image stores ln g as a float, which rounds
    // g to 1e-7.
    EXPECT_NEAR(stats.gMin * std::sqrt(1.0 - (2.0 / r)), 1.0, 1e-7);
    EXPECT_NEAR(stats.gMax * std::sqrt(1.0 - (2.0 / r)), 1.0, 1e-7);
    const sky::SkyRay outward =
        sky::traceSkyRay(tetrad, sky::lookDirection(0.75 * K_PI, 0.3), defaultSettings());
    EXPECT_NEAR(outward.g * std::sqrt(1.0 - (2.0 / r)), 1.0, 1e-14);
    // At a = 0 the static radial-potential classifier is exact.
    EXPECT_EQ(image.connectivityDisagreements, 0U);
  }
}

// ---------------------------------------------------------------------------
// Opatrny, Richterek & Bakala, Fig. 3(a): Schwarzschild ISCO
// ---------------------------------------------------------------------------

/**
 * Circular geodesic at r = 6M, v = 1/2. The paper's text gives the shadow as
 * 12.2% of the sky and g = 3/sqrt(2) ahead, 1/sqrt(2) behind (Eq. A12). The
 * shadow is Synge's 45 deg cap aberrated by v: its equatorial edges sit where
 * the static-frame angles 45 and 135 deg from the motion land, cos th' =
 * (cos th + v)/(1 + v cos th), at longitudes 90 deg - th'. The vector Fig. 3(a)
 * polygon covers 12.35% with equatorial edges at -18.98 and 63.41 deg.
 */
TEST(ObserverSkyMap, SchwarzschildIscoMatchesOpatrnyFigure3a) {
  const sky::ObserverKey key = orbiting(1.0, 5.0);
  EXPECT_NEAR(key.velocity, 0.5, 1e-15);
  const sky::Tetrad tetrad = sky::observerTetrad(key);
  const auto aberrated = [](double staticAngle) {
    return std::acos((std::cos(staticAngle) + 0.5) / (1.0 + (0.5 * std::cos(staticAngle))));
  };
  const double leadingEdge = 0.5 * K_PI - aberrated(0.25 * K_PI);
  const double trailingEdge = 0.5 * K_PI - aberrated(0.75 * K_PI);
  EXPECT_NEAR(fateEdge(tetrad, 40.0 * K_DEGREE, 80.0 * K_DEGREE, 0.0), leadingEdge, 2.0e-5);
  EXPECT_NEAR(fateEdge(tetrad, -40.0 * K_DEGREE, 0.0, 0.0), trailingEdge, 2.0e-5);
  // Against the drawn polygon, to its 0.3 deg drawing precision plus margin.
  EXPECT_NEAR(leadingEdge / K_DEGREE, 63.41, 0.5);
  EXPECT_NEAR(trailingEdge / K_DEGREE, -18.98, 0.5);

  const sky::ObserverSkyLut lut = sky::buildObserverSkyLut(
      key, sky::LutDimensions{.width = 256, .height = 128, .tileRadial = 32, .tileAzimuth = 32},
      defaultSettings());
  EXPECT_NEAR(lut.statistics.capturedFraction, 0.122, 0.003);
  EXPECT_NEAR(lut.statistics.gMax, 3.0 / std::sqrt(2.0), 1e-9);
  const sky::SkyRay behind =
      sky::traceSkyRay(tetrad, sky::lookDirection(-0.5 * K_PI, 0.0), defaultSettings());
  EXPECT_NEAR(behind.g, 1.0 / std::sqrt(2.0), 1e-12);
  const sky::SkyAngles peak = sky::lookAngles(lut.peak.look);
  EXPECT_NEAR(peak.longitude, 0.5 * K_PI, 1e-6) << "the peak blueshift looks along the motion";
}

// ---------------------------------------------------------------------------
// Fig. 3(b): a = 1 - 1.3e-14, r = 2.2 M
// ---------------------------------------------------------------------------

/**
 * Text: shadow 26% of the sky, maximum blueshift 6.90. Vector Fig. 3(b):
 * 26.06%, equatorial edges at 5.62 and 117.49 deg.
 */
TEST(ObserverSkyMap, NearExtremalAt2p2MatchesOpatrnyFigure3b) {
  const sky::ObserverKey key = orbiting(K_PAPER_DEFICIT, 1.2);
  const sky::Tetrad tetrad = sky::observerTetrad(key);
  EXPECT_NEAR(fateEdge(tetrad, 0.0, 20.0 * K_DEGREE, 0.0) / K_DEGREE, 5.62, 0.5);
  EXPECT_NEAR(fateEdge(tetrad, 100.0 * K_DEGREE, 130.0 * K_DEGREE, 0.0) / K_DEGREE, 117.49, 0.5);
  const sky::ObserverSkyLut lut = sky::buildObserverSkyLut(
      key, sky::LutDimensions{.width = 256, .height = 128, .tileRadial = 32, .tileAzimuth = 32},
      defaultSettings());
  EXPECT_NEAR(lut.statistics.capturedFraction, 0.26, 0.005);
  EXPECT_NEAR(lut.statistics.gMax, 6.90, 0.07);
}

// ---------------------------------------------------------------------------
// Fig. 3(c) and Fig. 4: Miller's planet, a = 1 - 1.3e-14, r = 1.0000379 M
// ---------------------------------------------------------------------------

/**
 * Shadow and equatorial edges against the vector Fig. 3(c): the polygon
 * covers 45.7% of the ellipse, with equatorial edges at -0.30 and 150.44 deg
 * and the far edge at 163.64 deg for latitude 30 deg. The text's "40%" is
 * not what the figure draws; the gate follows the figure. The blueshift
 * floor 1/sqrt(3) is the near-horizon bound Gralla, Lupsasca & Strominger
 * (arXiv:1710.11112, Eq. 3.14) derive for light between an extremal ISCO and
 * infinity, here read in the receiving direction.
 */
TEST(ObserverSkyMap, MillerShadowMatchesOpatrnyFigure3c) {
  const sky::ObserverKey key = orbiting(K_PAPER_DEFICIT, K_PAPER_MILLER_X);
  const sky::Tetrad tetrad = sky::observerTetrad(key);
  EXPECT_NEAR(fateEdge(tetrad, -10.0 * K_DEGREE, 10.0 * K_DEGREE, 0.0) / K_DEGREE, -0.30, 0.5);
  EXPECT_NEAR(fateEdge(tetrad, 120.0 * K_DEGREE, 170.0 * K_DEGREE, 0.0) / K_DEGREE, 150.44, 0.5);
  EXPECT_NEAR(fateEdge(tetrad, 140.0 * K_DEGREE, 175.0 * K_DEGREE, 30.0 * K_DEGREE) / K_DEGREE,
              163.64, 1.0);
  const sky::SkyImage image = sky::traceEquirect(key, 256, 128, defaultSettings());
  const sky::SkyStatistics stats = sky::equirectStatistics(image);
  EXPECT_NEAR(stats.capturedFraction, 0.457, 0.01);
  EXPECT_NEAR(stats.gMin, 1.0 / std::sqrt(3.0), 2e-4);
}

/**
 * Fig. 4 (vector): the shadow boundary near longitude 150 deg, as dphi =
 * longitude - 150 deg against latitude, and the constant-g contours, which
 * the figure draws as vertical segments -- g depends on dphi alone inside the
 * boundary. Digitized: boundary vertex -5.851 arcsec; boundary at latitude
 * +-5 / +-10 / +-20 arcsec: -5.630 / -4.86 / -2.31 arcsec; contours g =
 * 250,000 / 200,000 / 150,000 / 100,000 / 50,000 at dphi = -5.816 / -5.701 /
 * -5.293 / -4.447 / -2.486 arcsec. Text: peak g "up to 275,000".
 *
 * Tolerances: 0.3 arcsec on the boundary (the orbit speed v enters as
 * asin(v); a 1e-6 change in v moves the boundary 0.2 arcsec, and the paper
 * quotes r to 8 digits), 12% on the contour values (a 0.1 arcsec shift at the
 * steep end changes g by 10%), 2% on the peak.
 */
TEST(ObserverSkyMap, MillerPatchMatchesOpatrnyFigure4) {
  const sky::ObserverKey key = orbiting(K_PAPER_DEFICIT, K_PAPER_MILLER_X);
  const sky::Tetrad tetrad = sky::observerTetrad(key);
  const double reference = 150.0 * K_DEGREE;
  const auto boundary = [&](double latitudeArcsec) {
    return (fateEdge(tetrad, reference - (20.0 * K_ARCSECOND), reference + (5.0 * K_ARCSECOND),
                     latitudeArcsec * K_ARCSECOND) -
            reference) /
           K_ARCSECOND;
  };
  EXPECT_NEAR(boundary(0.0), -5.851, 0.3);
  EXPECT_NEAR(boundary(5.0), -5.630, 0.3);
  EXPECT_NEAR(boundary(-5.0), -5.630, 0.3);
  EXPECT_NEAR(boundary(10.0), -4.86, 0.3);
  EXPECT_NEAR(boundary(20.0), -2.31, 0.3);

  const std::array<std::pair<double, double>, 5> contours{{{-5.816, 250000.0},
                                                           {-5.701, 200000.0},
                                                           {-5.293, 150000.0},
                                                           {-4.447, 100000.0},
                                                           {-2.486, 50000.0}}};
  for (const auto &[dphi, gContour] : contours) {
    const sky::SkyRay onEquator = sky::traceSkyRay(
        tetrad, sky::lookDirection(reference + (dphi * K_ARCSECOND), 0.0), defaultSettings());
    ASSERT_EQ(onEquator.fate, sky::RayFate::Escaped);
    EXPECT_NEAR(onEquator.g / gContour, 1.0, 0.12) << "dphi " << dphi;
    // Vertical contours: the same g one arcsecond off the equator.
    const sky::SkyRay offEquator =
        sky::traceSkyRay(tetrad, sky::lookDirection(reference + (dphi * K_ARCSECOND), K_ARCSECOND),
                         defaultSettings());
    ASSERT_EQ(offEquator.fate, sky::RayFate::Escaped);
    EXPECT_NEAR(offEquator.g / onEquator.g, 1.0, 1e-4) << "dphi " << dphi;
  }

  const sky::PeakResult peak = sky::findPeakBlueshift(tetrad, {sky::zamoZenithLook(key.velocity)},
                                                      sky::PeakSearch{}, defaultSettings());
  EXPECT_NEAR(peak.g / 275000.0, 1.0, 0.02);
}

/**
 * The 99% energy strip. The text states 2.3 x 5.8 arcsec (longitude x
 * latitude). Its own Fig. 4 draws g constant along latitude out to the
 * boundary at +-27 arcsec, which places most of the energy in the parabola's
 * full height, not in a 5.8 arcsec band: the text figure is not reproducible
 * from the figure. The comparable claim -- that the energy sits in an
 * arcsecond-scale region hugging the shadow edge near longitude 150 deg -- is
 * asserted, with the region measured on a log-polar tile around the peak:
 * the 99% region spans under 10 arcsec in longitude and under 60 in latitude,
 * and the tile holds all but 1e-6 of the sky's energy.
 */
TEST(ObserverSkyMap, MillerEnergyConcentratesInArcsecondStrip) {
  const sky::ObserverKey key = orbiting(K_PAPER_DEFICIT, K_PAPER_MILLER_X);
  const sky::ObserverSkyLut lut = sky::buildObserverSkyLut(
      key, sky::LutDimensions{.width = 128, .height = 64, .tileRadial = 192, .tileAzimuth = 192},
      defaultSettings());
  const sky::LutStatistics &stats = lut.statistics;
  EXPECT_GT(stats.patch99LongitudeSpan / K_ARCSECOND, 2.3);
  EXPECT_LT(stats.patch99LongitudeSpan / K_ARCSECOND, 10.0);
  EXPECT_GT(stats.patch99LatitudeSpan / K_ARCSECOND, 5.8);
  EXPECT_LT(stats.patch99LatitudeSpan / K_ARCSECOND, 60.0);
  EXPECT_LT(stats.energyOutsideTile / stats.tileEnergy, 1e-6);
  const sky::SkyAngles peak = sky::lookAngles(lut.peak.look);
  EXPECT_NEAR((peak.longitude / K_ARCSECOND) - (150.0 * 3600.0), -5.851, 0.3);
}

// ---------------------------------------------------------------------------
// Numerical controls
// ---------------------------------------------------------------------------

/**
 * Halving the step leaves every pixel's fate and, up to one rotation about
 * the spin axis, its source direction unchanged. The rotation is the common
 * part of the error in the Boyer-Lindquist winding, about 1/x = 26,000 rad
 * for every ray that climbs out of the throat, and is indistinguishable from
 * the orbital phase the renderer adds, so it is fitted out. The remainder is
 * the ray-to-ray part: rays that linger in the throat wind further, and at
 * stepFraction 0.02 their winding carries a relative error near 4e-8, about
 * 1e-3 rad -- a sixth of the 1024-column map's 6.1e-3 rad pitch.
 */
TEST(ObserverSkyMap, MillerMapConvergesUnderStepHalving) {
  const sky::ObserverKey key = orbiting(K_PAPER_DEFICIT, K_PAPER_MILLER_X);
  sky::TraceSettings fine = defaultSettings();
  fine.stepFraction *= 0.5;
  const sky::SkyImage coarseImage = sky::traceEquirect(key, 64, 32, defaultSettings());
  const sky::SkyImage fineImage = sky::traceEquirect(key, 64, 32, fine);
  std::size_t fateChanges = 0;
  double sinSum = 0.0;
  double cosSum = 0.0;
  std::vector<std::pair<sky::Vec3, sky::Vec3>> pairs;
  for (std::size_t texel = 0; texel < std::size_t{64} * std::size_t{32}; ++texel) {
    const auto at = [texel](const sky::SkyImage &image, std::size_t channel) {
      return static_cast<double>(image.rgba.at((texel * 4) + channel));
    };
    const bool coarseSky = at(coarseImage, 3) > static_cast<double>(sky::K_NO_SKY_THRESHOLD);
    const bool fineSky = at(fineImage, 3) > static_cast<double>(sky::K_NO_SKY_THRESHOLD);
    fateChanges += coarseSky != fineSky ? 1U : 0U;
    if (!coarseSky || !fineSky) {
      continue;
    }
    EXPECT_NEAR(at(coarseImage, 3), at(fineImage, 3), 1e-6) << "ln g at texel " << texel;
    const sky::Vec3 a{at(coarseImage, 0), at(coarseImage, 1), at(coarseImage, 2)};
    const sky::Vec3 b{at(fineImage, 0), at(fineImage, 1), at(fineImage, 2)};
    // Rotation about Z taking a to b, weighted by the equatorial lever arm.
    sinSum += (a.at(0) * b.at(1)) - (a.at(1) * b.at(0));
    cosSum += (a.at(0) * b.at(0)) + (a.at(1) * b.at(1));
    pairs.emplace_back(a, b);
  }
  EXPECT_EQ(fateChanges, 0U);
  const double rotation = std::atan2(sinSum, cosSum);
  EXPECT_LT(std::fabs(rotation), 1e-3) << "winding error, rad";
  const double c = std::cos(rotation);
  const double s = std::sin(rotation);
  double worst = 0.0;
  for (const auto &[a, b] : pairs) {
    const sky::Vec3 rotated{(c * a.at(0)) - (s * a.at(1)), (s * a.at(0)) + (c * a.at(1)), a.at(2)};
    worst = std::max(worst, angleBetween(rotated, b));
  }
  EXPECT_LT(worst, 2e-3) << "rad after removing the common rotation";
}

/** @brief Write, read back, and reject a mismatched hash. */
TEST(ObserverSkyMap, LutRoundTripsThroughTheCache) {
  const sky::ObserverKey key = orbiting(0.1, 3.0);
  const sky::LutDimensions dimensions{.width = 32, .height = 16, .tileRadial = 8, .tileAzimuth = 8};
  const sky::ObserverSkyLut built = sky::buildObserverSkyLut(key, dimensions, defaultSettings(), 2);
  const std::filesystem::path directory =
      std::filesystem::temp_directory_path() / "observer_sky_map_test";
  ASSERT_TRUE(sky::writeObserverSkyLut(built, directory));
  const std::uint64_t hash = sky::lutHash(key, dimensions, defaultSettings());
  const std::filesystem::path file = directory / (sky::lutStem(hash) + ".bin");
  const std::optional<sky::ObserverSkyLut> read = sky::readObserverSkyLut(file, hash);
  if (!read.has_value()) {
    GTEST_FAIL() << "the written bundle did not read back";
  }
  const sky::ObserverSkyLut &loaded = *read;
  EXPECT_EQ(loaded.sky.rgba, built.sky.rgba);
  EXPECT_EQ(loaded.tileImage.rgba, built.tileImage.rgba);
  EXPECT_EQ(loaded.peak.g, built.peak.g);
  EXPECT_EQ(loaded.statistics.capturedFraction, built.statistics.capturedFraction);
  EXPECT_EQ(sky::lutSidecarJson(loaded), sky::lutSidecarJson(built));
  EXPECT_FALSE(sky::readObserverSkyLut(file, hash + 1).has_value());
  sky::TraceSettings other = defaultSettings();
  other.stepFraction = 0.01;
  EXPECT_NE(sky::lutHash(key, dimensions, other), hash);
  // A rebuild with a different thread count is bit-identical.
  EXPECT_EQ(sky::buildObserverSkyLut(key, dimensions, defaultSettings(), 1).sky.rgba,
            built.sky.rgba);
}

} // namespace
