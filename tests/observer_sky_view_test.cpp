/**
 * @file observer_sky_view_test.cpp
 * @brief Gates for the observer-sky scene's CPU side (render/observer_sky_view.h):
 *        the observer clock against kerr_observer's circular orbits and the
 *        canon Miller numbers, the sky phase, the camera geometry, and the
 *        blackbody table against the luminous efficacy of a Planck spectrum.
 *
 * Runs from the repository root (WORKING_DIRECTORY) so the committed
 * assets/luts/blackbody_cie_lut.csv resolves.
 */

#include <array>
#include <cmath>
#include <numbers>
#include <optional>

#include <gtest/gtest.h>

#include "physics/kerr_observer.h"
#include "physics/observer_sky_map.h"
#include "render/observer_sky_view.h"

namespace {

namespace ko = physics::kerr_observer;
namespace sky = physics::observer_sky;
using blackhole::ObserverKind;

constexpr double K_PI = std::numbers::pi;
constexpr double K_STEFAN_BOLTZMANN = 5.670374419e-8; // W m^-2 K^-4 (CODATA 2018, exact form)

sky::ObserverKey requireKey(const std::optional<sky::ObserverKey> &key) {
  EXPECT_TRUE(key.has_value());
  return key.value_or(sky::ObserverKey{});
}

sky::ObserverKey canonMiller() {
  const double x = ko::iscoOffset(blackhole::K_GARGANTUA_SPIN_DEFICIT, ko::OrbitSense::Prograde);
  const auto key =
      blackhole::observerKeyFor(blackhole::K_GARGANTUA_SPIN_DEFICIT, x, ObserverKind::Prograde);
  EXPECT_TRUE(key.has_value());
  return key.value_or(sky::ObserverKey{});
}

/**
 * The clock model's general form, dtau/dt = alpha sqrt(1 - v^2) and
 * Omega = omega + v alpha / varpi, must reproduce the Bardeen-Press-Teukolsky
 * orbit it is fed. At the canon Miller orbit (1 - a = 1.33e-14, prograde
 * ISCO) the canon numbers of docs/audits/physics-and-game-engine/03-game-engine.md
 * (section 4) follow: dtau/dt = 1.6286e-5 (one hour there is
 * seven years outside), Omega -> 1/(2M), a coordinate period of 4 pi M =
 * 1.72 h and a proper period of 0.10 s at M = 1e8 M_sun.
 */
TEST(ObserverSkyView, CanonClockMatchesMillerNumbers) {
  const sky::ObserverKey key = canonMiller();
  const ko::CircularOrbit orbit = ko::circularOrbit(key.epsilon, key.x, ko::OrbitSense::Prograde);
  const blackhole::ObserverClockModel clock = blackhole::observerClockModel(key, 1.0e8);
  EXPECT_NEAR(clock.properTimeRate / orbit.properTimeRate, 1.0, 1e-9);
  EXPECT_NEAR(clock.angularVelocity / orbit.angularVelocity, 1.0, 1e-12);
  EXPECT_NEAR(clock.properTimeRate, 1.6286e-5, 0.0001e-5);
  EXPECT_NEAR(1.0 / clock.properTimeRate / (7.0 * 365.25 * 24.0), 1.0, 0.005)
      << "one hour at Miller against seven outside years";
  EXPECT_NEAR(clock.secondsPerM, 492.549, 0.001);
  EXPECT_NEAR(clock.coordinatePeriodSeconds / (4.0 * K_PI * clock.secondsPerM), 1.0, 1e-4);
  EXPECT_NEAR(clock.coordinatePeriodSeconds / 3600.0, 1.719, 0.001);
  EXPECT_NEAR(clock.properPeriodSeconds, 0.1008, 0.0001);
}

TEST(ObserverSkyView, HoveringClocksAreTheLapseAndTheStaticRate) {
  const sky::ObserverKey zamo = requireKey(blackhole::observerKeyFor(0.1, 2.0, ObserverKind::Zamo));
  const ko::EquatorialFrame frame = ko::equatorialFrame(0.1, 2.0);
  const blackhole::ObserverClockModel zamoClock = blackhole::observerClockModel(zamo, 1.0);
  EXPECT_DOUBLE_EQ(zamoClock.properTimeRate, frame.alpha);
  EXPECT_DOUBLE_EQ(zamoClock.angularVelocity, frame.omega);

  // a = 0: the static observer is the ZAMO, dtau/dt = sqrt(1 - 2/r), Omega = 0.
  const sky::ObserverKey rest =
      requireKey(blackhole::observerKeyFor(1.0, 9.0, ObserverKind::Static));
  const blackhole::ObserverClockModel restClock = blackhole::observerClockModel(rest, 1.0);
  EXPECT_NEAR(restClock.properTimeRate, std::sqrt(1.0 - 0.2), 1e-15);
  EXPECT_EQ(restClock.angularVelocity, 0.0);
  EXPECT_EQ(restClock.coordinatePeriodSeconds, 0.0);
  EXPECT_EQ(blackhole::skyPhaseRadians(restClock, 1.0e6), 0.0);

  // Inside the ergoregion no observer is static.
  EXPECT_FALSE(blackhole::observerKeyFor(0.1, 0.5, ObserverKind::Static).has_value());
}

TEST(ObserverSkyView, SkyPhaseTurnsOncePerProperPeriod) {
  const blackhole::ObserverClockModel clock = blackhole::observerClockModel(canonMiller(), 1.0e8);
  const double period = clock.properPeriodSeconds;
  EXPECT_NEAR(blackhole::skyPhaseRadians(clock, 0.25 * period), 0.5 * K_PI, 1e-9);
  EXPECT_NEAR(blackhole::skyPhaseRadians(clock, 0.5 * period), K_PI, 1e-9);
  // A thousand turns later the double-precision phase is still exact to 1e-9.
  EXPECT_NEAR(blackhole::skyPhaseRadians(clock, 1000.25 * period), 0.5 * K_PI, 1e-9);
}

/** @brief One look direction's camera basis: orthonormal, forward on the
 *         look, up toward the spin axis, and the look projecting to the
 *         screen center while its antipode projects nowhere. */
void checkViewBasis(double longitudeDeg, double latitudeDeg) {
  const double longitude = longitudeDeg * K_PI / 180.0;
  const double latitude = latitudeDeg * K_PI / 180.0;
  const auto basis = blackhole::observerViewBasis(longitude, latitude);
  const sky::Vec3 forward = sky::lookDirection(longitude, latitude);
  const auto dot = [](const sky::Vec3 &a, const sky::Vec3 &b) {
    return (a.at(0) * b.at(0)) + (a.at(1) * b.at(1)) + (a.at(2) * b.at(2));
  };
  EXPECT_NEAR(dot(basis.at(2), forward), 1.0, 1e-15);
  EXPECT_NEAR(dot(basis.at(0), basis.at(1)), 0.0, 1e-15);
  EXPECT_NEAR(dot(basis.at(0), basis.at(0)), 1.0, 1e-15);
  EXPECT_NEAR(dot(basis.at(1), basis.at(1)), 1.0, 1e-15);
  EXPECT_LT(basis.at(1).at(1), 0.0) << "up leans toward the spin axis (-e_theta)";
  const auto center = blackhole::projectToPixel(basis, forward, 1.0, 1920, 1080);
  if (!center.has_value()) {
    GTEST_FAIL() << "the look direction projects off screen";
  }
  EXPECT_NEAR(center->at(0), 960.0, 1e-9);
  EXPECT_NEAR(center->at(1), 540.0, 1e-9);
  const sky::Vec3 behind{-forward.at(0), -forward.at(1), -forward.at(2)};
  EXPECT_FALSE(blackhole::projectToPixel(basis, behind, 1.0, 1920, 1080).has_value());
}

TEST(ObserverSkyView, ViewBasisIsRightHandedAndProjectsItsAxis) {
  checkViewBasis(0.0, 0.0);
  checkViewBasis(150.0, 0.0);
  checkViewBasis(-100.0, 40.0);
  checkViewBasis(30.0, -70.0);
}

/**
 * The table is the photopic luminance of a Planck spectrum. Its luminous
 * efficacy, luminance over radiance sigma T^4 / pi, is a textbook curve:
 * about 16 lm/W for CIE illuminant A's 2856 K, about 92 lm/W at the Sun's
 * 5772 K, peaking near 95 lm/W around 6500 K; D65's temperature renders
 * near-white; and on the Rayleigh-Jeans tail luminance grows as T.
 */
TEST(ObserverSkyView, BlackbodyTableHasPlanckEfficacyAndColor) {
  const auto table = blackhole::loadBlackbodyTable("assets/luts/blackbody_cie_lut.csv");
  if (!table.has_value()) {
    GTEST_FAIL() << "assets/luts/blackbody_cie_lut.csv did not load";
  }
  const auto efficacy = [&table](double temperature) {
    const double radiance = K_STEFAN_BOLTZMANN * std::pow(temperature, 4.0) / K_PI;
    return std::pow(10.0, table->at(std::log10(temperature)).at(3)) / radiance;
  };
  EXPECT_NEAR(efficacy(2856.0), 16.5, 1.0);
  EXPECT_NEAR(efficacy(5772.0), 92.0, 2.0);
  EXPECT_NEAR(efficacy(6504.0), 95.4, 2.0);
  const std::array<double, 4> d65 = table->at(std::log10(6504.0));
  EXPECT_NEAR(d65.at(0), 1.0, 0.06);
  EXPECT_NEAR(d65.at(1), 1.0, 0.06);
  EXPECT_NEAR(d65.at(2), 1.0, 0.06);
  const double slope = table->at(7.0).at(3) - table->at(6.0).at(3);
  EXPECT_NEAR(slope, 1.0, 0.01) << "log10 luminance per decade of T on the Rayleigh-Jeans tail";
}

} // namespace
