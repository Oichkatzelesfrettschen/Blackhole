/**
 * @file blackhole_time_field_test.cpp
 * @brief Falsification gates for the Schwarzschild TimeField adapter: horizon
 *        rejection, analytic dilation, and the radial signal-delay closed form
 *        coded independently of the adapter's own path.
 */

#include <gtest/gtest.h>

#include <cmath>
#include <limits>

#include "constants.h"
#include "game/blackhole_time_field.h"
#include "game/observer.h"

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;

// Independent expectation: r_s = 2GM/c^2 from the physical constants, never
// from physics::schwarzschildRadius, so a regression there is caught here.
double expectedHorizonCm(double massG) {
  return 2.0 * physics::G * massG / physics::C2;
}

// Independent expectation for the one-way radial coordinate-time delay:
// delta_t = (r2 - r1)/c + (r_s/c) * ln((r2 - r_s)/(r1 - r_s)).
double expectedRadialDelaySec(double innerCm, double outerCm, double horizonCm) {
  return ((outerCm - innerCm) / physics::C) +
         ((horizonCm / physics::C) * std::log((outerCm - horizonCm) / (innerCm - horizonCm)));
}

} // namespace

TEST(BlackholeTimeField, HorizonAndInsideAreRejectedAsStationRadii) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  EXPECT_FALSE(field.isValidStationRadius(0.0));
  EXPECT_FALSE(field.isValidStationRadius(0.5 * horizonCm));
  EXPECT_FALSE(field.isValidStationRadius(horizonCm));
  EXPECT_FALSE(field.isValidStationRadius(-3.0 * horizonCm));
  EXPECT_FALSE(field.isValidStationRadius(std::numeric_limits<double>::quiet_NaN()));
  EXPECT_FALSE(field.isValidStationRadius(std::numeric_limits<double>::infinity()));
  EXPECT_TRUE(field.isValidStationRadius(1.001 * horizonCm));
}

TEST(BlackholeTimeField, HorizonRadiusMatchesTwoGMOverCSquared) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  EXPECT_NEAR(field.horizonRadiusCm(), expectedHorizonCm(K_M87_MASS_G),
              1e-6 * field.horizonRadiusCm());
}

TEST(BlackholeTimeField, ProperTimeRateMatchesAnalyticDilation) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = expectedHorizonCm(K_M87_MASS_G);
  for (const double multiple : {1.5, 3.0, 10.0, 100.0}) {
    const double radiusCm = multiple * horizonCm;
    const double expectedRate = std::sqrt(1.0 - (horizonCm / radiusCm));
    EXPECT_NEAR(field.properTimeRate(radiusCm, game::Observer::Hovering), expectedRate, 1e-12)
        << "radius multiple " << multiple;
  }
}

TEST(BlackholeTimeField, SignalDelayMatchesRadialClosedForm) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  const double innerCm = 3.0 * horizonCm;
  const double outerCm = 50.0 * horizonCm;
  const double expectedSec = expectedRadialDelaySec(innerCm, outerCm, horizonCm);
  EXPECT_NEAR(field.signalDelaySec(innerCm, outerCm), expectedSec, 1e-9 * expectedSec);
  // Direction cannot matter for a stationary exchange.
  EXPECT_DOUBLE_EQ(field.signalDelaySec(innerCm, outerCm), field.signalDelaySec(outerCm, innerCm));
  // Coinciding stations exchange with zero delay.
  EXPECT_DOUBLE_EQ(field.signalDelaySec(innerCm, innerCm), 0.0);
}

TEST(BlackholeTimeField, SignalDelayIsFinitePositiveAndMonotoneWithSeparation) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  const double innerCm = 3.0 * horizonCm;
  double previousDelaySec = 0.0;
  for (const double multiple : {4.0, 10.0, 50.0, 200.0, 1000.0}) {
    const double delaySec = field.signalDelaySec(innerCm, multiple * horizonCm);
    EXPECT_TRUE(std::isfinite(delaySec));
    EXPECT_GT(delaySec, 0.0);
    EXPECT_GT(delaySec, previousDelaySec) << "delay must grow with separation";
    previousDelaySec = delaySec;
  }
}

TEST(BlackholeTimeField, SignalDelayDivergesTowardTheHorizon) {
  // The ln term grows without bound as the inner station approaches r_s: this
  // is the stale-telemetry pressure the campaign is built on.
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  const double outerCm = 100.0 * horizonCm;
  double previousDelaySec = 0.0;
  for (const double epsilon : {1e-1, 1e-3, 1e-6, 1e-9}) {
    const double innerCm = (1.0 + epsilon) * horizonCm;
    const double delaySec = field.signalDelaySec(innerCm, outerCm);
    EXPECT_TRUE(std::isfinite(delaySec));
    EXPECT_GT(delaySec, previousDelaySec) << "epsilon " << epsilon;
    previousDelaySec = delaySec;
  }
  // Unbounded growth is logarithmic in epsilon: each decade closer to the
  // horizon adds (r_s/c) * ln(10) of Shapiro excess over the flat flight
  // time. Eight decades (1e-1 -> 1e-9) must add more than 8 * (r_s/c).
  const double excessAtWideGapSec = field.signalDelaySec((1.0 + 1e-1) * horizonCm, outerCm) -
                                    ((outerCm - ((1.0 + 1e-1) * horizonCm)) / physics::C);
  const double excessNearHorizonSec =
      previousDelaySec - ((outerCm - ((1.0 + 1e-9) * horizonCm)) / physics::C);
  EXPECT_GT(excessNearHorizonSec - excessAtWideGapSec, 8.0 * horizonCm / physics::C);
}

// Falsifier: a circular orbit admitted at or inside 4M = 2 r_s (no bound
// orbit there), a hovering station refused outside the horizon, or an orbital
// clock other than sqrt(1 - 3M/r) (1/sqrt(2) at the 6M ISCO).
TEST(BlackholeTimeField, OrbitsNeedTheMarginallyBoundRadius) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  const double massCm = 0.5 * horizonCm;
  for (const game::Observer orbit :
       {game::Observer::CircularOrbitPrograde, game::Observer::CircularOrbitRetrograde}) {
    EXPECT_FALSE(field.admitsObserver(3.9 * massCm, orbit));
    EXPECT_FALSE(field.admitsObserver(4.0 * massCm, orbit));
    EXPECT_TRUE(field.admitsObserver(4.1 * massCm, orbit));
    EXPECT_NEAR(field.properTimeRate(6.0 * massCm, orbit), std::sqrt(0.5), 1e-12);
  }
  EXPECT_TRUE(field.admitsObserver(3.9 * massCm, game::Observer::Hovering));
  EXPECT_FALSE(field.admitsObserver(0.99 * horizonCm, game::Observer::Hovering));
  EXPECT_NEAR(field.properTimeRate(6.0 * massCm, game::Observer::Hovering), std::sqrt(2.0 / 3.0),
              1e-12);
}

// Falsifier: a Schwarzschild orbit between 4M and the 6M ISCO reported
// stable, or one at or outside 6M reported unstable.
TEST(BlackholeTimeField, StableOrbitsStartAtSixM) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double massCm = 0.5 * field.horizonRadiusCm();
  const game::Observer orbit = game::Observer::CircularOrbitPrograde;
  EXPECT_DOUBLE_EQ(field.iscoRadiusCm(orbit), 6.0 * massCm);
  EXPECT_FALSE(field.admitsStableOrbit(5.0 * massCm, orbit));
  EXPECT_TRUE(field.admitsObserver(5.0 * massCm, orbit));
  EXPECT_TRUE(field.admitsStableOrbit(6.0 * massCm, orbit));
  EXPECT_TRUE(field.admitsStableOrbit(20.0 * massCm, orbit));
  EXPECT_FALSE(field.admitsStableOrbit(20.0 * massCm, game::Observer::Hovering));
}
