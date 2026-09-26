/**
 * @file tests/energy_conserving_geodesic_test.cpp
 * @brief Null and timelike norm projection in verified/energy_conserving_geodesic.hpp.
 *
 * The additive projection keeps v^t and v^phi and rescales v^r, v^theta so
 * that g(v, v) returns to its target. The reference state is a Schwarzschild
 * r = 10M equatorial photon (v^t = 1/f, v^phi = 0.03) whose v^r carries a 1e-6
 * relative drift; the exact null v^r is 0.96333.
 */

#include <cmath>
#include <numbers>

#include <gtest/gtest.h>

#include "physics/verified/energy_conserving_geodesic.hpp"

namespace {

struct SchwarzschildNullCase {
  verified::MetricComponents g;
  verified::StateVector drifted;
  double exactVr;
};

SchwarzschildNullCase driftedNullCase() {
  constexpr double r = 10.0;
  constexpr double f = 1.0 - (2.0 / r);
  const verified::MetricComponents g(-f, 1.0 / f, r * r, r * r, 0.0);
  constexpr double vt = 1.0 / f;
  constexpr double vph = 0.03;
  const double exactVr = std::sqrt(((f * vt * vt) - (r * r * vph * vph)) * f);
  const verified::StateVector drifted{0.0, r, std::numbers::pi / 2.0, 0.0,
                                      vt,  exactVr * (1.0 + 1.0e-6), 0.0, vph};
  return {g, drifted, exactVr};
}

/** @brief Multiplicative rescale of v^r, v^theta by sqrt(|target / norm|), zero for a null target. */
verified::StateVector multiplicativeRescale(const verified::MetricComponents &g,
                                            const verified::StateVector &s, double target) {
  const double factor = std::sqrt(std::abs(target / verified::computeMetricNorm(g, s)));
  return {s.x0, s.x1, s.x2, s.x3, s.v0, factor * s.v1, factor * s.v2, s.v3};
}

} // namespace

/** @brief The drifted photon keeps v^r = 0.963 and returns to |g(v, v)| < 1e-14. */
TEST(EnergyConservingGeodesic, NullProjectionKeepsRadialVelocity) {
  const SchwarzschildNullCase c = driftedNullCase();
  EXPECT_GT(std::abs(verified::computeMetricNorm(c.g, c.drifted)), 1.0e-6);

  const verified::StateVector corrected =
      verified::applyConstraintCorrection(c.g, c.drifted, 0.0);
  EXPECT_NEAR(corrected.v1, 0.963, 5.0e-4);
  EXPECT_NEAR(corrected.v1, c.exactVr, 1.0e-14);
  EXPECT_LT(std::abs(verified::computeMetricNorm(c.g, corrected)), 1.0e-14);
  // v^t and v^phi, hence E and L, are untouched.
  EXPECT_EQ(corrected.v0, c.drifted.v0);
  EXPECT_EQ(corrected.v3, c.drifted.v3);
  EXPECT_EQ(verified::computeEnergy(c.g, corrected), verified::computeEnergy(c.g, c.drifted));
}

/** @brief Negative control: the multiplicative rescale zeroes v^r and leaves norm -1.16. */
TEST(EnergyConservingGeodesic, MultiplicativeRescaleDestroysNullRay) {
  const SchwarzschildNullCase c = driftedNullCase();
  const verified::StateVector rescaled = multiplicativeRescale(c.g, c.drifted, 0.0);
  EXPECT_EQ(rescaled.v1, 0.0);
  EXPECT_NEAR(verified::computeMetricNorm(c.g, rescaled), -1.16, 0.01);
}

/** @brief Kerr frame dragging with v^r and v^theta: common alpha, both projections. */
TEST(EnergyConservingGeodesic, KerrProjectionScalesRadialAndPolarTogether) {
  constexpr double m = 1.0;
  constexpr double a = 0.9;
  constexpr double r = 6.0;
  constexpr double theta = 1.1;
  const verified::MetricComponents g(verified::kerrGTt(r, theta, m, a),
                                     verified::kerrGRr(r, theta, m, a),
                                     verified::kerrGThth(r, theta, a),
                                     verified::kerrGPhph(r, theta, m, a),
                                     verified::kerrGTph(r, theta, m, a));
  const double vt = 1.3;
  const double vph = 0.02;
  const double vth = 0.01;
  // Solve v^r for a null vector, then perturb both spatial components.
  const double rest = (g.gTt * vt * vt) + (2.0 * g.gTph * vt * vph) + (g.gPhph * vph * vph) +
                      (g.gThth * vth * vth);
  const double vr = std::sqrt(-rest / g.gRr);
  const verified::StateVector drifted{0.0, r, theta, 0.0, vt, vr * (1.0 + 3.0e-6),
                                      vth * (1.0 - 2.0e-6), vph};

  const verified::StateVector null = verified::applyConstraintCorrection(g, drifted, 0.0);
  EXPECT_LT(std::abs(verified::computeMetricNorm(g, null)), 1.0e-14);
  EXPECT_NEAR(null.v1 / null.v2, drifted.v1 / drifted.v2, 1.0e-12);
  EXPECT_EQ(null.v0, drifted.v0);
  EXPECT_EQ(null.v3, drifted.v3);
}

/** @brief Timelike target -1 is restored the same way. */
TEST(EnergyConservingGeodesic, TimelikeProjection) {
  const SchwarzschildNullCase c = driftedNullCase();
  // A timelike state: lower v^r until g(v, v) is near -0.5, then project to -1.
  verified::StateVector timelike = c.drifted;
  timelike.v1 = 0.5;
  timelike.v0 = 1.4;
  const double before = verified::computeMetricNorm(c.g, timelike);
  ASSERT_LT(before, 0.0);
  const verified::StateVector corrected = verified::applyConstraintCorrection(c.g, timelike, -1.0);
  EXPECT_NEAR(verified::computeMetricNorm(c.g, corrected), -1.0, 1.0e-14);
  EXPECT_EQ(corrected.v0, timelike.v0);
}

/**
 * @brief No r-theta motion: v^t is re-solved, taking the root nearest the drifted v^t.
 *
 * A circular photon at the Schwarzschild photon sphere has v^r = v^theta = 0,
 * so only v^t can absorb the drift.
 */
TEST(EnergyConservingGeodesic, FallbackResolvesTimeComponent) {
  constexpr double r = 3.0;
  constexpr double f = 1.0 - (2.0 / r);
  const verified::MetricComponents g(-f, 1.0 / f, r * r, r * r, 0.0);
  constexpr double vph = 0.1;
  const double vtExact = std::sqrt(r * r * vph * vph / f);
  const verified::StateVector drifted{0.0, r, std::numbers::pi / 2.0, 0.0, vtExact * (1.0 + 1.0e-5),
                                      0.0, 0.0, vph};
  const verified::StateVector corrected = verified::applyConstraintCorrection(g, drifted, 0.0);
  EXPECT_NEAR(corrected.v0, vtExact, 1.0e-14);
  EXPECT_GT(corrected.v0, 0.0);
  EXPECT_LT(std::abs(verified::computeMetricNorm(g, corrected)), 1.0e-14);
}
