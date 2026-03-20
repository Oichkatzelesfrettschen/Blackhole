/**
 * @file kerr_schild_test.cpp
 * @brief Tests for outgoing Kerr-Schild coordinate transformations.
 *
 * Validates:
 * - Null vector normalization (l^mu l_mu = 0)
 * - Metric regularity at the horizon (no BL singularity)
 * - BL <-> KS velocity round-trip
 * - Schwarzschild limit (a=0)
 * - KS metric determinant
 */

#include <array>
#include <cmath>
#include <cstddef>

#include <gtest/gtest.h>

#include "physics/constants.h"
#include "physics/coordinates.h"

namespace {

// Geometric units: M = 1 for simplicity
constexpr double M_GEOM = 1.0;
constexpr double R_S = 2.0 * M_GEOM;

} // namespace

// --------------------------------------------------------------------------
// Outgoing null vector is indeed null: g_mu_nu l^mu l^nu = 0
// --------------------------------------------------------------------------
TEST(KerrSchild, NullVectorIsNull) {
  // Helper to compute g_mu_nu v^mu v^nu
  auto contract = [](const std::array<double, 10>& g,
                     const std::array<double, 4>& v) {
    // g = [g_tt, g_tr, g_tth, g_tph, g_rr, g_rth, g_rph,
    //      g_thth, g_thph, g_phph]
    return (g.at(0) * v.at(0) * v.at(0)) + (2.0 * g.at(1) * v.at(0) * v.at(1)) + (2.0 * g.at(2) * v.at(0) * v.at(2)) +
           (2.0 * g.at(3) * v.at(0) * v.at(3)) + (g.at(4) * v.at(1) * v.at(1)) + (2.0 * g.at(5) * v.at(1) * v.at(2)) +
           (2.0 * g.at(6) * v.at(1) * v.at(3)) + (g.at(7) * v.at(2) * v.at(2)) + (2.0 * g.at(8) * v.at(2) * v.at(3)) +
           (g.at(9) * v.at(3) * v.at(3));
  };

  double const spins[] = {0.0, 0.5, 0.9, 0.99};
  double const radii[] = {10.0, 5.0, 3.0, 2.5};
  double const thetas[] = {0.1, physics::PI / 4, physics::PI / 2, physics::PI - 0.1};

  for (double const a : spins) {
    for (double const r : radii) {
      for (double const theta : thetas) {
        auto g = physics::ksOutgoingMetric(r, theta, M_GEOM, a);

        // l^mu = (0, 1, 0, 0) is null
        auto l = physics::ksOutgoingNullVector(r, theta, a, R_S);
        double const normL = contract(g, l);
        EXPECT_NEAR(normL, 0.0, 1e-10)
            << "l^mu not null at r=" << r << " theta=" << theta << " a=" << a;

        // n^mu (ingoing) is also null
        auto n = physics::ksIngoingNullVector(r, theta, a, R_S);
        double const normN = contract(g, n);
        EXPECT_NEAR(normN, 0.0, 1e-10)
            << "n^mu not null at r=" << r << " theta=" << theta << " a=" << a;
      }
    }
  }
}

// --------------------------------------------------------------------------
// Metric is regular at the horizon (unlike BL)
// --------------------------------------------------------------------------
TEST(KerrSchild, RegularAtHorizon) {
  double const spins[] = {0.0, 0.5, 0.9, 0.99};
  double const thetas[] = {0.1, physics::PI / 4, physics::PI / 2, physics::PI - 0.1};

  for (double const a : spins) {
    double const rPlus = M_GEOM + std::sqrt((M_GEOM * M_GEOM) - (a * a));

    for (double const theta : thetas) {
      // Just outside the horizon
      double const rNear = rPlus + 1e-6;
      EXPECT_TRUE(physics::ksMetricIsRegular(rNear, theta, M_GEOM, a))
          << "Metric irregular near horizon at a=" << a << " theta=" << theta;

      // At the horizon exactly (Delta = 0)
      // KS metric should still have finite components except where
      // l_r_cov goes to the fallback value
      auto g = physics::ksOutgoingMetric(rPlus, theta, M_GEOM, a);
      // g_tt, g_thth, g_phph should be finite
      EXPECT_TRUE(std::isfinite(g.at(0))) << "g_tt infinite at horizon";
      EXPECT_TRUE(std::isfinite(g.at(7))) << "g_thth infinite at horizon";
      EXPECT_TRUE(std::isfinite(g.at(9))) << "g_phph infinite at horizon";
    }
  }
}

// --------------------------------------------------------------------------
// Schwarzschild limit: a=0 reduces to standard Schwarzschild KS
// --------------------------------------------------------------------------
TEST(KerrSchild, SchwarzschildLimit) {
  double const r = 5.0;
  double const theta = physics::PI / 3;

  auto g = physics::ksOutgoingMetric(r, theta, M_GEOM, 0.0);

  // For a=0: Sigma = r^2, Delta = r^2 - 2Mr, f = 2M/r
  double const f = 2.0 * M_GEOM / r;

  // g_tt = -(1 - 2M/r)
  EXPECT_NEAR(g.at(0), -(1.0 - f), 1e-12);

  // g_theta_theta = r^2 (= Sigma when a=0)
  EXPECT_NEAR(g.at(7), r * r, 1e-12);

  // Off-diagonal t-phi vanishes when a=0
  EXPECT_NEAR(g.at(3), 0.0, 1e-15);

  // r-phi vanishes when a=0
  EXPECT_NEAR(g.at(6), 0.0, 1e-15);
}

// --------------------------------------------------------------------------
// BL <-> KS velocity round-trip
// --------------------------------------------------------------------------
TEST(KerrSchild, VelocityRoundTrip) {
  double const a = 0.7;
  double const r = 6.0;

  std::array<double, 4> uBl = {1.5, -0.3, 0.1, 0.8};

  auto uKs = physics::blToKsVelocity(uBl, r, M_GEOM, a);
  auto uRt = physics::ksToBlVelocity(uKs, r, M_GEOM, a);

  for (int i = 0; i < 4; ++i) {
    EXPECT_NEAR(uRt.at(static_cast<size_t>(i)), uBl.at(static_cast<size_t>(i)), 1e-12)
        << "Round-trip failed for component " << i;
  }
}

// --------------------------------------------------------------------------
// KS phi transformation reduces to identity for a=0
// --------------------------------------------------------------------------
TEST(KerrSchild, PhiTransformSchwarzschildIdentity) {
  double const phiKs = 1.234;
  double const r = 10.0;

  double const phiBl = physics::ksToBlPhi(r, phiKs, M_GEOM, 0.0);
  EXPECT_NEAR(phiBl, phiKs, 1e-15);
}

// --------------------------------------------------------------------------
// KS phi transformation is finite near horizon
// --------------------------------------------------------------------------
TEST(KerrSchild, PhiTransformNearHorizon) {
  double const a = 0.9;
  double const rPlus = M_GEOM + std::sqrt((M_GEOM * M_GEOM) - (a * a));
  double const phiKs = 2.0;

  // Just outside horizon
  double const r = rPlus + 0.01;
  double const phiBl = physics::ksToBlPhi(r, phiKs, M_GEOM, a);
  EXPECT_TRUE(std::isfinite(phiBl));
}

// --------------------------------------------------------------------------
// KS f function matches 2Mr/Sigma
// --------------------------------------------------------------------------
TEST(KerrSchild, FFunction) {
  double const a = 0.5;
  double const r = 4.0;
  double const theta = physics::PI / 3;

  double const f = physics::ksF(r, theta, M_GEOM, a);
  double const sigma = (r * r) + (a * a * std::cos(theta) * std::cos(theta));
  double const expected = 2.0 * M_GEOM * r / sigma;

  EXPECT_NEAR(f, expected, 1e-14);
}

// --------------------------------------------------------------------------
// Outgoing null vector l^r is positive (outgoing)
// --------------------------------------------------------------------------
TEST(KerrSchild, OutgoingDirectionPositive) {
  auto l = physics::ksOutgoingNullVector(5.0, physics::PI / 2, 0.5, R_S);
  EXPECT_GT(l.at(1), 0.0) << "l^r should be positive (outgoing)";
}

// --------------------------------------------------------------------------
// Ingoing null vector n^r is negative (ingoing)
// --------------------------------------------------------------------------
TEST(KerrSchild, IngoingDirectionNegative) {
  auto n = physics::ksIngoingNullVector(5.0, physics::PI / 2, 0.5, R_S);
  EXPECT_LT(n.at(1), 0.0) << "n^r should be negative (ingoing)";
}

// --------------------------------------------------------------------------
// g_tr = -2Mr/Sigma for outgoing KS (negative, unlike ingoing which is positive)
// --------------------------------------------------------------------------
TEST(KerrSchild, MetricCrossTermSign) {
  double const a = 0.7;
  double const r = 5.0;
  double const theta = physics::PI / 3;

  auto g = physics::ksOutgoingMetric(r, theta, M_GEOM, a);

  double const sigma = (r * r) + (a * a * std::cos(theta) * std::cos(theta));
  double const expectedGtr = -2.0 * M_GEOM * r / sigma;

  EXPECT_NEAR(g.at(1), expectedGtr, 1e-12) << "g_tr should be -2Mr/Sigma for outgoing KS";
}
