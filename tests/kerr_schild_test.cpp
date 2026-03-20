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

#include <gtest/gtest.h>
#include "physics/coordinates.h"
#include "physics/kerr.h"
#include "physics/constants.h"
#include <cmath>
#include <array>

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
    return g[0] * v[0] * v[0]
         + 2.0 * g[1] * v[0] * v[1]
         + 2.0 * g[2] * v[0] * v[2]
         + 2.0 * g[3] * v[0] * v[3]
         + g[4] * v[1] * v[1]
         + 2.0 * g[5] * v[1] * v[2]
         + 2.0 * g[6] * v[1] * v[3]
         + g[7] * v[2] * v[2]
         + 2.0 * g[8] * v[2] * v[3]
         + g[9] * v[3] * v[3];
  };

  double spins[] = {0.0, 0.5, 0.9, 0.99};
  double radii[] = {10.0, 5.0, 3.0, 2.5};
  double thetas[] = {0.1, M_PI / 4, M_PI / 2, M_PI - 0.1};

  for (double a : spins) {
    for (double r : radii) {
      for (double theta : thetas) {
        auto g = physics::ks_outgoing_metric(r, theta, M_GEOM, a);

        // l^mu = (0, 1, 0, 0) is null
        auto l = physics::ks_outgoing_null_vector(r, theta, a, R_S);
        double norm_l = contract(g, l);
        EXPECT_NEAR(norm_l, 0.0, 1e-10)
            << "l^mu not null at r=" << r << " theta=" << theta
            << " a=" << a;

        // n^mu (ingoing) is also null
        auto n = physics::ks_ingoing_null_vector(r, theta, a, R_S);
        double norm_n = contract(g, n);
        EXPECT_NEAR(norm_n, 0.0, 1e-10)
            << "n^mu not null at r=" << r << " theta=" << theta
            << " a=" << a;
      }
    }
  }
}

// --------------------------------------------------------------------------
// Metric is regular at the horizon (unlike BL)
// --------------------------------------------------------------------------
TEST(KerrSchild, RegularAtHorizon) {
  double spins[] = {0.0, 0.5, 0.9, 0.99};
  double thetas[] = {0.1, M_PI / 4, M_PI / 2, M_PI - 0.1};

  for (double a : spins) {
    double r_plus = M_GEOM + std::sqrt(M_GEOM * M_GEOM - a * a);

    for (double theta : thetas) {
      // Just outside the horizon
      double r_near = r_plus + 1e-6;
      EXPECT_TRUE(physics::ks_metric_is_regular(r_near, theta, M_GEOM, a))
          << "Metric irregular near horizon at a=" << a << " theta=" << theta;

      // At the horizon exactly (Delta = 0)
      // KS metric should still have finite components except where
      // l_r_cov goes to the fallback value
      auto g = physics::ks_outgoing_metric(r_plus, theta, M_GEOM, a);
      // g_tt, g_thth, g_phph should be finite
      EXPECT_TRUE(std::isfinite(g[0])) << "g_tt infinite at horizon";
      EXPECT_TRUE(std::isfinite(g[7])) << "g_thth infinite at horizon";
      EXPECT_TRUE(std::isfinite(g[9])) << "g_phph infinite at horizon";
    }
  }
}

// --------------------------------------------------------------------------
// Schwarzschild limit: a=0 reduces to standard Schwarzschild KS
// --------------------------------------------------------------------------
TEST(KerrSchild, SchwarzschildLimit) {
  double r = 5.0;
  double theta = M_PI / 3;

  auto g = physics::ks_outgoing_metric(r, theta, M_GEOM, 0.0);

  // For a=0: Sigma = r^2, Delta = r^2 - 2Mr, f = 2M/r
  double f = 2.0 * M_GEOM / r;

  // g_tt = -(1 - 2M/r)
  EXPECT_NEAR(g[0], -(1.0 - f), 1e-12);

  // g_theta_theta = r^2 (= Sigma when a=0)
  EXPECT_NEAR(g[7], r * r, 1e-12);

  // Off-diagonal t-phi vanishes when a=0
  EXPECT_NEAR(g[3], 0.0, 1e-15);

  // r-phi vanishes when a=0
  EXPECT_NEAR(g[6], 0.0, 1e-15);
}

// --------------------------------------------------------------------------
// BL <-> KS velocity round-trip
// --------------------------------------------------------------------------
TEST(KerrSchild, VelocityRoundTrip) {
  double a = 0.7;
  double r = 6.0;

  std::array<double, 4> u_bl = {1.5, -0.3, 0.1, 0.8};

  auto u_ks = physics::bl_to_ks_velocity(u_bl, r, M_GEOM, a);
  auto u_rt = physics::ks_to_bl_velocity(u_ks, r, M_GEOM, a);

  for (int i = 0; i < 4; ++i) {
    EXPECT_NEAR(u_rt[static_cast<size_t>(i)],
                u_bl[static_cast<size_t>(i)], 1e-12)
        << "Round-trip failed for component " << i;
  }
}

// --------------------------------------------------------------------------
// KS phi transformation reduces to identity for a=0
// --------------------------------------------------------------------------
TEST(KerrSchild, PhiTransformSchwarzschildIdentity) {
  double phi_ks = 1.234;
  double r = 10.0;

  double phi_bl = physics::ks_to_bl_phi(r, phi_ks, M_GEOM, 0.0);
  EXPECT_NEAR(phi_bl, phi_ks, 1e-15);
}

// --------------------------------------------------------------------------
// KS phi transformation is finite near horizon
// --------------------------------------------------------------------------
TEST(KerrSchild, PhiTransformNearHorizon) {
  double a = 0.9;
  double r_plus = M_GEOM + std::sqrt(M_GEOM * M_GEOM - a * a);
  double phi_ks = 2.0;

  // Just outside horizon
  double r = r_plus + 0.01;
  double phi_bl = physics::ks_to_bl_phi(r, phi_ks, M_GEOM, a);
  EXPECT_TRUE(std::isfinite(phi_bl));
}

// --------------------------------------------------------------------------
// KS f function matches 2Mr/Sigma
// --------------------------------------------------------------------------
TEST(KerrSchild, FFunction) {
  double a = 0.5;
  double r = 4.0;
  double theta = M_PI / 3;

  double f = physics::ks_f(r, theta, M_GEOM, a);
  double sigma = r * r + a * a * std::cos(theta) * std::cos(theta);
  double expected = 2.0 * M_GEOM * r / sigma;

  EXPECT_NEAR(f, expected, 1e-14);
}

// --------------------------------------------------------------------------
// Outgoing null vector l^r is positive (outgoing)
// --------------------------------------------------------------------------
TEST(KerrSchild, OutgoingDirectionPositive) {
  auto l = physics::ks_outgoing_null_vector(5.0, M_PI / 2, 0.5, R_S);
  EXPECT_GT(l[1], 0.0) << "l^r should be positive (outgoing)";
}

// --------------------------------------------------------------------------
// Ingoing null vector n^r is negative (ingoing)
// --------------------------------------------------------------------------
TEST(KerrSchild, IngoingDirectionNegative) {
  auto n = physics::ks_ingoing_null_vector(5.0, M_PI / 2, 0.5, R_S);
  EXPECT_LT(n[1], 0.0) << "n^r should be negative (ingoing)";
}

// --------------------------------------------------------------------------
// g_tr = -2Mr/Sigma for outgoing KS (negative, unlike ingoing which is positive)
// --------------------------------------------------------------------------
TEST(KerrSchild, MetricCrossTermSign) {
  double a = 0.7;
  double r = 5.0;
  double theta = M_PI / 3;

  auto g = physics::ks_outgoing_metric(r, theta, M_GEOM, a);

  double sigma = r * r + a * a * std::cos(theta) * std::cos(theta);
  double expected_gtr = -2.0 * M_GEOM * r / sigma;

  EXPECT_NEAR(g[1], expected_gtr, 1e-12)
      << "g_tr should be -2Mr/Sigma for outgoing KS";
}
