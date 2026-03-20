/**
 * @file johannsen_psaltis_test.cpp
 * @brief Tests for Johannsen-Psaltis parametric deviation metric.
 */

#include <gtest/gtest.h>
#include "physics/johannsen_psaltis.h"
#include <cmath>

// --------------------------------------------------------------------------
// JP reduces to Kerr when all deviations vanish
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, ReducesToKerr) {
  double spins[] = {0.0, 0.5, 0.9, 0.99};
  double radii[] = {3.0, 6.0, 10.0, 50.0};

  for (double a : spins) {
    for (double r : radii) {
      EXPECT_TRUE(physics::jp_kerr_limit_check(r, M_PI / 3, 1.0, a))
          << "JP(alpha=0) != Kerr at r=" << r << " a=" << a;
    }
  }
}

// --------------------------------------------------------------------------
// A1 function: 1 + alpha_13 * (M/r)^3
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, A1Function) {
  // At r = M: A1 = 1 + alpha_13
  EXPECT_NEAR(physics::jp_A1(1.0, 1.0, 0.5), 1.5, 1e-14);
  EXPECT_NEAR(physics::jp_A1(1.0, 1.0, -0.5), 0.5, 1e-14);

  // At r = 2M: A1 = 1 + alpha_13/8
  EXPECT_NEAR(physics::jp_A1(2.0, 1.0, 1.0), 1.125, 1e-14);

  // Large r: A1 -> 1
  EXPECT_NEAR(physics::jp_A1(100.0, 1.0, 1.0), 1.0, 1e-5);
}

// --------------------------------------------------------------------------
// Non-zero deviation changes metric components
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, DeviationChangesMetric) {
  physics::JPParams params;
  params.alpha_13 = 0.5;

  auto jp = physics::jp_metric(6.0, M_PI / 2, 1.0, 0.9, params);

  physics::JPParams zero;
  auto kerr = physics::jp_metric(6.0, M_PI / 2, 1.0, 0.9, zero);

  // g_tt should differ
  EXPECT_NE(jp[0], kerr[0]);

  // g_thth should be the same (Sigma is unchanged)
  EXPECT_NEAR(jp[2], kerr[2], 1e-14);
}

// --------------------------------------------------------------------------
// Shadow shift is proportional to alpha_13
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, ShadowShiftLinear) {
  double shift1 = physics::jp_shadow_fractional_shift(1.0, 0.0, 0.1);
  double shift2 = physics::jp_shadow_fractional_shift(1.0, 0.0, 0.2);

  // Should be approximately 2x
  EXPECT_NEAR(shift2 / shift1, 2.0, 1e-10);
}

// --------------------------------------------------------------------------
// EHT bounds check
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, EHTBoundsCheck) {
  physics::JPParams in_bounds;
  in_bounds.alpha_13 = 1.0;
  EXPECT_TRUE(physics::jp_within_eht_bounds(in_bounds));

  physics::JPParams out_bounds;
  out_bounds.alpha_13 = 5.0;
  EXPECT_FALSE(physics::jp_within_eht_bounds(out_bounds));
}
