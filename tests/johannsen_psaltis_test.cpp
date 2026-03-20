/**
 * @file johannsen_psaltis_test.cpp
 * @brief Tests for Johannsen-Psaltis parametric deviation metric.
 */

#include <gtest/gtest.h>
#include "physics/johannsen_psaltis.h"
#include <numbers>

// --------------------------------------------------------------------------
// JP reduces to Kerr when all deviations vanish
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, ReducesToKerr) {
  const double spins[] = {0.0, 0.5, 0.9, 0.99};
  const double radii[] = {3.0, 6.0, 10.0, 50.0};

  for (const double a : spins) {
    for (const double r : radii) {
      EXPECT_TRUE(physics::jpKerrLimitCheck(r, std::numbers::pi / 3, 1.0, a))
          << "JP(alpha=0) != Kerr at r=" << r << " a=" << a;
    }
  }
}

// --------------------------------------------------------------------------
// A1 function: 1 + alpha_13 * (M/r)^3
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, A1Function) {
  // At r = M: A1 = 1 + alpha_13
  EXPECT_NEAR(physics::jpA1(1.0, 1.0, 0.5), 1.5, 1e-14);
  EXPECT_NEAR(physics::jpA1(1.0, 1.0, -0.5), 0.5, 1e-14);

  // At r = 2M: A1 = 1 + alpha_13/8
  EXPECT_NEAR(physics::jpA1(2.0, 1.0, 1.0), 1.125, 1e-14);

  // Large r: A1 -> 1
  EXPECT_NEAR(physics::jpA1(100.0, 1.0, 1.0), 1.0, 1e-5);
}

// --------------------------------------------------------------------------
// Non-zero deviation changes metric components
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, DeviationChangesMetric) {
  physics::JPParams params;
  params.alpha13 = 0.5;

  const auto jp = physics::jpMetric(6.0, std::numbers::pi / 2, 1.0, 0.9, params);

  const physics::JPParams zero;
  const auto kerr = physics::jpMetric(6.0, std::numbers::pi / 2, 1.0, 0.9, zero);

  // g_tt should differ
  EXPECT_NE(jp.at(0), kerr.at(0));

  // g_thth should be the same (Sigma is unchanged)
  EXPECT_NEAR(jp.at(2), kerr.at(2), 1e-14);
}

// --------------------------------------------------------------------------
// Shadow shift is proportional to alpha_13
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, ShadowShiftLinear) {
  const double shift1 = physics::jpShadowFractionalShift(1.0, 0.0, 0.1);
  const double shift2 = physics::jpShadowFractionalShift(1.0, 0.0, 0.2);

  // Should be approximately 2x
  EXPECT_NEAR(shift2 / shift1, 2.0, 1e-10);
}

// --------------------------------------------------------------------------
// EHT bounds check
// --------------------------------------------------------------------------
TEST(JohannsenPsaltis, EHTBoundsCheck) {
  physics::JPParams inBounds;
  inBounds.alpha13 = 1.0;
  EXPECT_TRUE(physics::jpWithinEhtBounds(inBounds));

  physics::JPParams outBounds;
  outBounds.alpha13 = 5.0;
  EXPECT_FALSE(physics::jpWithinEhtBounds(outBounds));
}
