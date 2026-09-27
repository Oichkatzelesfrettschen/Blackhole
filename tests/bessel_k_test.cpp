#include <algorithm>
#include <array>
#include <cmath>

#include <gtest/gtest.h>

#include "../src/physics/bessel_k.h"
#include "../src/physics/safe_limits.h"

struct BesselKRow {
  double nu;
  double x;
  double scaledK;
  double scaledTail;
};

#include "bessel_k_reference.inc"

namespace {

// IEEE builds keep the kernel's compensated sum and stay within 1e-15 of the
// table. -ffast-math reassociates the compensation away, and the plain
// 128-term sum reaches 2.0e-15 under GCC 14 -O2, so fast-math builds get 4e-15.
#ifdef __FAST_MATH__
constexpr double TOLERANCE = 4.0e-15;
#else
constexpr double TOLERANCE = 1.0e-15;
#endif

double relativeError(double got, double expected) { return std::abs(got - expected) / expected; }

const BesselKRow *findRow(double nu, double x) {
  const auto *const found = std::ranges::find_if(
      BESSEL_K_ROWS, [nu, x](const BesselKRow &row) { return row.nu == nu && row.x == x; });
  return found == std::ranges::end(BESSEL_K_ROWS) ? nullptr : found;
}

} // namespace

TEST(BesselKTest, MatchesMpmathReference) {
  for (const BesselKRow &row : BESSEL_K_ROWS) {
    const physics::BesselKAndTailValues<double> values = physics::scaledBesselKAndTail(row.nu, row.x);
    EXPECT_LE(relativeError(values.scaledK, row.scaledK), TOLERANCE)
        << "nu=" << row.nu << ", x=" << row.x;
    EXPECT_LE(relativeError(values.scaledTail, row.scaledTail), TOLERANCE)
        << "nu=" << row.nu << ", x=" << row.x;
  }
}

// The shared passes truncate at the largest order they carry, so each order's
// value comes from a different integration range than the single-order call.
TEST(BesselKTest, SharedPassesMatchMpmathReference) {
  for (const BesselKRow &row : BESSEL_K_ROWS) {
    if (row.nu != 0.0) {
      continue;
    }
    const double x = row.x;
    const physics::BesselK012Values<double> thermal = physics::scaledBesselK012(x);
    const BesselKRow *k1 = findRow(1.0, x);
    const BesselKRow *k2 = findRow(2.0, x);
    const BesselKRow *twoThirds = findRow(2.0 / 3.0, x);
    const BesselKRow *fiveThirds = findRow(5.0 / 3.0, x);
    ASSERT_NE(k1, nullptr);
    ASSERT_NE(k2, nullptr);
    ASSERT_NE(twoThirds, nullptr);
    ASSERT_NE(fiveThirds, nullptr);
    EXPECT_LE(relativeError(thermal.scaledK0, row.scaledK), TOLERANCE) << "x=" << x;
    EXPECT_LE(relativeError(thermal.scaledK1, k1->scaledK), TOLERANCE) << "x=" << x;
    EXPECT_LE(relativeError(thermal.scaledK2, k2->scaledK), TOLERANCE) << "x=" << x;
    const physics::SynchrotronBesselValues<double> synchrotron =
        physics::scaledSynchrotronBessel(x);
    EXPECT_LE(relativeError(synchrotron.scaledKTwoThirds, twoThirds->scaledK), TOLERANCE)
        << "x=" << x;
    EXPECT_LE(relativeError(synchrotron.scaledTailFiveThirds, fiveThirds->scaledTail), TOLERANCE)
        << "x=" << x;
  }
}

TEST(BesselKTest, RemainsFiniteAndPositiveAtArgumentExtremes) {
  constexpr std::array<double, 2> arguments = {1.0e-10, 1.0e10};
  for (const double x : arguments) {
    const physics::BesselK012Values<double> thermalValues = physics::scaledBesselK012(x);
    const physics::SynchrotronBesselValues<double> synchrotronValues =
        physics::scaledSynchrotronBessel(x);
    EXPECT_TRUE(physics::safeIsfinite(thermalValues.scaledK0));
    EXPECT_TRUE(physics::safeIsfinite(thermalValues.scaledK1));
    EXPECT_TRUE(physics::safeIsfinite(thermalValues.scaledK2));
    EXPECT_TRUE(physics::safeIsfinite(synchrotronValues.scaledKTwoThirds));
    EXPECT_TRUE(physics::safeIsfinite(synchrotronValues.scaledTailFiveThirds));
    EXPECT_GT(thermalValues.scaledK0, 0.0);
    EXPECT_GT(thermalValues.scaledK1, 0.0);
    EXPECT_GT(thermalValues.scaledK2, 0.0);
    EXPECT_GT(synchrotronValues.scaledKTwoThirds, 0.0);
    EXPECT_GT(synchrotronValues.scaledTailFiveThirds, 0.0);
  }
}
