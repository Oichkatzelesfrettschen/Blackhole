#include <algorithm>
#include <array>
#include <cmath>
#include <iterator>
#include <string>

#include <gtest/gtest.h>

#include "../src/physics/bessel_k.h"
#include "../src/physics/safe_limits.h"

namespace {

struct BesselKRow {
  double nu;
  double x;
  double scaledK;
  double scaledTail;
};

#include "bessel_k_reference.inc"

// IEEE builds keep the kernel's compensated sum and stay within 1e-15 of the
// table. -ffast-math reassociates the compensation away, and the plain
// 128-term sum reaches 2.0e-15 under GCC 14 -O2, so fast-math builds get 4e-15.
#ifdef __FAST_MATH__
constexpr double TOLERANCE = 4.0e-15;
#else
constexpr double TOLERANCE = 1.0e-15;
#endif

const BesselKRow &rowAt(double nu, double x) {
  const auto *const found = std::ranges::find_if(
      BESSEL_K_ROWS, [nu, x](const BesselKRow &row) { return row.nu == nu && row.x == x; });
  EXPECT_NE(found, std::ranges::end(BESSEL_K_ROWS)) << "nu=" << nu << ", x=" << x;
  return *found;
}

void expectMatches(double got, double expected, const std::string &label, double x) {
  EXPECT_LE(std::abs(got - expected) / expected, TOLERANCE) << label << " at x=" << x;
}

void expectFinitePositive(double value, const std::string &label, double x) {
  EXPECT_TRUE(physics::safeIsfinite(value)) << label << " at x=" << x;
  EXPECT_GT(value, 0.0) << label << " at x=" << x;
}

} // namespace

TEST(BesselKTest, MatchesMpmathReference) {
  for (const BesselKRow &row : BESSEL_K_ROWS) {
    const physics::BesselKAndTailValues<double> values =
        physics::scaledBesselKAndTail(row.nu, row.x);
    const std::string order = "nu=" + std::to_string(row.nu);
    expectMatches(values.scaledK, row.scaledK, order + " e^x K", row.x);
    expectMatches(values.scaledTail, row.scaledTail, order + " e^x tail", row.x);
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
    expectMatches(thermal.scaledK0, row.scaledK, "K_0", x);
    expectMatches(thermal.scaledK1, rowAt(1.0, x).scaledK, "K_1", x);
    expectMatches(thermal.scaledK2, rowAt(2.0, x).scaledK, "K_2", x);
    const physics::SynchrotronBesselValues<double> synchrotron =
        physics::scaledSynchrotronBessel(x);
    expectMatches(synchrotron.scaledKTwoThirds, rowAt(2.0 / 3.0, x).scaledK, "K_2/3", x);
    expectMatches(synchrotron.scaledTailFiveThirds, rowAt(5.0 / 3.0, x).scaledTail,
                  "tail K_5/3", x);
  }
}

// 1e20 exceeds the 3.6e17 point past which 1 + 40/x rounds to 1; the
// truncation keeps a positive range there, and e^x K_nu -> sqrt(pi / (2x)).
TEST(BesselKTest, RemainsFiniteAndPositiveAtArgumentExtremes) {
  constexpr std::array<double, 3> arguments = {1.0e-10, 1.0e10, 1.0e20};
  for (const double x : arguments) {
    const physics::BesselK012Values<double> thermal = physics::scaledBesselK012(x);
    const physics::SynchrotronBesselValues<double> synchrotron =
        physics::scaledSynchrotronBessel(x);
    expectFinitePositive(thermal.scaledK0, "K_0", x);
    expectFinitePositive(thermal.scaledK1, "K_1", x);
    expectFinitePositive(thermal.scaledK2, "K_2", x);
    expectFinitePositive(synchrotron.scaledKTwoThirds, "K_2/3", x);
    expectFinitePositive(synchrotron.scaledTailFiveThirds, "tail K_5/3", x);
  }
  const double asymptote = std::sqrt(std::acos(-1.0) / 2.0e20);
  EXPECT_NEAR(physics::scaledBesselK(2.0, 1.0e20) / asymptote, 1.0, 1.0e-12);
}
