/**
 * @file colony_clock_test.cpp
 * @brief Falsification gates for the Q48 fixed-point station clock: exact
 *        closed form, the rate-quantization error bound, carry across a
 *        billion turns, and local tick crossings.
 */

#include <gtest/gtest.h>

#include <cmath>
#include <cstdint>

#include "game/kerr_time_field.h"
#include "game/observer.h"
#include "game/observer_clock.h"

namespace {

__extension__ using Reference128 = unsigned __int128; // test-only cross-check

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_GARGANTUA_MASS_G = 1.0e8 * K_SOLAR_MASS_G;
constexpr double K_GARGANTUA_SPIN_DEFICIT = 1.33e-14;
constexpr std::uint64_t K_DAY_SEC = 86400;

double millerRate() {
  const game::KerrTimeField field(K_GARGANTUA_MASS_G,
                                  game::SpinDeficit{.epsilon = K_GARGANTUA_SPIN_DEFICIT});
  const double iscoCm = field.iscoRadiusCm(game::Observer::CircularOrbitPrograde);
  return field.properTimeRate(iscoCm, game::Observer::CircularOrbitPrograde);
}

// A reading minus a double, in seconds. The whole seconds and the double lie
// within a factor of two of each other, so their difference is exact
// (Sterbenz); the Q48 fraction is exact in a double and adds to that small
// difference with one rounding far below the bounds tested here.
double readingMinus(const game::ClockReading &reading, double valueSec) {
  const auto whole = static_cast<double>(reading.properSec);
  return (whole - valueSec) +
         std::ldexp(static_cast<double>(reading.fractionQ), -game::K_CLOCK_FRACTION_BITS);
}

} // namespace

// Falsifier: any 64 x 64 product whose limb decomposition disagrees with the
// compiler's 128-bit arithmetic.
TEST(ColonyClock, WideMultiplyMatchesReference) {
  const game::WideProduct extreme = game::multiplyWide(~0ULL, ~0ULL);
  EXPECT_EQ(extreme.high, ~0ULL - 1U);
  EXPECT_EQ(extreme.low, 1U);
  std::uint64_t state = 0x9E3779B97F4A7C15ULL;
  for (int sample = 0; sample < 10000; ++sample) {
    state = (state * 6364136223846793005ULL) + 1442695040888963407ULL;
    const std::uint64_t lhs = state;
    state = (state * 6364136223846793005ULL) + 1442695040888963407ULL;
    const std::uint64_t rhs = state >> (sample % 64);
    const Reference128 reference = static_cast<Reference128>(lhs) * rhs;
    const game::WideProduct product = game::multiplyWide(lhs, rhs);
    ASSERT_EQ(product.high, static_cast<std::uint64_t>(reference >> 64));
    ASSERT_EQ(product.low, static_cast<std::uint64_t>(reference));
  }
}

// Falsifier: Miller's rate quantizing to anything but ~4.584e9, or the
// quantized rate off the double by more than half a Q48 unit.
TEST(ColonyClock, MillerRateQuantizesWithinHalfUnit) {
  const double rate = millerRate();
  EXPECT_NEAR(rate, 1.6286e-5, 1e-8);
  const std::uint64_t rateQ = game::quantizeClockRate(rate);
  EXPECT_NEAR(static_cast<double>(rateQ), 4.584e9, 1e6);
  // rateQ / 2^48 is exact and within a factor of two of rate, so the
  // subtraction is exact (Sterbenz): this is the true quantization error.
  const double quantized = std::ldexp(static_cast<double>(rateQ), -game::K_CLOCK_FRACTION_BITS);
  EXPECT_LE(std::fabs(quantized - rate), std::ldexp(1.0, -49));
  // The Q32 alternative carries a relative error above 1e-6 at this rate.
  const double q32 = std::round(std::ldexp(rate, 32));
  EXPECT_GT(std::fabs(std::ldexp(q32, -32) - rate) / rate, 1e-6);
  EXPECT_LT(std::fabs(quantized - rate) / rate, 2e-10);
}

// Falsifier: N single-turn advances differing in any bit from the closed form
// N * rateQ * secondsPerTurn, for a deep clock, a near-unit clock (whose
// per-turn increment exceeds 2^64 Q48 units), and the unit clock.
TEST(ColonyClock, SteppedClockEqualsClosedFormExactly) {
  for (const double rate : {millerRate(), 0.985, 1.0}) {
    const std::uint64_t rateQ = game::quantizeClockRate(rate);
    game::ObserverClock clock(rateQ, K_DAY_SEC, 3600);
    constexpr std::uint64_t turns = 200000;
    for (std::uint64_t turn = 1; turn <= turns; ++turn) {
      clock.advance();
      if (turn % 997 == 0 || turn == turns) {
        ASSERT_EQ(clock.reading(), game::clockReadingAfter(rateQ, K_DAY_SEC, turn))
            << "rate " << rate << " turn " << turn;
      }
    }
  }
}

// Falsifier: the clock straying from N * spt * rate (the unquantized double
// form) by more than N * spt * 2^-49 plus the double form's own rounding.
TEST(ColonyClock, ErrorAgainstDoubleFormWithinQuantizationBound) {
  const double rate = millerRate();
  const std::uint64_t rateQ = game::quantizeClockRate(rate);
  for (const std::uint64_t turns : {1ULL, 1000ULL, 1000000ULL, 1000000000ULL}) {
    const game::ClockReading reading = game::clockReadingAfter(rateQ, K_DAY_SEC, turns);
    const double exactDouble = static_cast<double>(turns) * static_cast<double>(K_DAY_SEC) * rate;
    const double bound = static_cast<double>(turns) * static_cast<double>(K_DAY_SEC) *
                         std::ldexp(1.0, -49);
    // Two roundings in the double product, each at most half an ulp.
    const double productSlack = 2.0 * std::ldexp(std::fabs(exactDouble), -52);
    EXPECT_LE(std::fabs(readingMinus(reading, exactDouble)), bound + productSlack)
        << "turns " << turns;
  }
}

// Falsifier: a clock resumed at the billion-turn closed form drifting from the
// closed form a few thousand turns later, or closed forms failing to compose
// (the fraction carry lost or double-counted at a turn count where
// turns * fractionQ exceeds 2^64).
TEST(ColonyClock, CarryHoldsAcrossBillionTurns) {
  for (const double rate : {millerRate(), 0.985}) {
    const std::uint64_t rateQ = game::quantizeClockRate(rate);
    constexpr std::uint64_t base = 1000000000ULL;
    const game::ClockReading atBase = game::clockReadingAfter(rateQ, K_DAY_SEC, base);
    game::ObserverClock clock(rateQ, K_DAY_SEC, 3600, atBase);
    for (std::uint64_t step = 1; step <= 5000; ++step) {
      clock.advance();
    }
    EXPECT_EQ(clock.reading(), game::clockReadingAfter(rateQ, K_DAY_SEC, base + 5000));

    constexpr std::uint64_t extra = 700000013ULL;
    const game::ClockReading tail = game::clockReadingAfter(rateQ, K_DAY_SEC, extra);
    const std::uint64_t fraction = atBase.fractionQ + tail.fractionQ;
    game::ClockReading composed;
    composed.properSec = atBase.properSec + tail.properSec +
                         static_cast<std::int64_t>(fraction >> game::K_CLOCK_FRACTION_BITS);
    composed.fractionQ = fraction & game::K_CLOCK_FRACTION_MASK;
    EXPECT_EQ(composed, game::clockReadingAfter(rateQ, K_DAY_SEC, base + extra));
  }
}

// Falsifier: local ticks firing anywhere but on crossings of localTickSec, or
// the per-turn tick counts failing to sum to the reading's tick count.
TEST(ColonyClock, LocalTicksFireOnCrossings) {
  const std::uint64_t rateQ = game::quantizeClockRate(millerRate());
  game::ObserverClock clock(rateQ, K_DAY_SEC, 3600);
  std::int64_t fired = 0;
  std::uint64_t firstTickTurn = 0;
  for (std::uint64_t turn = 1; turn <= 20000; ++turn) {
    const std::int64_t crossed = clock.advance();
    EXPECT_LE(crossed, 1); // 1.4 local seconds per turn never crosses two hours.
    if (crossed > 0 && firstTickTurn == 0) {
      firstTickTurn = turn;
    }
    fired += crossed;
  }
  EXPECT_EQ(fired, clock.ticks());
  EXPECT_EQ(clock.ticks(), clock.properSec() / 3600);
  // The first local hour on Miller's orbit takes 3600 / 1.4071 = 2558.5 turns.
  EXPECT_EQ(game::clockReadingAfter(rateQ, K_DAY_SEC, firstTickTurn - 1).properSec / 3600, 0);
  EXPECT_EQ(game::clockReadingAfter(rateQ, K_DAY_SEC, firstTickTurn).properSec / 3600, 1);
  EXPECT_NEAR(static_cast<double>(firstTickTurn), 2559.0, 1.0);

  // A shallow clock with short ticks crosses several per turn.
  game::ObserverClock shallow(game::quantizeClockRate(0.985), K_DAY_SEC, 3600);
  EXPECT_EQ(shallow.advance(), 23);
}

TEST(ColonyClock, TurnLengthMustBeWholeSecondsBelowTwoToThe32) {
  EXPECT_TRUE(game::isClockTurnLength(86400.0));
  EXPECT_TRUE(game::isClockTurnLength(1.0));
  EXPECT_FALSE(game::isClockTurnLength(86400.5));
  EXPECT_FALSE(game::isClockTurnLength(0.0));
  EXPECT_FALSE(game::isClockTurnLength(std::ldexp(1.0, 32)));
  EXPECT_FALSE(game::isClockTurnLength(std::nan("")));
}
