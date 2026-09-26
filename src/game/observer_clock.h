/**
 * @file observer_clock.h
 * @brief Exact fixed-point proper-time clock for a station on one worldline.
 *
 * A station's clock rate dtau/dt is quantized once, at placement, to
 * rateQ = llround(rate * 2^48). Every coordinate turn then adds exactly
 * rateQ * secondsPerTurn Q48 units: whole seconds into an int64, the rest
 * into a 48-bit fraction that carries into the seconds when it overflows. The
 * clock is pure integer arithmetic after quantization, so N single-turn
 * advances equal the closed form N * rateQ * secondsPerTurn bit for bit, on
 * every host and in any batching.
 *
 * Why Q48. Miller's orbit runs at dtau/dt = 1.6286e-5, which Q48 holds as
 * rateQ ~ 4.584e9 with a rounding error of at most 2^-49 absolute, 1.1e-10
 * relative. Q32 would hold it as ~69948 with a relative error up to 7.1e-6:
 * about half a local second lost or gained per local day.
 *
 * Error bound. |rateQ / 2^48 - rate| <= 2^-49, so after N turns the clock
 * differs from N * secondsPerTurn * rate by at most N * secondsPerTurn * 2^-49
 * seconds. The quantized rate is the clock's definition from then on; the
 * bound only compares it with the double it came from.
 *
 * Overflow. rate is in (0, 1], so rateQ <= 2^48; secondsPerTurn < 2^32, so
 * the per-turn increment rateQ * secondsPerTurn < 2^80 is formed as a 128-bit
 * product in 32-bit limbs (no compiler extension) and split once into a whole
 * part below 2^32 and a Q48 fraction. The int64 second counter wraps only
 * after 2^63 s, about 2.9e11 years of local time.
 *
 * The station's worldline is a game::Observer: the TimeField maps it to the
 * physics/kerr_observer.h rate (ZAMO lapse for Hovering, the Bardeen-Press-
 * Teukolsky clock for a circular orbit). The clock takes that rate, not the
 * observer, so it has no static-observer kind: no game station follows a
 * static worldline (a station holding a radius on thrust is a ZAMO, and no
 * static observer exists inside the ergosphere at all).
 */

#ifndef BLACKHOLE_GAME_OBSERVER_CLOCK_H
#define BLACKHOLE_GAME_OBSERVER_CLOCK_H

#include <cassert>
#include <cmath>
#include <cstdint>

#include "physics/safe_limits.h"
#include <limits>
#include <optional>

namespace game {

inline constexpr int K_CLOCK_FRACTION_BITS = 48;
inline constexpr std::uint64_t K_CLOCK_ONE = std::uint64_t{1} << K_CLOCK_FRACTION_BITS;
inline constexpr std::uint64_t K_CLOCK_FRACTION_MASK = K_CLOCK_ONE - 1U;
/// Largest turn length the clock accepts, in seconds (exclusive).
inline constexpr std::uint64_t K_CLOCK_MAX_SECONDS_PER_TURN = std::uint64_t{1} << 32;

/** @brief Unsigned 128-bit value as two 64-bit halves. */
struct WideProduct {
  std::uint64_t high = 0;
  std::uint64_t low = 0;
};

/** @brief Full 64 x 64 -> 128-bit product from 32-bit limbs. */
[[nodiscard]] constexpr WideProduct multiplyWide(std::uint64_t lhs, std::uint64_t rhs) {
  constexpr std::uint64_t mask32 = 0xFFFFFFFFULL;
  const std::uint64_t lhsLow = lhs & mask32;
  const std::uint64_t lhsHigh = lhs >> 32;
  const std::uint64_t rhsLow = rhs & mask32;
  const std::uint64_t rhsHigh = rhs >> 32;
  const std::uint64_t lowLow = lhsLow * rhsLow;
  const std::uint64_t lowHigh = lhsLow * rhsHigh;
  const std::uint64_t highLow = lhsHigh * rhsLow;
  const std::uint64_t highHigh = lhsHigh * rhsHigh;
  // Middle column: three terms each below 2^32 after splitting, so no overflow.
  const std::uint64_t middle = (lowLow >> 32) + (lowHigh & mask32) + (highLow & mask32);
  WideProduct product;
  product.low = (middle << 32) | (lowLow & mask32);
  product.high = highHigh + (lowHigh >> 32) + (highLow >> 32) + (middle >> 32);
  return product;
}

/** @brief rateQ = llround(rate * 2^48) for a rate in (0, 1]. ldexp is exact,
 *         so the only rounding is the final llround. A rate below 2^-49
 *         quantizes to 0, a stopped clock: callers building a station reject
 *         rateQ == 0 (CampaignState refuses the config). */
[[nodiscard]] inline std::uint64_t quantizeClockRate(double rate) {
  assert(physics::safeIsfinite(rate) && rate > 0.0 && rate <= 1.0);
  return static_cast<std::uint64_t>(std::llround(std::ldexp(rate, K_CLOCK_FRACTION_BITS)));
}

/** @brief True when a turn length is a whole number of seconds the clock can
 *         carry: integral, positive, and below 2^32. */
[[nodiscard]] inline bool isClockTurnLength(double secondsPerTurn) {
  return physics::safeIsfinite(secondsPerTurn) && secondsPerTurn >= 1.0 &&
         secondsPerTurn < static_cast<double>(K_CLOCK_MAX_SECONDS_PER_TURN) &&
         std::floor(secondsPerTurn) == secondsPerTurn;
}

/** @brief A clock value: whole local seconds plus a Q48 fraction of a second. */
struct ClockReading {
  std::int64_t properSec = 0;
  std::uint64_t fractionQ = 0; ///< In [0, 2^48).

  friend constexpr bool operator==(const ClockReading &, const ClockReading &) = default;
};

/** @brief Per-turn increment rateQ * secondsPerTurn split into whole seconds
 *         (below 2^32) and a Q48 fraction. */
struct ClockIncrement {
  std::uint64_t wholeSec = 0;
  std::uint64_t fractionQ = 0;
};

[[nodiscard]] constexpr ClockIncrement clockIncrement(std::uint64_t rateQ,
                                                      std::uint64_t secondsPerTurn) {
  const WideProduct product = multiplyWide(rateQ, secondsPerTurn);
  ClockIncrement increment;
  increment.wholeSec = (product.high << (64 - K_CLOCK_FRACTION_BITS)) |
                       (product.low >> K_CLOCK_FRACTION_BITS);
  increment.fractionQ = product.low & K_CLOCK_FRACTION_MASK;
  return increment;
}

/** @brief Closed form of `turns` single-turn advances from zero:
 *         divmod(turns * rateQ * secondsPerTurn, 2^48); nullopt when the
 *         whole seconds would not fit the int64 second counter. */
[[nodiscard]] constexpr std::optional<ClockReading>
clockReadingAfter(std::uint64_t rateQ, std::uint64_t secondsPerTurn, std::uint64_t turns) {
  const ClockIncrement increment = clockIncrement(rateQ, secondsPerTurn);
  // turns * increment = turns * wholeSec * 2^48 + turns * fractionQ; the second
  // term is up to 111 bits and carries its own whole seconds.
  const WideProduct fractionSum = multiplyWide(turns, increment.fractionQ);
  const std::uint64_t carrySec = (fractionSum.high << (64 - K_CLOCK_FRACTION_BITS)) |
                                 (fractionSum.low >> K_CLOCK_FRACTION_BITS);
  // The whole-second carry of turns * fractionQ is below 2^63 exactly when its
  // 128-bit product is below 2^111.
  if ((fractionSum.high >> (K_CLOCK_FRACTION_BITS - 1)) != 0) {
    return std::nullopt;
  }
  std::uint64_t wholeSec = 0;
  std::uint64_t totalSec = 0;
  if (__builtin_mul_overflow(turns, increment.wholeSec, &wholeSec) ||
      __builtin_add_overflow(wholeSec, carrySec, &totalSec) ||
      totalSec > static_cast<std::uint64_t>(std::numeric_limits<std::int64_t>::max())) {
    return std::nullopt;
  }
  ClockReading reading;
  reading.properSec = static_cast<std::int64_t>(totalSec);
  reading.fractionQ = fractionSum.low & K_CLOCK_FRACTION_MASK;
  return reading;
}

/**
 * @brief One station's local clock, advanced once per coordinate turn.
 *
 * Local ticks (the station's own schedule: a production shift, a local hour)
 * fire whenever the whole-second counter crosses a multiple of localTickSec;
 * advance() returns how many crossed this turn. A deep clock crosses one rarely
 * (Miller's 1.4 local seconds per one-day turn reach a local hour every 2558
 * turns); a shallow clock can cross several per turn.
 */
class ObserverClock {
public:
  ObserverClock() = default;

  /** @brief rateQ from quantizeClockRate; secondsPerTurn in [1, 2^32);
   *         localTickSec > 0. Starts at `start` (zero by default). */
  ObserverClock(std::uint64_t rateQ, std::uint64_t secondsPerTurn, std::int64_t localTickSec,
                ClockReading start = {})
      : rateQ_(rateQ), increment_(clockIncrement(rateQ, secondsPerTurn)),
        localTickSec_(localTickSec), reading_(start) {
    assert(rateQ > 0 && rateQ <= K_CLOCK_ONE);
    assert(secondsPerTurn >= 1 && secondsPerTurn < K_CLOCK_MAX_SECONDS_PER_TURN);
    assert(localTickSec > 0);
    assert(start.properSec >= 0 && start.fractionQ < K_CLOCK_ONE);
  }

  /** @brief Advances one coordinate turn; returns the local ticks crossed. */
  std::int64_t advance() {
    const std::int64_t ticksBefore = reading_.properSec / localTickSec_;
    std::uint64_t fraction = reading_.fractionQ + increment_.fractionQ;
    const std::uint64_t carry = fraction >> K_CLOCK_FRACTION_BITS;
    fraction &= K_CLOCK_FRACTION_MASK;
    reading_.properSec += static_cast<std::int64_t>(increment_.wholeSec + carry);
    reading_.fractionQ = fraction;
    return (reading_.properSec / localTickSec_) - ticksBefore;
  }

  [[nodiscard]] const ClockReading &reading() const { return reading_; }
  [[nodiscard]] std::int64_t properSec() const { return reading_.properSec; }
  [[nodiscard]] std::uint64_t fractionQ() const { return reading_.fractionQ; }
  [[nodiscard]] std::uint64_t rateQ() const { return rateQ_; }
  [[nodiscard]] std::int64_t localTickSec() const { return localTickSec_; }
  /** @brief Local ticks elapsed since zero. */
  [[nodiscard]] std::int64_t ticks() const { return reading_.properSec / localTickSec_; }
  /** @brief The quantized rate as a double, rateQ / 2^48. */
  [[nodiscard]] double rate() const {
    return std::ldexp(static_cast<double>(rateQ_), -K_CLOCK_FRACTION_BITS);
  }
  /** @brief Display value; the integer reading is the clock. */
  [[nodiscard]] double properSecApprox() const {
    return static_cast<double>(reading_.properSec) +
           std::ldexp(static_cast<double>(reading_.fractionQ), -K_CLOCK_FRACTION_BITS);
  }

private:
  std::uint64_t rateQ_ = K_CLOCK_ONE;
  ClockIncrement increment_{};
  std::int64_t localTickSec_ = 1;
  ClockReading reading_{};
};

} // namespace game

#endif // BLACKHOLE_GAME_OBSERVER_CLOCK_H
