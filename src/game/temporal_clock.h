/**
 * @file temporal_clock.h
 * @brief Coordinate turn clock and per-fleet proper-time accumulation.
 *
 * The integer turn count is the only loop variable in the campaign. Coordinate
 * time is derived (turn * secondsPerTurn, one multiply, never accumulated) so
 * it cannot drift. Proper time accumulates per-turn in a fixed order, which
 * makes any batch advance bit-identical to the same advances issued one at a
 * time: advance(n) IS n iterated single-turn advances by construction.
 */

#ifndef BLACKHOLE_GAME_TEMPORAL_CLOCK_H
#define BLACKHOLE_GAME_TEMPORAL_CLOCK_H

#include <cstdint>

namespace game {

class TemporalClock {
public:
  explicit TemporalClock(double secondsPerTurn);

  /** @brief Advances one coordinate turn. */
  void advance();

  /** @brief Advances turnCount turns as iterated single-turn advances. */
  void advance(std::int64_t turnCount);

  [[nodiscard]] std::int64_t turn() const { return turn_; }
  [[nodiscard]] double secondsPerTurn() const { return secondsPerTurn_; }

  /** @brief Derived coordinate time: turn * secondsPerTurn. */
  [[nodiscard]] double coordinateTimeSec() const;

  /** @brief Smallest whole number of turns covering delaySec; never rounds a
   *         delivery earlier than its physical delay. */
  [[nodiscard]] std::int64_t ceilTurns(double delaySec) const;

private:
  std::int64_t turn_ = 0;
  double secondsPerTurn_;
};

/** @brief Proper time a stationary observer accrues over one coordinate turn:
 *         properTimeRate * secondsPerTurn. */
[[nodiscard]] double properDeltaSec(double properTimeRate, double secondsPerTurn);

} // namespace game

#endif // BLACKHOLE_GAME_TEMPORAL_CLOCK_H
