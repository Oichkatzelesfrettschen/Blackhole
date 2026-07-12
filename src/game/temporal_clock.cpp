/**
 * @file temporal_clock.cpp
 * @brief Coordinate turn clock implementation.
 */

#include "game/temporal_clock.h"

#include <cassert>
#include <cmath>
#include <cstdint>

namespace game {

TemporalClock::TemporalClock(double secondsPerTurn) : secondsPerTurn_(secondsPerTurn) {
  assert(std::isfinite(secondsPerTurn) && secondsPerTurn > 0.0);
}

void TemporalClock::advance() { ++turn_; }

void TemporalClock::advance(std::int64_t turnCount) {
  assert(turnCount >= 0);
  for (std::int64_t step = 0; step < turnCount; ++step) {
    advance();
  }
}

double TemporalClock::coordinateTimeSec() const {
  return static_cast<double>(turn_) * secondsPerTurn_;
}

std::int64_t TemporalClock::ceilTurns(double delaySec) const {
  assert(std::isfinite(delaySec) && delaySec >= 0.0);
  return static_cast<std::int64_t>(std::ceil(delaySec / secondsPerTurn_));
}

double properDeltaSec(double properTimeRate, double secondsPerTurn) {
  return properTimeRate * secondsPerTurn;
}

} // namespace game
