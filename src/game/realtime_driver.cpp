/**
 * @file realtime_driver.cpp
 * @brief Wall-time to campaign-turn driver.
 */

#include "game/realtime_driver.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <utility>

namespace game {

RealtimeDriver::RealtimeDriver(RealtimeDriverConfig config) : config_(std::move(config)) {
  assert(std::isfinite(config_.secondsPerTurn) && config_.secondsPerTurn > 0.0);
  assert(std::isfinite(config_.localSecondsPerWallSecond) &&
         config_.localSecondsPerWallSecond > 0.0);
  assert(config_.maxTurnsPerFrame > 0 && config_.maxBacklogFrames > 0);
}

void RealtimeDriver::setFocusRate(double properTimeRate) {
  assert(std::isfinite(properTimeRate) && properTimeRate > 0.0 && properTimeRate <= 1.0);
  focusRate_ = properTimeRate;
}

void RealtimeDriver::setLocalSecondsPerWallSecond(double localSecondsPerWallSecond) {
  assert(std::isfinite(localSecondsPerWallSecond) && localSecondsPerWallSecond > 0.0);
  config_.localSecondsPerWallSecond = localSecondsPerWallSecond;
}

void RealtimeDriver::setPaused(bool shouldPause) {
  paused_ = shouldPause;
  if (paused_) {
    // Wall time spent paused is not owed to the world on resume.
    turnsDue_ = 0.0;
    lagging_ = false;
  }
}

double RealtimeDriver::turnsPerWallSecond() const {
  return config_.localSecondsPerWallSecond / (focusRate_ * config_.secondsPerTurn);
}

RealtimePumpResult RealtimeDriver::pump(double wallDtSec, const StepFunction &step) {
  RealtimePumpResult result;
  if (paused_ || !(wallDtSec > 0.0) || !std::isfinite(wallDtSec)) {
    return result;
  }
  // In double: the int64 product of two large budgets would overflow.
  const double backlogCap = static_cast<double>(config_.maxTurnsPerFrame) *
                            static_cast<double>(config_.maxBacklogFrames);
  turnsDue_ = std::min(turnsDue_ + (wallDtSec * turnsPerWallSecond()), backlogCap);
  while (turnsDue_ >= 1.0 && result.turnsAdvanced < config_.maxTurnsPerFrame) {
    turnsDue_ -= 1.0;
    ++result.turnsAdvanced;
    if (step()) {
      // Stop on the arrival turn: nothing after it runs this frame.
      result.pausedByArrival = true;
      setPaused(true);
      return result;
    }
  }
  lagging_ = turnsDue_ >= 1.0;
  result.lagging = lagging_;
  return result;
}

} // namespace game
