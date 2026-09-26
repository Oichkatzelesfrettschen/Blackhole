/**
 * @file realtime_driver.h
 * @brief Maps wall-clock time onto whole campaign turns at the focused
 *        station's proper-time rate, outside the deterministic core.
 *
 * The campaign advances only in whole coordinate turns and never reads a wall
 * clock. This driver is the one place wall time enters: it owns a fractional
 * turn backlog, and each frame adds
 *   turnsDue += wallDt * localSecondsPerWallSecond / (focusRate * secondsPerTurn),
 * so with the player's view on a station whose clock runs at dtau/dt the
 * outside world runs 1 / (dtau/dt) times faster than the wall. On Miller's
 * orbit (dtau/dt = 1.6286e-5) with one-day turns and one local second per wall
 * second, that is 0.711 turns per wall second: a local minute is 42.6 outside
 * days. Changing focus changes only this mapping, never what a turn does.
 *
 * The driver steps the campaign one turn at a time through a callback and
 * asks, after every turn, whether that turn's arrivals request a pause; a pause
 * stops the frame on the arrival turn itself and discards the backlog. A frame
 * advances at most maxTurnsPerFrame turns; past that the backlog is capped and
 * lagging() reports that the world runs slower than the requested rate.
 * Because the core sees only the ordered sequence of single-turn advances and
 * the commands issued between them, any focus, frame-rate, or pause schedule
 * reaches the same state at the same turn.
 */

#ifndef BLACKHOLE_GAME_REALTIME_DRIVER_H
#define BLACKHOLE_GAME_REALTIME_DRIVER_H

#include <cstdint>
#include <functional>

namespace game {

/// Fastest real-time scale the controls offer: one local hour per wall second.
inline constexpr double K_MAX_LOCAL_SECONDS_PER_WALL_SECOND = 3600.0;
/// Largest manual batch the controls offer (the "Advance 25" button).
inline constexpr std::int64_t K_MAX_MANUAL_BATCH_TURNS = 25;

struct RealtimeDriverConfig {
  double secondsPerTurn = 86400.0;          ///< Coordinate seconds per campaign turn.
  double localSecondsPerWallSecond = 1.0;   ///< 1 = real time at the focused station.
  std::int64_t maxTurnsPerFrame = 64;       ///< Turn budget per pump.
  std::int64_t maxBacklogFrames = 4;        ///< Backlog cap, in frame budgets.
};

/** @brief What one pump did. */
struct RealtimePumpResult {
  std::int64_t turnsAdvanced = 0;
  bool pausedByArrival = false; ///< A turn's arrivals requested a pause.
  bool lagging = false;         ///< The frame budget ran out with whole turns still due.
};

class RealtimeDriver {
public:
  /** @brief Advances the campaign one turn; returns true when that turn's
   *         arrivals request a pause. */
  using StepFunction = std::function<bool()>;

  explicit RealtimeDriver(RealtimeDriverConfig config = {});

  /** @brief dtau/dt of the station the player is watching, in (0, 1]. */
  void setFocusRate(double properTimeRate);
  [[nodiscard]] double focusRate() const { return focusRate_; }

  /** @brief Changes the real-time scale in place. The backlog already owed
   *         (fractional or lagging) is wall time the world has not yet run,
   *         so it carries over; only turns accrued from now on use the new
   *         scale. */
  void setLocalSecondsPerWallSecond(double localSecondsPerWallSecond);
  [[nodiscard]] double localSecondsPerWallSecond() const {
    return config_.localSecondsPerWallSecond;
  }

  void setPaused(bool shouldPause);
  [[nodiscard]] bool paused() const { return paused_; }

  /** @brief Outside turns per wall second at the current focus. */
  [[nodiscard]] double turnsPerWallSecond() const;

  /** @brief Adds wallDtSec of wall time to the backlog and advances whole
   *         turns through `step` until the backlog, the frame budget, or a
   *         pause request runs out. A paused driver accrues nothing. */
  RealtimePumpResult pump(double wallDtSec, const StepFunction &step);

  [[nodiscard]] double turnsDue() const { return turnsDue_; }
  [[nodiscard]] bool lagging() const { return lagging_; }

private:
  RealtimeDriverConfig config_;
  double focusRate_ = 1.0;
  double turnsDue_ = 0.0;
  bool paused_ = false;
  bool lagging_ = false;
};

} // namespace game

#endif // BLACKHOLE_GAME_REALTIME_DRIVER_H
