/**
 * @file campaign_realtime_determinism_test.cpp
 * @brief Falsification gates for the real-time driver: the wall-to-turn
 *        mapping, pause-on-arrival stopping on the arrival turn, the lagging
 *        indicator, and identical per-turn digests for one command log played
 *        under different focus, frame-batch, and pause schedules.
 */

#include <gtest/gtest.h>

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <map>
#include <set>
#include <string>
#include <vector>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/command.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/fleet.h"
#include "game/inbox.h"
#include "game/observer.h"
#include "game/realtime_driver.h"

namespace {

constexpr double K_MILLER_RATE = 1.6286e-5;
constexpr double K_DAY_SEC = 86400.0;
constexpr std::int64_t K_RUN_TURNS = 600;

/** @brief A command log keyed by the coordinate turn it is issued on. */
using CommandLog = std::map<std::int64_t, std::vector<game::Command>>;

CommandLog scriptedLog() {
  CommandLog log;
  game::Command assign;
  assign.type = game::CommandType::AssignTask;
  assign.properTimeCostSec = 24.0 * 3600.0;
  for (std::int64_t turn = 0; turn < K_RUN_TURNS; turn += 17) {
    for (game::FleetId fleet = 1; fleet <= 6; ++fleet) {
      assign.fleet = fleet;
      log[turn].push_back(assign);
    }
  }
  game::Command dive;
  dive.type = game::CommandType::PlaceFleet;
  dive.fleet = 6;
  dive.targetBand = 0;
  dive.lane = game::OrbitLane::Prograde;
  dive.station = game::StationKeeping::Hover;
  log[40].push_back(dive);
  return log;
}

/** @brief One schedule's frames: wall seconds per frame, the focus rate for
 *         the frame, and turns after which the step requests a pause (standing
 *         in for a flagged arrival). */
struct Schedule {
  double focusRate = 1.0;
  std::vector<double> frameWallSec;
  std::set<std::int64_t> pauseAfterTurns;
  std::int64_t maxTurnsPerFrame = 64;
  bool alternateFocus = false; ///< Swap focus between Miller and the far band each frame.
};

/** @brief Plays the log under a schedule; returns the digest after every turn. */
std::vector<std::uint64_t> playSchedule(const Schedule &schedule, const CommandLog &log) {
  game::CampaignSession session(11);
  game::CampaignState &campaign = session.state();
  std::vector<std::uint64_t> digests;
  game::RealtimeDriverConfig config;
  config.secondsPerTurn = K_DAY_SEC;
  config.maxTurnsPerFrame = schedule.maxTurnsPerFrame;
  game::RealtimeDriver driver(config);
  driver.setFocusRate(schedule.focusRate);
  const game::RealtimeDriver::StepFunction step = [&]() {
    const auto due = log.find(campaign.turn());
    if (due != log.end()) {
      for (const game::Command &command : due->second) {
        static_cast<void>(campaign.issueCommand(command));
      }
    }
    campaign.advanceTurn();
    digests.push_back(campaign.stateDigest());
    return schedule.pauseAfterTurns.contains(campaign.turn());
  };
  std::size_t frame = 0;
  while (campaign.turn() < K_RUN_TURNS) {
    if (schedule.alternateFocus) {
      driver.setFocusRate(frame % 2 == 0 ? K_MILLER_RATE : 0.97);
    }
    const double wallSec = schedule.frameWallSec.at(frame % schedule.frameWallSec.size());
    const game::RealtimePumpResult result = driver.pump(wallSec, step);
    if (result.pausedByArrival) {
      EXPECT_TRUE(schedule.pauseAfterTurns.contains(campaign.turn()));
      driver.setPaused(false); // the player reads the inbox and resumes
    }
    ++frame;
  }
  digests.resize(static_cast<std::size_t>(K_RUN_TURNS));
  return digests;
}

/** @brief Digests after every turn and the turns the inbox paused on. */
struct StoryPlay {
  std::vector<std::uint64_t> digests;
  std::vector<std::int64_t> pauseTurns;
};

/** @brief Plays the host-goes-dark story on Miller's orbit under a schedule:
 *         pauses come from the colony inbox (silence and collapse notices),
 *         and every 250 turns the colony orders the survey fleet. */
StoryPlay playStory(const Schedule &schedule, const game::EventSet &story, std::int64_t turns) {
  game::CampaignSession session(4, story, 0);
  game::CampaignState &campaign = session.state();
  game::Inbox inbox(game::K_FIRST_COLONY_NODE);
  StoryPlay play;
  game::RealtimeDriverConfig config;
  config.maxTurnsPerFrame = schedule.maxTurnsPerFrame;
  game::RealtimeDriver driver(config);
  driver.setFocusRate(schedule.focusRate);
  const game::RealtimeDriver::StepFunction step = [&]() {
    if (campaign.turn() % 250 == 0) {
      static_cast<void>(session.issueAssignTask(1, 0.5, game::K_FIRST_COLONY_NODE));
    }
    campaign.advanceTurn();
    play.digests.push_back(campaign.stateDigest());
    return inbox.sync(campaign.arrivals());
  };
  std::size_t frame = 0;
  while (campaign.turn() < turns) {
    if (schedule.alternateFocus) {
      driver.setFocusRate(frame % 2 == 0 ? K_MILLER_RATE : 0.97);
    }
    if (driver.pump(schedule.frameWallSec.at(frame % schedule.frameWallSec.size()), step)
            .pausedByArrival) {
      play.pauseTurns.push_back(campaign.turn());
      driver.setPaused(false);
    }
    ++frame;
  }
  play.digests.resize(static_cast<std::size_t>(turns));
  return play;
}

} // namespace

// Falsifier: Miller focus mapping to anything but 1 / (1.6286e-5 * 86400) =
// 0.711 one-day turns per wall second at real time.
TEST(RealtimeDriver, MillerFocusRunsOutsideAtInverseRate) {
  game::RealtimeDriver driver;
  driver.setFocusRate(K_MILLER_RATE);
  EXPECT_NEAR(driver.turnsPerWallSecond(), 0.71067, 1e-4);
  driver.setFocusRate(1.0);
  EXPECT_DOUBLE_EQ(driver.turnsPerWallSecond(), 1.0 / K_DAY_SEC);
}

// Falsifier: a pause request honored a turn late or early, turns advancing
// while paused, or paused wall time owed to the world on resume.
TEST(RealtimeDriver, PauseStopsOnTheRequestingTurn) {
  game::RealtimeDriverConfig config;
  config.maxTurnsPerFrame = 1000;
  game::RealtimeDriver driver(config);
  driver.setFocusRate(K_MILLER_RATE);
  std::int64_t turn = 0;
  const game::RealtimeDriver::StepFunction step = [&]() { return ++turn == 7; };
  const game::RealtimePumpResult first = driver.pump(100.0, step); // 71 turns due
  EXPECT_TRUE(first.pausedByArrival);
  EXPECT_EQ(turn, 7);
  EXPECT_EQ(first.turnsAdvanced, 7);
  EXPECT_TRUE(driver.paused());
  EXPECT_EQ(driver.pump(100.0, step).turnsAdvanced, 0);
  EXPECT_EQ(turn, 7);
  driver.setPaused(false);
  EXPECT_DOUBLE_EQ(driver.turnsDue(), 0.0);
  EXPECT_EQ(driver.pump(1.5 / 0.71067, step).turnsAdvanced, 1);
}

// Falsifier: the budget exceeded, the lagging flag missing while whole turns
// remain due, or the backlog growing without bound.
TEST(RealtimeDriver, FrameBudgetCapsTurnsAndFlagsLagging) {
  game::RealtimeDriverConfig config;
  config.maxTurnsPerFrame = 4;
  config.maxBacklogFrames = 2;
  game::RealtimeDriver driver(config);
  driver.setFocusRate(K_MILLER_RATE);
  const game::RealtimeDriver::StepFunction step = []() { return false; };
  const game::RealtimePumpResult result = driver.pump(1000.0, step);
  EXPECT_EQ(result.turnsAdvanced, 4);
  EXPECT_TRUE(result.lagging);
  EXPECT_TRUE(driver.lagging());
  EXPECT_LE(driver.turnsDue(), 8.0);
  const game::RealtimePumpResult drained = driver.pump(1e-9, step);
  EXPECT_EQ(drained.turnsAdvanced, 4);
  EXPECT_FALSE(drained.lagging);
}

// Falsifier: a change of real-time scale dropping the turns already owed --
// a fractional backlog that the next short frame should tip into a turn, or
// a lagging backlog above the frame budget.
TEST(RealtimeDriver, ScaleChangeKeepsTheBacklog) {
  const game::RealtimeDriver::StepFunction step = []() { return false; };
  game::RealtimeDriver fractional;
  fractional.setFocusRate(K_MILLER_RATE);
  EXPECT_EQ(fractional.pump(1.0, step).turnsAdvanced, 0); // 0.711 turns owed
  fractional.setLocalSecondsPerWallSecond(2.0);
  EXPECT_NEAR(fractional.turnsDue(), 0.71067, 1e-4);
  EXPECT_DOUBLE_EQ(fractional.localSecondsPerWallSecond(), 2.0);
  // 0.25 s at twice the scale adds 0.355 turns: the carried 0.711 tips it over.
  EXPECT_EQ(fractional.pump(0.25, step).turnsAdvanced, 1);

  game::RealtimeDriverConfig config;
  config.maxTurnsPerFrame = 4;
  config.maxBacklogFrames = 2;
  game::RealtimeDriver lagging(config);
  lagging.setFocusRate(K_MILLER_RATE);
  EXPECT_EQ(lagging.pump(1000.0, step).turnsAdvanced, 4);
  const double owed = lagging.turnsDue();
  EXPECT_GE(owed, 4.0);
  lagging.setLocalSecondsPerWallSecond(3.0);
  EXPECT_DOUBLE_EQ(lagging.turnsDue(), owed);
  EXPECT_TRUE(lagging.lagging());
  EXPECT_EQ(lagging.pump(1e-9, step).turnsAdvanced, 4);
}

// Falsifier: one command log reaching a different digest on any turn when
// played at authority focus with smooth frames, at Miller focus with a tiny
// per-frame budget and jittered frames, or with focus flipping every frame
// and pauses interrupting the stream.
TEST(RealtimeDeterminism, ThreeSchedulesGiveIdenticalPerTurnDigests) {
  const CommandLog log = scriptedLog();

  Schedule smooth;
  smooth.focusRate = 1.0;
  smooth.frameWallSec = {K_DAY_SEC * 2.5}; // 2.5 turns per frame at unit rate
  const std::vector<std::uint64_t> smoothDigests = playSchedule(smooth, log);

  Schedule miller;
  miller.focusRate = K_MILLER_RATE;
  miller.frameWallSec = {0.016, 3.0, 0.5, 40.0, 0.001};
  miller.maxTurnsPerFrame = 3;
  const std::vector<std::uint64_t> millerDigests = playSchedule(miller, log);

  Schedule paused;
  paused.alternateFocus = true;
  paused.frameWallSec = {7.0, 0.3, 90.0};
  paused.pauseAfterTurns = {1, 40, 41, 299, 500};
  const std::vector<std::uint64_t> pausedDigests = playSchedule(paused, log);

  ASSERT_EQ(smoothDigests.size(), static_cast<std::size_t>(K_RUN_TURNS));
  for (std::size_t turn = 0; turn < smoothDigests.size(); ++turn) {
    ASSERT_EQ(smoothDigests.at(turn), millerDigests.at(turn)) << "turn " << turn + 1;
    ASSERT_EQ(smoothDigests.at(turn), pausedDigests.at(turn)) << "turn " << turn + 1;
  }
}

// Falsifier: the colony story -- colony-origin orders, packets, and the
// inbox's own pauses on the silence and collapse notices -- reaching a
// different digest on any turn, or pausing on different turns, under Miller
// focus with large frames, unit focus with day-scale frames, or flipping
// focus with a seven-turn budget.
TEST(RealtimeDeterminism, ColonyStoryWithInboxPausesIsScheduleIndependent) {
  const game::EventLoadResult loaded = game::loadEventSetFile(
      std::string(BLACKHOLE_SOURCE_DIR) + "/assets/events/host_goes_dark.json");
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  game::CampaignSession probe(4, loaded.story, 0);
  const std::int64_t turns = probe.state().storyParam("dark_turn").value_or(0) +
                             probe.state().nodeDelayTurns(0, 1) +
                             (4 * probe.state().storyParam("packet_period").value_or(0));

  Schedule miller;
  miller.focusRate = K_MILLER_RATE;
  miller.frameWallSec = {3000.0, 17.0};
  miller.maxTurnsPerFrame = 5000;
  const StoryPlay millerPlay = playStory(miller, loaded.story, turns);

  Schedule unit;
  unit.focusRate = 1.0;
  unit.frameWallSec = {K_DAY_SEC * 50.0};
  const StoryPlay unitPlay = playStory(unit, loaded.story, turns);

  Schedule flipping;
  flipping.alternateFocus = true;
  flipping.frameWallSec = {40.0, 0.2, 9.0};
  flipping.maxTurnsPerFrame = 7;
  const StoryPlay flippingPlay = playStory(flipping, loaded.story, turns);

  EXPECT_EQ(millerPlay.pauseTurns.size(), 2U);
  EXPECT_EQ(millerPlay.pauseTurns, unitPlay.pauseTurns);
  EXPECT_EQ(millerPlay.pauseTurns, flippingPlay.pauseTurns);
  ASSERT_EQ(millerPlay.digests.size(), static_cast<std::size_t>(turns));
  for (std::size_t turn = 0; turn < millerPlay.digests.size(); ++turn) {
    ASSERT_EQ(millerPlay.digests.at(turn), unitPlay.digests.at(turn)) << "turn " << turn + 1;
    ASSERT_EQ(millerPlay.digests.at(turn), flippingPlay.digests.at(turn)) << "turn " << turn + 1;
  }
}

// Falsifier: budgets whose int64 product overflows wrapping the backlog cap
// negative, so the driver never advances.
TEST(RealtimeDriver, HugeBudgetsDoNotOverflowTheBacklogCap) {
  game::RealtimeDriverConfig config;
  config.maxTurnsPerFrame = std::int64_t{1} << 40;
  config.maxBacklogFrames = std::int64_t{1} << 40;
  game::RealtimeDriver driver(config);
  driver.setFocusRate(K_MILLER_RATE);
  std::int64_t steps = 0;
  const game::RealtimeDriver::StepFunction step = [&steps]() {
    ++steps;
    return false;
  };
  const game::RealtimePumpResult result = driver.pump(10.0, step);
  EXPECT_EQ(result.turnsAdvanced, 7); // 10 s x 0.7107 turns per wall second
  EXPECT_EQ(steps, 7);
  EXPECT_GE(driver.turnsDue(), 0.0);
}
