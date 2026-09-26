/**
 * @file campaign_save_test.cpp
 * @brief Falsification gates for the versioned replay save: round trips
 *        reproduce the digest and the future, and every malformed or
 *        mismatched save is refused.
 */

#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "campaign_test_field.h"
#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_sim_lines.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/realtime_driver.h"
#include "game/save_format.h"
#include "game/station_node.h"
#include "game/time_field.h"

namespace {

game::EventSet shippedStory() {
  const game::EventLoadResult loaded =
      game::loadEventSetFile(std::string(BLACKHOLE_SOURCE_DIR) + "/assets/events/host_goes_dark.json");
  EXPECT_TRUE(loaded.ok()) << loaded.error;
  return loaded.story;
}

/** @brief Plays the default scenario's pod line for `turns` turns. */
void playPod(game::CampaignSession &session, std::int64_t turns) {
  for (const game::FleetId fleet : campaign_sim::deepFleets(campaign_sim::Commit::Pod)) {
    static_cast<void>(session.issuePlaceFleet(fleet, 0, game::OrbitLane::Prograde,
                                              game::StationKeeping::Hover));
  }
  for (std::int64_t turn = 0; turn < turns; ++turn) {
    if (turn % 9 == 0) {
      for (game::FleetId fleet = 1; fleet <= 6; ++fleet) {
        static_cast<void>(session.issueAssignTask(fleet, 24.0));
      }
    }
    session.state().advanceTurn();
  }
}

/** @brief Continues two sessions in lockstep and compares every digest. */
void expectSameFuture(game::CampaignSession &lhs, game::CampaignSession &rhs, std::int64_t turns) {
  for (std::int64_t turn = 0; turn < turns; ++turn) {
    if (turn % 13 == 0) {
      static_cast<void>(lhs.issueAssignTask(1, 12.0));
      static_cast<void>(rhs.issueAssignTask(1, 12.0));
    }
    lhs.state().advanceTurn();
    rhs.state().advanceTurn();
    ASSERT_EQ(lhs.state().stateDigest(), rhs.state().stateDigest()) << "turn " << turn;
  }
}

std::string loadError(const std::vector<std::uint8_t> &bytes, const game::EventSet *story) {
  return game::loadCampaign(bytes, story).error;
}

// Section offsets: magic (4) + version (4), then HEAD tag (4) + length (4)
// and its 29-byte body, then CMDS tag + length + body, then TURN.
constexpr std::size_t K_HEAD_BODY = 16;
constexpr std::size_t K_HEAD_LENGTH = 1 + 8 + 8 + 4 + 8;
constexpr std::size_t K_COMMANDS_TAG = K_HEAD_BODY + K_HEAD_LENGTH;

void writeI64(std::vector<std::uint8_t> &bytes, std::size_t offset, std::int64_t value) {
  const auto bits = static_cast<std::uint64_t>(value);
  for (std::size_t byte = 0; byte < 8; ++byte) {
    bytes.at(offset + byte) = static_cast<std::uint8_t>(bits >> (8U * byte));
  }
}

std::size_t turnValueOffset(const std::vector<std::uint8_t> &bytes) {
  const std::size_t commandsLength = static_cast<std::size_t>(bytes.at(K_COMMANDS_TAG + 4)) |
                                     (static_cast<std::size_t>(bytes.at(K_COMMANDS_TAG + 5)) << 8);
  return K_COMMANDS_TAG + 8 + commandsLength + 8;
}

/** @brief Seconds one load takes; the refusals under test return before any
 *         replayed turn, so a generous bound separates them from a replay. */
double loadSeconds(const std::vector<std::uint8_t> &bytes, const game::EventSet *story,
                   std::string &error) {
  const auto start = std::chrono::steady_clock::now();
  error = game::loadCampaign(bytes, story).error;
  return std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
}

} // namespace

// Falsifier: a reloaded default campaign whose bytes differ from the original
// at the save turn, or whose future under the same commands diverges.
TEST(CampaignSave, DefaultScenarioRoundTripsAndContinuesIdentically) {
  game::CampaignSession original(42);
  playPod(original, 300);
  // An order issued this turn and not yet advanced is part of the save.
  ASSERT_TRUE(original.issueAssignTask(2, 6.0));
  const std::vector<std::uint8_t> save = game::saveCampaign(original);
  game::CampaignLoadResult loaded = game::loadCampaign(save, nullptr);
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  EXPECT_EQ(loaded.session->state().turn(), 300);
  EXPECT_EQ(loaded.session->state().serializeState(), original.state().serializeState());
  EXPECT_EQ(game::saveCampaign(*loaded.session), save);
  expectSameFuture(original, *loaded.session, 200);
}

// Falsifier: a colony-story save, with orders from both the host and the
// colony, failing to reproduce the digest or the future.
TEST(CampaignSave, ColonyStoryRoundTripsWithItsStory) {
  const game::EventSet story = shippedStory();
  game::CampaignSession original(5, story, 0);
  for (std::int64_t turn = 0; turn < 900; ++turn) {
    if (turn % 50 == 0) {
      ASSERT_TRUE(original.issueAssignTask(1, 2.0, turn % 100 == 0 ? game::K_AUTHORITY_NODE
                                                                   : game::K_FIRST_COLONY_NODE));
    }
    original.state().advanceTurn();
  }
  const std::vector<std::uint8_t> save = game::saveCampaign(original);
  game::CampaignLoadResult loaded = game::loadCampaign(save, &story);
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  EXPECT_EQ(loaded.session->state().stateDigest(), original.state().stateDigest());
  EXPECT_EQ(loaded.session->colonyBand(), 0);
  expectSameFuture(original, *loaded.session, 400);
}

// Falsifier: any of these loading -- bad magic, an unknown version, every
// truncation, a trailing byte, a tampered digest, a tampered command, a
// missing or different story.
TEST(CampaignSave, MalformedAndMismatchedSavesAreRefused) {
  const game::EventSet story = shippedStory();
  game::CampaignSession original(9, story, 0);
  ASSERT_TRUE(original.issueAssignTask(1, 3.0, game::K_FIRST_COLONY_NODE));
  original.state().advanceTurns(40);
  const std::vector<std::uint8_t> save = game::saveCampaign(original);
  ASSERT_TRUE(game::loadCampaign(save, &story).ok());

  std::vector<std::uint8_t> badMagic = save;
  badMagic.at(0) = 'X';
  EXPECT_EQ(loadError(badMagic, &story), "not a campaign save");

  std::vector<std::uint8_t> future = save;
  future.at(4) = static_cast<std::uint8_t>(game::K_SAVE_FORMAT_VERSION + 1);
  EXPECT_NE(loadError(future, &story).find("unknown save format version"), std::string::npos);

  for (std::size_t length = 0; length < save.size(); ++length) {
    const std::vector<std::uint8_t> truncated(save.begin(),
                                              save.begin() + static_cast<std::ptrdiff_t>(length));
    ASSERT_FALSE(game::loadCampaign(truncated, &story).ok()) << "length " << length;
  }

  std::vector<std::uint8_t> trailing = save;
  trailing.push_back(0);
  EXPECT_FALSE(loadError(trailing, &story).empty());

  std::vector<std::uint8_t> tamperedDigest = save;
  tamperedDigest.back() ^= 0x01U;
  EXPECT_EQ(loadError(tamperedDigest, &story), "replay digest differs from the saved digest");

  // The command's cost is the last f64 before its origin node: flip its low
  // mantissa bit so the replay contracts a different task.
  std::vector<std::uint8_t> tamperedCommand = save;
  const std::size_t headEnd = 8 + 8 + 1 + 8 + 8 + 4 + 8;
  const std::size_t costOffset = headEnd + 8 + 4 + 8 + 1 + 4 + 4 + 1 + 1;
  tamperedCommand.at(costOffset) ^= 0x01U;
  EXPECT_EQ(loadError(tamperedCommand, &story), "replay digest differs from the saved digest");

  EXPECT_FALSE(loadError(save, nullptr).empty());
  game::EventSet other = story;
  other.params.front().max += 1;
  EXPECT_FALSE(loadError(save, &other).empty());
}

// Falsifier: a save with any single header bit flipped loading -- every field
// (scenario, seed, spin, colony band, story digest) is bound to the session it
// rebuilds -- or a turn field corrupted to 2^62 being replayed at all.
TEST(CampaignSave, EveryHeaderBitAndAnOutOfRangeTurnAreRefused) {
  const game::EventSet story = shippedStory();
  game::CampaignSession original(9, story, 0);
  ASSERT_TRUE(original.issueAssignTask(1, 3.0, game::K_FIRST_COLONY_NODE));
  original.state().advanceTurns(40);
  const std::vector<std::uint8_t> save = game::saveCampaign(original);
  for (std::size_t bit = 0; bit < K_HEAD_LENGTH * 8; ++bit) {
    std::vector<std::uint8_t> flipped = save;
    flipped.at(K_HEAD_BODY + (bit / 8)) ^= static_cast<std::uint8_t>(1U << (bit % 8));
    ASSERT_FALSE(game::loadCampaign(flipped, &story).ok()) << "header bit " << bit;
  }

  std::vector<std::uint8_t> farTurn = save;
  writeI64(farTurn, turnValueOffset(farTurn), std::int64_t{1} << 62);
  EXPECT_EQ(loadError(farTurn, &story).rfind("saved turn outside [0, ", 0), 0U);
}

// Falsifier: a scenario's budget other than four wall hours at its fastest
// advance rate -- manual batches for stations near dtau/dt = 1, real time at
// the Miller clock for the deep colony -- or a deep budget too short for the
// colony's whole charter.
TEST(CampaignSave, ReplayBudgetFollowsTheScenario) {
  const game::EventSet story = shippedStory();
  const auto manualBudget = static_cast<std::int64_t>(std::ceil(
      game::K_SAVE_SESSION_WALL_SEC * static_cast<double>(game::K_MAX_MANUAL_BATCH_TURNS) *
      game::K_SAVE_MANUAL_BATCHES_PER_WALL_SEC));
  EXPECT_EQ(manualBudget, 3600000);
  const game::CampaignSession m87(42);
  EXPECT_EQ(game::saveReplayTurnBudget(m87.state()), manualBudget);
  const game::CampaignSession survey(9, story, game::K_SURVEY_BAND);
  EXPECT_EQ(game::saveReplayTurnBudget(survey.state()), manualBudget);

  const game::CampaignSession deep(9, story, game::K_MILLER_BAND);
  const double millerRate = deep.state().nodes().at(game::K_FIRST_COLONY_NODE).clock.rate();
  const double secondsPerTurn = deep.state().config().secondsPerTurn;
  const std::int64_t deepBudget = game::saveReplayTurnBudget(deep.state());
  EXPECT_EQ(deepBudget,
            static_cast<std::int64_t>(std::ceil(game::K_SAVE_SESSION_WALL_SEC *
                                                game::K_MAX_LOCAL_SECONDS_PER_WALL_SECOND /
                                                (millerRate * secondsPerTurn))));
  EXPECT_NEAR(static_cast<double>(deepBudget), 3.68e7, 0.01e7);
  const double charterTurns =
      static_cast<double>(game::K_COLONY_MISSION_SEC) / (millerRate * secondsPerTurn);
  EXPECT_GT(static_cast<double>(deepBudget), charterTurns);
}

namespace {

/** @brief The fake field with the near band at the Q48 clock floor. */
class ClockFloorField final : public game::TimeField {
public:
  [[nodiscard]] double properTimeRate(double radiusCm, game::Observer /*observer*/) const override {
    return radiusCm < 970.0 ? 0x1p-48 : 1.0;
  }
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override {
    return std::fabs(toRadiusCm - fromRadiusCm);
  }
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override {
    return std::isfinite(radiusCm) && radiusCm > 1.0;
  }
};

} // namespace

// Falsifier: a valid campaign whose slowest station sits at the Q48 clock
// floor (rateQ == 1) with one-second turns producing an out-of-range or
// negative budget -- its unclamped value, 1.46e22 turns, is past int64 --
// instead of the documented ceiling.
TEST(CampaignSave, ClockFloorBudgetIsClampedToTheCeiling) {
  const ClockFloorField field;
  game::CampaignConfig config = campaign_test::fakeConfig();
  ASSERT_DOUBLE_EQ(config.secondsPerTurn, 1.0);
  game::ColonyConfig colony;
  colony.bandIndex = 0; // radius 960, dtau/dt = 2^-48
  config.colonies = {colony};
  const game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  ASSERT_DOUBLE_EQ(state.nodes().at(game::K_FIRST_COLONY_NODE).clock.rate(), 0x1p-48);
  EXPECT_EQ(game::saveReplayTurnBudget(state), game::K_SAVE_REPLAY_TURN_CEILING);
}

// Falsifier: a tiny save whose turn field sits past its scenario's budget (or
// at the 1e8 turns a global cap once admitted), or whose command log runs past
// its turn, replaying any turn before the refusal. Refusal is asserted by
// message; the time bound is generous against a 3.6e6-turn replay.
TEST(CampaignSave, OverBudgetTurnAndStrayCommandsAreRefusedBeforeReplay) {
  const game::EventSet story = shippedStory();
  game::CampaignSession m87(42);
  playPod(m87, 20);
  game::CampaignSession deep(9, story, game::K_MILLER_BAND);
  ASSERT_TRUE(deep.issueAssignTask(1, 3.0, game::K_FIRST_COLONY_NODE));
  deep.state().advanceTurns(20);

  struct Case {
    game::CampaignSession *session;
    const game::EventSet *story;
  };
  for (const Case &scenario : {Case{&m87, nullptr}, Case{&deep, &story}}) {
    const std::vector<std::uint8_t> save = game::saveCampaign(*scenario.session);
    ASSERT_TRUE(game::loadCampaign(save, scenario.story).ok());
    const std::int64_t budget = game::saveReplayTurnBudget(scenario.session->state());
    for (const std::int64_t turn : {budget + 1, std::int64_t{100000000}}) {
      std::vector<std::uint8_t> overBudget = save;
      writeI64(overBudget, turnValueOffset(overBudget), turn);
      std::string error;
      const double seconds = loadSeconds(overBudget, scenario.story, error);
      EXPECT_EQ(error, "saved turn outside [0, " + std::to_string(budget) +
                           "], this scenario's replay budget")
          << "turn " << turn;
      EXPECT_LT(seconds, 0.5) << "turn " << turn;
    }

    // An in-budget turn with the first command moved past it: refused on the
    // log, not after replaying every turn up to the budget.
    std::vector<std::uint8_t> strayCommand = save;
    writeI64(strayCommand, turnValueOffset(strayCommand), budget);
    writeI64(strayCommand, K_COMMANDS_TAG + 12, budget + 1);
    std::string error;
    const double seconds = loadSeconds(strayCommand, scenario.story, error);
    EXPECT_EQ(error, "saved commands are out of turn order or beyond the saved turn");
    EXPECT_LT(seconds, 0.5);
  }
}

// Falsifier: an M87 save whose spin has only its sign flipped loading. The
// session rebuilds from the header's spin, so the header check alone cannot
// catch it; the replay digest must, because the state carries the sense of
// rotation beside the spin deficit.
TEST(CampaignSave, SpinSignFlipIsRefused) {
  game::CampaignSession original(42);
  playPod(original, 60);
  std::vector<std::uint8_t> save = game::saveCampaign(original);
  ASSERT_TRUE(game::loadCampaign(save, nullptr).ok());
  // HEAD body starts at byte 16: u8 scenario, u64 seed, then the f64 spin,
  // whose sign bit is the top bit of its last little-endian byte.
  constexpr std::size_t spinSignByte = 16 + 1 + 8 + 7;
  save.at(spinSignByte) ^= 0x80U;
  EXPECT_EQ(loadError(save, nullptr), "replay digest differs from the saved digest");
}
