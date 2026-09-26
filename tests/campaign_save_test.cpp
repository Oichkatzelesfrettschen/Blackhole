/**
 * @file campaign_save_test.cpp
 * @brief Falsification gates for the versioned replay save: round trips
 *        reproduce the digest and the future, and every malformed or
 *        mismatched save is refused.
 */

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_sim_lines.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/save_format.h"

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
  // magic (4) + version (4) + HEAD tag (4) + length (4), then a 29-byte body.
  constexpr std::size_t headBody = 16;
  constexpr std::size_t headLength = 1 + 8 + 8 + 4 + 8;
  for (std::size_t bit = 0; bit < headLength * 8; ++bit) {
    std::vector<std::uint8_t> flipped = save;
    flipped.at(headBody + (bit / 8)) ^= static_cast<std::uint8_t>(1U << (bit % 8));
    ASSERT_FALSE(game::loadCampaign(flipped, &story).ok()) << "header bit " << bit;
  }

  // The turn section follows the command section; set its value to 2^62.
  std::vector<std::uint8_t> farTurn = save;
  const std::size_t commandsTag = headBody + headLength;
  const std::size_t commandsLength = static_cast<std::size_t>(farTurn.at(commandsTag + 4)) |
                                     (static_cast<std::size_t>(farTurn.at(commandsTag + 5)) << 8);
  const std::size_t turnValue = commandsTag + 8 + commandsLength + 8;
  for (std::size_t byte = 0; byte < 8; ++byte) {
    farTurn.at(turnValue + byte) = byte == 7 ? 0x40U : 0x00U;
  }
  EXPECT_EQ(loadError(farTurn, &story), "saved turn outside [0, K_SAVE_MAX_TURN]");
}
