/**
 * @file campaign_colony_outcome_test.cpp
 * @brief Falsification gates for the colony outcome axes: production on the
 *        colony's clock inside its mission window, a dark host banking
 *        nothing, and a tech tier the outcome reads as a victory.
 */

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "campaign_test_field.h"
#include "game/campaign.h"
#include "game/campaign_view.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/station_node.h"

namespace {

/** @brief The fake field with one colony on band 995 (rate 1, 5 turns from
 *         the host), one local tick and one energy unit per turn. */
game::CampaignConfig colonyConfig(const std::string &storyJson, std::int64_t missionSec) {
  game::CampaignConfig config = campaign_test::fakeConfig();
  game::ColonyConfig colony;
  colony.bandIndex = 1;
  colony.localTickSec = 1;
  colony.energyPerTick = 1.0;
  colony.missionProperSec = missionSec;
  config.colonies = {colony};
  const game::EventLoadResult loaded = game::parseEventSet(storyJson);
  EXPECT_TRUE(loaded.ok()) << loaded.error;
  config.story = loaded.story;
  return config;
}

} // namespace

// Falsifier: production outside the ten-local-second mission window, energy
// banked before a report's five-turn flight, or the colony still receiving
// after its window closed.
TEST(ColonyOutcome, ProductionStopsWhenTheMissionWindowCloses) {
  const campaign_test::FakeTimeField field;
  game::CampaignState state(
      colonyConfig(R"({"events": [{"id": 1, "triggers": [{"turn_at_least": 20}],
                        "effects": [{"emit": {"kind": "tech_packet", "to": "colony", "points": 1}}]}]})",
                   10),
      field);
  ASSERT_TRUE(state.valid());
  state.advanceTurns(5);
  EXPECT_DOUBLE_EQ(state.energyUnits(), 0.0);
  state.advanceTurns(1);
  EXPECT_DOUBLE_EQ(state.energyUnits(), 1.0); // the turn-1 report lands at 6
  state.advanceTurns(40);
  EXPECT_DOUBLE_EQ(state.energyUnits(), 10.0);
  EXPECT_TRUE(state.nodes().at(game::K_FIRST_COLONY_NODE).dark());
  EXPECT_EQ(state.nodes().at(game::K_FIRST_COLONY_NODE).techPoints, 0); // packet landed at 25
}

// Falsifier: a report reaching the host after its dark turn banking energy,
// or the lost production going unrecorded.
TEST(ColonyOutcome, DarkHostBanksNothing) {
  const campaign_test::FakeTimeField field;
  game::CampaignState state(
      colonyConfig(R"({"events": [{"id": 1, "triggers": [{"turn_at_least": 8}],
                        "effects": [{"set_flag": "dark"}]}]})",
                   0),
      field);
  ASSERT_TRUE(state.valid());
  state.advanceTurns(30);
  // Reports from turns 1..3 land at 6..8, before the host goes dark at the
  // end of turn 8's deliveries; every later report is lost.
  EXPECT_DOUBLE_EQ(state.energyUnits(), 3.0);
  EXPECT_DOUBLE_EQ(state.renderSnapshot().energyLostToDarkness, 30.0 - 5.0 - 3.0);
}

// Falsifier: the outcome ignoring the tech tier, or declaring the win on any
// turn but the one the tier-reaching packet arrives.
TEST(ColonyOutcome, TechTierIsAVictoryAxis) {
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config = colonyConfig(R"({
      "tech_tiers": [{"points": 1, "name": "a"}, {"points": 3, "name": "b"}],
      "events": [
        {"id": 1, "triggers": [{"turn_at_least": 1}],
         "effects": [{"emit": {"kind": "tech_packet", "to": "colony", "points": 1}},
                     {"schedule": {"event": 2, "delay_turns": 1}}]},
        {"id": 2, "mode": "scheduled",
         "effects": [{"emit": {"kind": "tech_packet", "to": "colony", "points": 1}},
                     {"schedule": {"event": 2, "delay_turns": 1}}]}]})",
                                             0);
  config.victoryTechTier = 2;
  game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  state.advanceTurns(7);
  EXPECT_EQ(state.colonyTechTier(), 1);
  EXPECT_EQ(state.status(), game::CampaignStatus::Ongoing);
  state.advanceTurns(1); // the third packet (emitted turn 3) lands at 8
  EXPECT_EQ(state.colonyTechTier(), 2);
  EXPECT_EQ(state.status(), game::CampaignStatus::Won);
  EXPECT_EQ(state.clearedTurn(), 8);
  EXPECT_EQ(state.renderSnapshot().colonyTechTier, 2);
}
