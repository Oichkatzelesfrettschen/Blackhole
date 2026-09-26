/**
 * @file campaign_colony_outcome_test.cpp
 * @brief Falsification gates for the colony outcome axes: production on the
 *        colony's clock inside its mission window, a dark host banking
 *        nothing, and a tech tier the outcome reads as a victory.
 */

#include <gtest/gtest.h>

#include <bit>
#include <cmath>
#include <cstdint>
#include <limits>
#include <string>

#include "campaign_test_field.h"
#include "game/campaign.h"
#include "game/campaign_view.h"
#include "game/command.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/event_loader.h"
#include "game/observer.h"
#include "game/station_node.h"
#include "game/time_field.h"

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

// Falsifier: the outcome ignoring the tech tier, or declaring the win before
// the host can know of it. The colony reaches tier 2 when the third packet
// lands at turn 8; its production report stamped with those points leaves at
// turn 9 (a turn's reports ship before its deliveries land) and reaches the
// host 5 turns later, at 14 -- the turn the win latches.
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
  state.advanceTurns(8); // the third packet (emitted turn 3) lands at 8
  EXPECT_EQ(state.colonyTechTier(), 2);
  EXPECT_LT(state.hostKnownColonyTechTier(), 2);
  EXPECT_EQ(state.status(), game::CampaignStatus::Ongoing);
  state.advanceTurns(5);
  EXPECT_EQ(state.status(), game::CampaignStatus::Ongoing);
  state.advanceTurns(1);
  EXPECT_EQ(state.hostKnownColonyTechTier(), 2);
  EXPECT_EQ(state.status(), game::CampaignStatus::Won);
  EXPECT_EQ(state.clearedTurn(), 14);
  EXPECT_EQ(state.perceivedSnapshot(game::K_AUTHORITY_NODE).colonyTechTier, 2);
}

namespace {

/** @brief A field whose inner band runs at 1e-16, below the 2^-49 Q48 floor. */
class StoppedClockField final : public game::TimeField {
public:
  [[nodiscard]] double properTimeRate(double radiusCm, game::Observer /*observer*/) const override {
    return radiusCm < 970.0 ? 1e-16 : 1.0;
  }
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override {
    return std::fabs(toRadiusCm - fromRadiusCm);
  }
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override {
    return std::isfinite(radiusCm) && radiusCm > 1.0;
  }
};

} // namespace

// Falsifier: a colony whose clock would quantize to zero accepted as a
// station that never ages, instead of the configuration being refused.
TEST(ColonyOutcome, StationBelowTheClockFloorIsRefused) {
  const StoppedClockField field;
  game::CampaignConfig config = campaign_test::fakeConfig();
  game::ColonyConfig colony;
  colony.bandIndex = 0; // radius 960, rate 1e-16
  config.colonies = {colony};
  EXPECT_FALSE(game::CampaignState(config, field).valid());
  config.colonies.front().bandIndex = 1;
  EXPECT_TRUE(game::CampaignState(config, field).valid());
}

// Falsifier: the host's energy stamped on a notice differing from what the
// host had banked when it sent it (reports from turns 1..15 landed by turn
// 20), or the colony learning it before the notice's five-turn flight ends.
TEST(ColonyOutcome, HostEnergyReachesTheColonyOnlyAsStampedAtEmission) {
  const campaign_test::FakeTimeField field;
  game::CampaignState state(
      colonyConfig(R"({"events": [{"id": 1, "triggers": [{"turn_at_least": 20}],
                        "effects": [{"emit": {"kind": "notice", "to": "colony"}}]}]})",
                   0),
      field);
  ASSERT_TRUE(state.valid());
  state.advanceTurns(24);
  EXPECT_TRUE(state.arrivals().empty());
  state.advanceTurns(1);
  ASSERT_EQ(state.arrivals().size(), 1U);
  EXPECT_EQ(state.arrivals().front().emitTurn, 20);
  EXPECT_DOUBLE_EQ(state.arrivals().front().senderEnergyUnitsAtEmit, 15.0);
  EXPECT_DOUBLE_EQ(state.energyUnits(), 20.0);
}

// Falsifier: a colony whose production rate is infinite, NaN, or negative
// accepted (its first report would carry a non-finite or negative yield, and
// the config would fail the finite-value serialization contract).
TEST(ColonyOutcome, NonFiniteOrNegativeProductionIsRefused) {
  const campaign_test::FakeTimeField field;
  for (const double rate : {std::numeric_limits<double>::infinity(),
                            std::numeric_limits<double>::quiet_NaN(), -1.0}) {
    game::CampaignConfig config = colonyConfig(R"({})", 0);
    config.colonies.front().energyPerTick = rate;
    EXPECT_FALSE(game::CampaignState(config, field).valid()) << rate;
  }
  game::CampaignConfig config = colonyConfig(R"({})", 0);
  config.colonies.front().energyPerTick = 0.0;
  EXPECT_TRUE(game::CampaignState(config, field).valid());
}

// Falsifier: tech-point accumulation wrapping past the int64 range instead of
// saturating at it.
TEST(ColonyOutcome, TechPointsSaturate) {
  constexpr std::int64_t kMax = std::numeric_limits<std::int64_t>::max();
  constexpr std::int64_t kMin = std::numeric_limits<std::int64_t>::min();
  EXPECT_EQ(game::saturatingAdd(kMax - 5, game::K_STORY_INT_LIMIT), kMax);
  EXPECT_EQ(game::saturatingAdd(kMin + 5, -game::K_STORY_INT_LIMIT), kMin);
  EXPECT_EQ(game::saturatingAdd(40, 2), 42);
}

// Falsifier: a finite but enormous production rate accepted (DBL_MAX makes
// the first multi-tick report or the second accumulated one overflow to inf),
// or the documented maximum refused.
TEST(ColonyOutcome, ProductionRateIsBounded) {
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config = colonyConfig(R"({})", 0);
  config.colonies.front().energyPerTick = std::numeric_limits<double>::max();
  EXPECT_FALSE(game::CampaignState(config, field).valid());
  config.colonies.front().energyPerTick = game::K_MAX_ENERGY_PER_TICK * 2.0;
  EXPECT_FALSE(game::CampaignState(config, field).valid());
  config.colonies.front().energyPerTick = game::K_MAX_ENERGY_PER_TICK;
  game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  state.advanceTurns(50);
  EXPECT_TRUE(std::isfinite(state.energyUnits()));
  EXPECT_FALSE(state.serializeState().empty());
}

// Falsifier: a live colony's order refused because the host has latched a
// victory the colony has not heard of -- the refusal would reveal the remote
// outcome -- while the host, which knows it, is refused as before.
TEST(ColonyOutcome, HostDecisionDoesNotSilenceTheColony) {
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config = colonyConfig(R"({})", 0);
  config.victoryEnergyUnits = 3.0; // the colony's reports from turns 1..3 land at 6..8
  game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  const game::FleetId fleet = state.addFleet(game::FleetCapability::Research, 1);
  ASSERT_NE(fleet, game::K_INVALID_FLEET_ID);
  state.advanceTurns(10);
  ASSERT_EQ(state.status(), game::CampaignStatus::Won);
  EXPECT_EQ(state.perceivedSnapshot(game::K_FIRST_COLONY_NODE).status,
            game::CampaignStatus::Ongoing);

  game::Command order;
  order.type = game::CommandType::AssignTask;
  order.fleet = fleet;
  order.properTimeCostSec = 3600.0;
  order.originNode = game::K_AUTHORITY_NODE;
  EXPECT_FALSE(state.issueCommand(order));
  order.originNode = game::K_FIRST_COLONY_NODE;
  EXPECT_TRUE(state.issueCommand(order));
}

// Falsifier: the colony's band delays reflecting where relay fleets truly are
// -- relay positions are fleet telemetry the colony lacks -- instead of the
// a-priori delay (geodesic times the configured overhead). The fake band 960
// is 40 s from the host; overhead 2 makes 80 s, which a relay on band 995
// cuts to 60 s in the referee view.
TEST(ColonyOutcome, ColonyBandDelaysIgnoreUnseenRelays) {
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config = colonyConfig(R"({})", 0);
  config.signalOverheadFactor = 2.0;
  config.relayDelayFraction = 0.25;
  game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  ASSERT_NE(state.addFleet(game::FleetCapability::Relay, 1), game::K_INVALID_FLEET_ID);
  EXPECT_DOUBLE_EQ(state.renderSnapshot().bands.at(0).delayToAuthoritySec, 60.0);
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  EXPECT_DOUBLE_EQ(colony.bands.at(0).delayToAuthoritySec, 80.0);
  EXPECT_DOUBLE_EQ(colony.bands.at(1).delayToAuthoritySec, 10.0);
}

// Falsifier: a tech victory whose tier every colony holds at zero points left
// Ongoing at construction, so the authority's orders are accepted into a
// campaign that has already met its objective.
TEST(ColonyOutcome, VictoryMetAtSetupIsLatchedAtConstruction) {
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config =
      colonyConfig(R"({"tech_tiers": [{"points": 0, "name": "founded"}]})", 0);
  config.victoryTechTier = 1;
  game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  const game::FleetId fleet = state.addFleet(game::FleetCapability::Research, 1);
  EXPECT_EQ(state.status(), game::CampaignStatus::Won);
  EXPECT_EQ(state.clearedTurn(), 0);
  game::Command order;
  order.type = game::CommandType::AssignTask;
  order.fleet = fleet;
  order.properTimeCostSec = 3600.0;
  EXPECT_FALSE(state.issueCommand(order));
}

// Falsifier: a colony or authority station configured with an observer value
// outside the enum building a valid campaign (a field may read any unknown
// value as some orbit, and the invalid byte would be serialized).
TEST(ColonyOutcome, OutOfRangeObserverIsRefused) {
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config = colonyConfig(R"({})", 0);
  config.colonies.front().observer = std::bit_cast<game::Observer>(std::uint8_t{9});
  EXPECT_FALSE(game::CampaignState(config, field).valid());
  config = colonyConfig(R"({})", 0);
  config.authorityObserver = std::bit_cast<game::Observer>(std::uint8_t{7});
  EXPECT_FALSE(game::CampaignState(config, field).valid());
}

namespace {

/** @brief The fake field with a horizon at 950, counting every delay query
 *         made with a radius that is not a valid station. */
class CountingField final : public game::TimeField {
public:
  [[nodiscard]] double properTimeRate(double radiusCm, game::Observer /*observer*/) const override {
    return radiusCm < 970.0 ? 0.1 : 1.0;
  }
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override {
    if (!isValidStationRadius(fromRadiusCm) || !isValidStationRadius(toRadiusCm)) {
      ++invalidQueries;
    }
    return std::fabs(toRadiusCm - fromRadiusCm);
  }
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override {
    return std::isfinite(radiusCm) && radiusCm > 950.0;
  }
  mutable int invalidQueries = 0;
};

} // namespace

// Falsifier: a colony's view querying a signal delay for a band at or inside
// the horizon -- such bands stay in the config for the map but are no
// station, and a Kerr field asserts on them -- when it estimates the longest
// possible order delay.
TEST(ColonyOutcome, ColonyViewSkipsForbiddenBands) {
  const CountingField field;
  game::CampaignConfig config = colonyConfig(R"({})", 0);
  config.bandRadiusCm = {900.0, 995.0}; // band 0 is inside the horizon
  game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  const game::FleetId fleet = state.addFleet(game::FleetCapability::Research, 1);
  game::Command order;
  order.type = game::CommandType::AssignTask;
  order.fleet = fleet;
  order.properTimeCostSec = 3600.0;
  order.originNode = game::K_FIRST_COLONY_NODE;
  ASSERT_TRUE(state.issueCommand(order));
  field.invalidQueries = 0;
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  EXPECT_EQ(field.invalidQueries, 0);
  EXPECT_EQ(colony.ordersInFlight.size(), 1U);
}

// Falsifier: a fleet's completion report lost at a dark host counted as lost
// colony production -- the colony-production figure must be exactly the
// colony's reports that reached the dark host, with fleet yield tallied apart.
TEST(ColonyOutcome, FleetYieldLostToDarknessIsTalliedApart) {
  const campaign_test::FakeTimeField field;
  game::CampaignState state(
      colonyConfig(R"({"events": [{"id": 1, "triggers": [{"turn_at_least": 8}],
                        "effects": [{"set_flag": "dark"}]}]})",
                   0),
      field);
  ASSERT_TRUE(state.valid());
  // A fleet on band 995 (rate 1, 5 turns from the host) finishes a two-second
  // task at turn 7; its report would land at 12, after the host goes dark.
  const game::FleetId fleet = state.addFleet(game::FleetCapability::Research, 1);
  game::Command order;
  order.type = game::CommandType::AssignTask;
  order.fleet = fleet;
  order.properTimeCostSec = 2.0;
  ASSERT_TRUE(state.issueCommand(order));
  state.advanceTurns(30);
  const game::CampaignViewSnapshot view = state.renderSnapshot();
  EXPECT_DOUBLE_EQ(view.energyLostToDarkness, 30.0 - 5.0 - 3.0);
  EXPECT_GT(view.fleetYieldLostToDarkness, 0.0);
  EXPECT_TRUE(state.intelLog().empty());
}
