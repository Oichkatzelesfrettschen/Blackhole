/**
 * @file campaign_perceived_view_test.cpp
 * @brief Falsification gates for a colony's perceived view, the snapshot the
 *        panels and the strategic map draw at colony focus: nothing of the
 *        host's present, only what has arrived, and fleets only where the
 *        colony last sent them.
 */

#include <gtest/gtest.h>

#include <cstdint>
#include <string>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/station_node.h"

namespace {

constexpr game::FleetId K_SURVEY_FLEET = 1;

game::EventSet shippedStory() {
  const game::EventLoadResult loaded = game::loadEventSetFile(
      std::string(BLACKHOLE_SOURCE_DIR) + "/assets/events/host_goes_dark.json");
  EXPECT_TRUE(loaded.ok()) << loaded.error;
  return loaded.story;
}

/** @brief The host's latest arrival at the colony (by emission turn). */
game::ArrivalRecord latestHostArrival(const game::CampaignState &state) {
  game::ArrivalRecord latest;
  latest.emitTurn = -1;
  for (const game::ArrivalRecord &arrival : state.arrivals()) {
    if (arrival.sender == game::K_AUTHORITY_NODE &&
        arrival.destination == game::K_FIRST_COLONY_NODE && arrival.emitTurn >= latest.emitTurn) {
      latest = arrival;
    }
  }
  return latest;
}

void expectNoTelemetry(const game::FleetView &fleet) {
  EXPECT_FALSE(fleet.telemetryKnown);
  EXPECT_FALSE(fleet.positionKnown);
  EXPECT_DOUBLE_EQ(fleet.properTimeSec, 0.0);
  EXPECT_EQ(fleet.completedTasks, 0U);
}

/** @brief The host keeps its own ledger, intel, and fleet reports, and sees
 *         only arrivals addressed to itself. */
void expectHostLedgerKept(const game::CampaignViewSnapshot &authority,
                          const game::CampaignViewSnapshot &referee) {
  EXPECT_EQ(authority.perceivedBy, game::K_AUTHORITY_NODE);
  EXPECT_DOUBLE_EQ(authority.energyUnits, referee.energyUnits);
  EXPECT_EQ(authority.intel.size(), referee.intel.size());
  EXPECT_TRUE(authority.fleets.front().telemetryKnown);
  for (const game::ArrivalRecord &arrival : authority.arrivals) {
    EXPECT_EQ(arrival.destination, game::K_AUTHORITY_NODE);
  }
}

} // namespace

// Falsifier: the colony's view carrying any host-local truth -- the present
// bank, intel, reports, or an order the host sent -- or a host clock other
// than the stamp on its latest arrival.
TEST(PerceivedView, ColonySeesTheHostOnlyAsLastHeard) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_AUTHORITY_NODE));
  state.advanceTurns(1500);
  // A second task banks more energy after the host's latest packet (turn
  // 1456; the next leaves at 1547), and a third leaves an order in flight.
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_AUTHORITY_NODE));
  state.advanceTurns(20);
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_AUTHORITY_NODE));

  const game::CampaignViewSnapshot referee = state.renderSnapshot();
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  ASSERT_FALSE(referee.intel.empty());
  ASSERT_FALSE(referee.ordersInFlight.empty());
  EXPECT_EQ(colony.perceivedBy, game::K_FIRST_COLONY_NODE);
  EXPECT_TRUE(colony.intel.empty());
  EXPECT_TRUE(colony.reportsInFlight.empty());
  EXPECT_TRUE(colony.ordersInFlight.empty()); // the only order in flight is the host's

  // The host's bank as stamped on its latest arrival, not as it stands.
  const game::ArrivalRecord latest = latestHostArrival(state);
  ASSERT_GE(latest.emitTurn, 0);
  EXPECT_DOUBLE_EQ(colony.energyUnits, latest.senderEnergyUnitsAtEmit);
  EXPECT_GT(referee.energyUnits, colony.energyUnits);
  const game::NodeView &host = colony.nodes.at(game::K_AUTHORITY_NODE);
  EXPECT_TRUE(host.heard);
  EXPECT_EQ(host.asOfTurn, latest.emitTurn);
  EXPECT_DOUBLE_EQ(host.properTimeSec, static_cast<double>(latest.senderProperSecAtEmit));
  EXPECT_EQ(colony.nodes.at(game::K_FIRST_COLONY_NODE).asOfTurn, state.turn());

}

// Falsifier: an arrival addressed elsewhere in the colony's view, any fleet
// telemetry there, or the host losing its own ledger or seeing arrivals
// addressed elsewhere.
TEST(PerceivedView, ColonyViewHoldsOnlyItsArrivalsAndNoTelemetry) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_AUTHORITY_NODE));
  state.advanceTurns(1500);
  const game::CampaignViewSnapshot referee = state.renderSnapshot();
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  ASSERT_FALSE(colony.arrivals.empty());
  for (const game::ArrivalRecord &arrival : colony.arrivals) {
    EXPECT_EQ(arrival.destination, game::K_FIRST_COLONY_NODE);
  }
  ASSERT_FALSE(colony.fleets.empty());
  expectNoTelemetry(colony.fleets.front());
  expectHostLedgerKept(state.perceivedSnapshot(game::K_AUTHORITY_NODE), referee);
}

// Falsifier: a fleet placed before the colony's order could reach it, placed
// anywhere but the ordered band once it could, or the colony's own order in
// flight hidden from it.
TEST(PerceivedView, ColonyPlacesFleetsWhereItLastSentThem) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  state.advanceTurns(5);
  ASSERT_TRUE(session.issuePlaceFleet(K_SURVEY_FLEET, game::K_MILLER_BAND,
                                      game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                      game::K_FIRST_COLONY_NODE));
  const std::int64_t effectTurn = state.commandLog().back().effectTurn;
  ASSERT_GT(effectTurn, 6);

  state.advanceTurns(1);
  game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  ASSERT_EQ(colony.ordersInFlight.size(), 1U);
  EXPECT_EQ(colony.ordersInFlight.front().origin, game::K_FIRST_COLONY_NODE);
  EXPECT_FALSE(colony.fleets.front().positionKnown);

  state.advanceTurns(effectTurn - state.turn());
  colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  EXPECT_TRUE(colony.fleets.front().positionKnown);
  EXPECT_EQ(colony.fleets.front().bandIndex, game::K_MILLER_BAND);
  EXPECT_FALSE(colony.fleets.front().telemetryKnown);
}

// Falsifier: the colony's view reporting the host dark -- the colony can only
// infer silence from missing packets, which the story does -- or showing a
// host clock newer than the last packet sent before the dark turn.
TEST(PerceivedView, HostDarknessIsNeverObservedDirectly) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  const std::int64_t darkTurn = state.storyParam("dark_turn").value_or(0);
  ASSERT_GT(darkTurn, 0);
  state.advanceTurns(darkTurn + 1000);
  ASSERT_TRUE(state.nodes().at(game::K_AUTHORITY_NODE).dark());
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  const game::NodeView &host = colony.nodes.at(game::K_AUTHORITY_NODE);
  EXPECT_FALSE(host.dark);
  EXPECT_TRUE(host.heard);
  EXPECT_LT(host.asOfTurn, darkTurn);
}

// Falsifier: the host seeing the colony's present -- any clock, tech, or tier
// newer than what the colony's latest landed production report stamped -- or
// knowing anything of the colony before a report has arrived. On Miller's
// orbit the first local hour (the first report) leaves near turn 2559 and
// lands a signal delay later, while packets keep raising the colony's tier.
TEST(PerceivedView, HostSeesTheColonyOnlyAsReported) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  const std::int64_t delay = state.nodeDelayTurns(game::K_FIRST_COLONY_NODE, game::K_AUTHORITY_NODE);

  state.advanceTurns(1000);
  game::CampaignViewSnapshot host = state.perceivedSnapshot(game::K_AUTHORITY_NODE);
  EXPECT_GE(state.colonyTechTier(), 1);
  EXPECT_FALSE(host.nodes.at(game::K_FIRST_COLONY_NODE).heard);
  EXPECT_EQ(host.colonyTechTier, 0);

  state.advanceTurns(3000);
  host = state.perceivedSnapshot(game::K_AUTHORITY_NODE);
  const game::NodeView &colony = host.nodes.at(game::K_FIRST_COLONY_NODE);
  const game::StationNode &truth = state.nodes().at(game::K_FIRST_COLONY_NODE);
  ASSERT_TRUE(colony.heard);
  EXPECT_LE(colony.asOfTurn + delay, state.turn());
  EXPECT_LT(colony.techPoints, truth.techPoints);
  EXPECT_LT(host.colonyTechTier, state.colonyTechTier());
  EXPECT_EQ(host.colonyTechTier, colony.techTier);
  EXPECT_LT(colony.properTimeSec, truth.clock.properSecApprox());
  EXPECT_FALSE(colony.dark);
  // The referee view still carries the truth, for tests and debugging only.
  EXPECT_EQ(state.renderSnapshot().colonyTechTier, state.colonyTechTier());
}
