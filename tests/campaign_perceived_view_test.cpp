/**
 * @file campaign_perceived_view_test.cpp
 * @brief Falsification gates for a colony's perceived view, the snapshot the
 *        panels and the strategic map draw at colony focus: nothing of the
 *        host's present, only what has arrived, and fleets only where the
 *        colony last sent them.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <numeric>
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
  game::ArrivalRecord none;
  none.emitTurn = -1;
  return std::accumulate(state.arrivals().begin(), state.arrivals().end(), none,
                         [](const game::ArrivalRecord &latest, const game::ArrivalRecord &arrival) {
                           const bool fromHost = arrival.sender == game::K_AUTHORITY_NODE &&
                                                 arrival.destination == game::K_FIRST_COLONY_NODE;
                           return fromHost && arrival.emitTurn >= latest.emitTurn ? arrival
                                                                                  : latest;
                         });
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

// Falsifier: the host's view listing an order the colony sent, which the
// host has no way to have learned.
TEST(PerceivedView, HostDoesNotSeeColonyOrdersInFlight) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_FIRST_COLONY_NODE));
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_AUTHORITY_NODE));
  state.advanceTurn();
  ASSERT_EQ(state.renderSnapshot().ordersInFlight.size(), 2U);
  const game::CampaignViewSnapshot host = state.perceivedSnapshot(game::K_AUTHORITY_NODE);
  ASSERT_EQ(host.ordersInFlight.size(), 1U);
  EXPECT_EQ(host.ordersInFlight.front().origin, game::K_AUTHORITY_NODE);
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  ASSERT_EQ(colony.ordersInFlight.size(), 1U);
  EXPECT_EQ(colony.ordersInFlight.front().origin, game::K_FIRST_COLONY_NODE);
}

namespace {

/** @brief The colony's view of its own in-flight order at `logIndex`. */
game::OrderInFlightView colonyOrder(const game::CampaignState &state, std::size_t logIndex) {
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  const auto found = std::ranges::find(colony.ordersInFlight, logIndex,
                                       &game::OrderInFlightView::logIndex);
  if (found == colony.ordersInFlight.end()) {
    ADD_FAILURE() << "order " << logIndex << " not in the colony's view";
    return {};
  }
  return *found;
}

} // namespace

// Falsifier: the colony's in-flight order carrying the engine's true effect
// turn -- which encodes the fleet's true band -- instead of the colony's own
// estimate: "unknown" before the colony has ever placed the fleet, equal to
// the truth while its belief is current, and different once the host has
// moved the fleet without the colony knowing.
TEST(PerceivedView, ColonyEstimatesItsOrdersFromItsOwnBelief) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();

  // Never placed: the colony cannot estimate.
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_FIRST_COLONY_NODE));
  EXPECT_FALSE(colonyOrder(state, state.commandLog().size() - 1).effectTurnKnown);

  // The colony brings the fleet to Miller's band and waits out the longest
  // possible delay; its belief is now current.
  ASSERT_TRUE(session.issuePlaceFleet(K_SURVEY_FLEET, game::K_MILLER_BAND,
                                      game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                      game::K_FIRST_COLONY_NODE));
  state.advanceTurns(400);
  ASSERT_EQ(state.fleets().front().bandIndex, game::K_MILLER_BAND);
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_FIRST_COLONY_NODE));
  const game::LoggedCommand current = state.commandLog().back();
  const game::OrderInFlightView currentView = colonyOrder(state, state.commandLog().size() - 1);
  ASSERT_TRUE(currentView.effectTurnKnown);
  EXPECT_EQ(currentView.effectTurn, current.effectTurn);

  // The host moves the fleet back out; the colony is not told.
  ASSERT_TRUE(session.issuePlaceFleet(K_SURVEY_FLEET, game::K_SURVEY_BAND,
                                      game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                      game::K_AUTHORITY_NODE));
  state.advanceTurns(state.commandLog().back().effectTurn - state.turn());
  ASSERT_EQ(state.fleets().front().bandIndex, game::K_SURVEY_BAND);
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_FIRST_COLONY_NODE));
  const game::LoggedCommand stale = state.commandLog().back();
  const game::OrderInFlightView staleView = colonyOrder(state, state.commandLog().size() - 1);
  ASSERT_TRUE(staleView.effectTurnKnown);
  EXPECT_EQ(staleView.effectTurn, stale.issueTurn + 1); // it believes: same radius as Miller
  EXPECT_GT(stale.effectTurn, staleView.effectTurn);    // truth: the fleet is 100M out
  // The colony still places the fleet where it last sent it.
  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  EXPECT_EQ(colony.fleets.front().bandIndex, game::K_MILLER_BAND);
}

// Falsifier: the colony still placing a fleet at the band of a redeployment
// the fleet has told it fizzled (not enough fuel on arrival).
TEST(PerceivedView, FizzledPlacementLeavesTheColonysBelief) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  // The host spends all 100 fuel on five hops, leaving the fleet on Miller's
  // band with none.
  for (int hop = 0; hop < 5; ++hop) {
    ASSERT_TRUE(session.issuePlaceFleet(K_SURVEY_FLEET,
                                        hop % 2 == 0 ? game::K_MILLER_BAND : game::K_SURVEY_BAND,
                                        game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                        game::K_AUTHORITY_NODE));
    state.advanceTurns(state.commandLog().back().effectTurn - state.turn());
  }
  ASSERT_DOUBLE_EQ(state.fleets().front().fuelUnits, 0.0);

  // The colony orders the fleet out; it fizzles, and the reply comes back.
  ASSERT_TRUE(session.issuePlaceFleet(K_SURVEY_FLEET, game::K_SURVEY_BAND,
                                      game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                      game::K_FIRST_COLONY_NODE));
  state.advanceTurns(400); // past every delay the colony could wait out
  ASSERT_EQ(state.fleets().front().bandIndex, game::K_MILLER_BAND);
  const auto fizzle = std::ranges::find_if(state.arrivals(), [](const game::ArrivalRecord &arrival) {
    return arrival.sender == game::K_NO_NODE;
  });
  ASSERT_NE(fizzle, state.arrivals().end());
  EXPECT_EQ(fizzle->payloadIndex, state.commandLog().size() - 1);

  const game::CampaignViewSnapshot colony = state.perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  EXPECT_FALSE(colony.fleets.front().positionKnown);
}

// Falsifier: a colony order leaving the colony's list of orders in flight on
// the engine's true landing turn rather than the colony's own estimate --
// the disappearance would reveal where the fleet truly is.
TEST(PerceivedView, ColonyOrderStaysListedUntilItsOwnEstimate) {
  game::CampaignSession session(3, shippedStory(), game::K_MILLER_BAND);
  game::CampaignState &state = session.state();
  // The colony sends the fleet to the survey band (where it already is) and
  // waits out every possible delay: it believes the fleet is 100M out.
  ASSERT_TRUE(session.issuePlaceFleet(K_SURVEY_FLEET, game::K_SURVEY_BAND,
                                      game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                      game::K_FIRST_COLONY_NODE));
  state.advanceTurns(400);
  // Unseen by the colony, the host brings the fleet down to Miller's band.
  ASSERT_TRUE(session.issuePlaceFleet(K_SURVEY_FLEET, game::K_MILLER_BAND,
                                      game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                      game::K_AUTHORITY_NODE));
  state.advanceTurns(state.commandLog().back().effectTurn - state.turn());
  ASSERT_EQ(state.fleets().front().bandIndex, game::K_MILLER_BAND);

  // A colony task now truly lands next turn (same radius), but the colony
  // expects it some 300 turns out.
  ASSERT_TRUE(session.issueAssignTask(K_SURVEY_FLEET, 1.0, game::K_FIRST_COLONY_NODE));
  const game::LoggedCommand logged = state.commandLog().back();
  ASSERT_EQ(logged.effectTurn, logged.issueTurn + 1);
  state.advanceTurns(2);
  const game::OrderInFlightView view = colonyOrder(state, state.commandLog().size() - 1);
  ASSERT_TRUE(view.effectTurnKnown);
  EXPECT_GT(view.effectTurn, state.turn());
}
