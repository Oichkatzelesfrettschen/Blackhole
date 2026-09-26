/**
 * @file campaign_causality_test.cpp
 * @brief Seed-swept causality gates for the host-goes-dark story on
 *        Gargantua: every signal lands exactly one quantized light delay after
 *        emission, the colony infers the silence no earlier than the first
 *        missing packet could have arrived, and auto-pause stops the clock on
 *        the arrival turn itself.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <optional>
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
#include "game/station_node.h"

namespace {

constexpr std::uint32_t K_EVENT_HOST_SILENT = 10;
constexpr std::uint32_t K_EVENT_PRESUMED_DARK = 11;
constexpr std::int64_t K_SILENCE_MARGIN = 30; ///< The story's "plus" on the silence thresholds.
constexpr int K_MILLER_BAND = 0;
constexpr std::uint64_t K_SEEDS = 12;

game::EventSet shippedStory() {
  const game::EventLoadResult loaded =
      game::loadEventSetFile(std::string(BLACKHOLE_SOURCE_DIR) + "/assets/events/host_goes_dark.json");
  EXPECT_TRUE(loaded.ok()) << loaded.error;
  return loaded.story;
}

std::optional<std::int64_t> noticeArrival(const game::CampaignState &state, std::uint32_t event) {
  const auto found =
      std::ranges::find_if(state.arrivals(), [event](const game::ArrivalRecord &arrival) {
        return arrival.kind == game::EmitKind::Notice && arrival.payloadIndex == event;
      });
  if (found == state.arrivals().end()) {
    return std::nullopt;
  }
  return found->arrivalTurn;
}

std::int64_t param(const game::CampaignState &state, const char *name) {
  const std::optional<std::int64_t> value = state.storyParam(name);
  EXPECT_TRUE(value.has_value()) << name;
  return value.value_or(0);
}

/** @brief Turns until every consequence of the dark turn has reached the
 *         colony: the last packet's flight plus four cadences. */
std::int64_t storyHorizon(const game::CampaignState &state) {
  return param(state, "dark_turn") + state.nodeDelayTurns(0, 1) +
         (4 * param(state, "packet_period")) + K_SILENCE_MARGIN;
}

/** @brief Latest emission and latest arrival of the host's tech packets;
 *         also checks none left on or after the dark turn. */
struct PacketStream {
  std::int64_t lastEmit = -1;
  std::int64_t lastArrival = -1;
};

PacketStream packetStream(const game::CampaignState &state, std::int64_t darkTurn) {
  PacketStream stream;
  for (const game::ArrivalRecord &arrival : state.arrivals()) {
    if (arrival.kind == game::EmitKind::TechPacket) {
      EXPECT_LT(arrival.emitTurn, darkTurn);
      stream.lastEmit = std::max(stream.lastEmit, arrival.emitTurn);
      stream.lastArrival = std::max(stream.lastArrival, arrival.arrivalTurn);
    }
  }
  return stream;
}

} // namespace

// Falsifier: any node signal arriving on a turn other than emit + ceil(delay /
// secondsPerTurn), or earlier than the geodesic light delay between the two
// stations allows.
TEST(CampaignCausality, EverySignalLandsOneQuantizedLightDelayAfterEmission) {
  const game::EventSet story = shippedStory();
  for (std::uint64_t seed = 1; seed <= K_SEEDS; ++seed) {
    game::CampaignSession session(seed, story, K_MILLER_BAND);
    game::CampaignState &state = session.state();
    ASSERT_TRUE(state.valid());
    state.advanceTurns(storyHorizon(state));
    ASSERT_FALSE(state.arrivals().empty());
    const double secondsPerTurn = state.config().secondsPerTurn;
    for (const game::ArrivalRecord &arrival : state.arrivals()) {
      const double fromCm = state.nodes().at(arrival.sender).radiusCm;
      const double toCm = state.nodes().at(arrival.destination).radiusCm;
      const double lightSec = fromCm == toCm ? 0.0 : session.field().signalDelaySec(fromCm, toCm);
      const auto lightTurns = static_cast<std::int64_t>(std::ceil(lightSec / secondsPerTurn));
      ASSERT_EQ(arrival.arrivalTurn,
                arrival.emitTurn + state.nodeDelayTurns(arrival.sender, arrival.destination))
          << "seed " << seed;
      ASSERT_GE(arrival.arrivalTurn, arrival.emitTurn + lightTurns) << "seed " << seed;
    }
  }
}

// Falsifier: an order sent from the colony taking effect before the light
// delay from the colony's radius to the fleet's band.
TEST(CampaignCausality, ColonyOrdersRideTheColonyToFleetDelay) {
  game::CampaignSession session(3, shippedStory(), K_MILLER_BAND);
  game::CampaignState &state = session.state();
  state.advanceTurns(10);
  ASSERT_TRUE(session.issueAssignTask(1, 1.0, game::K_FIRST_COLONY_NODE));
  const game::LoggedCommand &logged = state.commandLog().back();
  const double colonyCm = state.nodes().at(game::K_FIRST_COLONY_NODE).radiusCm;
  const double fleetCm = state.config().bandRadiusCm.at(1);
  const double delaySec = session.field().signalDelaySec(colonyCm, fleetCm);
  EXPECT_EQ(logged.issueTurn, 10);
  EXPECT_EQ(logged.effectTurn,
            10 + static_cast<std::int64_t>(std::ceil(delaySec / state.config().secondsPerTurn)));
  EXPECT_EQ(logged.command.originNode, game::K_FIRST_COLONY_NODE);
  // An unknown origin is refused.
  game::Command bogus = logged.command;
  bogus.originNode = 7;
  EXPECT_FALSE(state.issueCommand(bogus));
}

// Falsifier: a packet emitted on or after the dark turn; the colony's silence
// inference landing before the first missing packet could have arrived (its
// scheduled emission, never earlier than the dark turn, plus the light
// delay, plus the story's margin), on any other turn than exactly that, or
// the presumed-dark inference off lastArrival + 3K + margin.
TEST(CampaignCausality, SilenceIsInferredOnlyFromMissingArrivals) {
  const game::EventSet story = shippedStory();
  for (std::uint64_t seed = 1; seed <= K_SEEDS; ++seed) {
    game::CampaignSession session(seed, story, K_MILLER_BAND);
    game::CampaignState &state = session.state();
    const std::int64_t darkTurn = param(state, "dark_turn");
    const std::int64_t period = param(state, "packet_period");
    const std::int64_t delay = state.nodeDelayTurns(0, 1);
    state.advanceTurns(storyHorizon(state));

    const PacketStream stream = packetStream(state, darkTurn);
    ASSERT_GE(stream.lastEmit, 1);
    const std::int64_t firstMissedEmit = stream.lastEmit + period;
    ASSERT_GE(firstMissedEmit, darkTurn);

    const std::int64_t silent = noticeArrival(state, K_EVENT_HOST_SILENT).value_or(-1);
    const std::int64_t presumed = noticeArrival(state, K_EVENT_PRESUMED_DARK).value_or(-1);
    EXPECT_EQ(silent, firstMissedEmit + delay + K_SILENCE_MARGIN) << "seed " << seed;
    EXPECT_GE(silent, darkTurn + delay + K_SILENCE_MARGIN) << "seed " << seed;
    EXPECT_EQ(presumed, stream.lastArrival + (3 * period) + K_SILENCE_MARGIN) << "seed " << seed;
    EXPECT_GT(presumed, silent);
  }
}

// Falsifier: the real-time driver at Miller focus stopping on any turn but
// the silence notice's arrival, or, resumed, on any turn but the presumed-dark
// notice's -- the tech packets and the opening notice (category tech) never
// pause.
TEST(CampaignCausality, AutoPauseStopsExactlyOnTheArrivalTurn) {
  const game::EventSet story = shippedStory();
  for (std::uint64_t seed = 1; seed <= 4; ++seed) {
    game::CampaignSession reference(seed, story, K_MILLER_BAND);
    reference.state().advanceTurns(storyHorizon(reference.state()));
    const std::int64_t silentTurn =
        noticeArrival(reference.state(), K_EVENT_HOST_SILENT).value_or(-1);
    const std::int64_t presumedTurn =
        noticeArrival(reference.state(), K_EVENT_PRESUMED_DARK).value_or(-1);
    ASSERT_GT(silentTurn, 0);
    ASSERT_GT(presumedTurn, silentTurn);

    game::CampaignSession session(seed, story, K_MILLER_BAND);
    game::CampaignState &state = session.state();
    game::Inbox inbox(game::K_FIRST_COLONY_NODE);
    game::RealtimeDriverConfig config;
    config.maxTurnsPerFrame = 5000;
    game::RealtimeDriver driver(config);
    driver.setFocusRate(state.nodes().at(game::K_FIRST_COLONY_NODE).clock.rate());
    const game::RealtimeDriver::StepFunction step = [&]() {
      state.advanceTurn();
      return inbox.sync(state.arrivals());
    };
    std::vector<std::int64_t> pauseTurns;
    while (state.turn() < presumedTurn + 10 && pauseTurns.size() < 2) {
      if (driver.pump(3000.0, step).pausedByArrival) {
        pauseTurns.push_back(state.turn());
        driver.setPaused(false);
      }
    }
    ASSERT_EQ(pauseTurns.size(), 2U) << "seed " << seed;
    EXPECT_EQ(pauseTurns.at(0), silentTurn) << "seed " << seed;
    EXPECT_EQ(pauseTurns.at(1), presumedTurn) << "seed " << seed;
    // Pausing changed nothing: caught up to the reference, the states agree.
    ASSERT_LE(state.turn(), reference.state().turn());
    state.advanceTurns(reference.state().turn() - state.turn());
    EXPECT_EQ(state.stateDigest(), reference.state().stateDigest()) << "seed " << seed;
  }
}

// Falsifier: an order whose origin shares the fleet's radius logged for a turn
// other than the one it acts in. Sent between turns, it can act no earlier
// than the next turn; the log must say so.
TEST(CampaignCausality, ZeroDelayOrdersActOnTheirLoggedTurn) {
  game::CampaignSession session(3, shippedStory(), K_MILLER_BAND);
  game::CampaignState &state = session.state();
  // The colony brings the survey fleet down to Miller's orbit.
  ASSERT_TRUE(session.issuePlaceFleet(1, K_MILLER_BAND, game::OrbitLane::Prograde,
                                      game::StationKeeping::Orbit, game::K_FIRST_COLONY_NODE));
  state.advanceTurns(state.commandLog().back().effectTurn);
  ASSERT_EQ(state.fleets().front().bandIndex, K_MILLER_BAND);

  // Colony and fleet now share a radius: zero light delay.
  ASSERT_TRUE(session.issueAssignTask(1, 1.0, game::K_FIRST_COLONY_NODE));
  const game::LoggedCommand logged = state.commandLog().back();
  EXPECT_EQ(logged.effectTurn, logged.issueTurn + 1);
  const std::size_t tasksBefore = state.fleets().front().assignedTasks.size();
  state.advanceTurn();
  EXPECT_EQ(state.turn(), logged.effectTurn);
  EXPECT_EQ(state.fleets().front().assignedTasks.size(), tasksBefore + 1);
}

// Falsifier: a colony's redeployment refused at issue on the fleet's true
// fuel (telemetry the colony lacks), or, once sent, fizzling without a reply
// that lands at the effect turn plus the fleet-to-colony light delay.
TEST(CampaignCausality, ColonyRedeploymentFizzlesAtEffectWithANotice) {
  game::CampaignSession session(3, shippedStory(), K_MILLER_BAND);
  game::CampaignState &state = session.state();
  // The host spends the survey fleet's 100 fuel on five 20-fuel hops, leaving
  // it on Miller's band (index 0) with none.
  for (int hop = 0; hop < 5; ++hop) {
    ASSERT_TRUE(session.issuePlaceFleet(1, hop % 2 == 0 ? K_MILLER_BAND : 1,
                                        game::OrbitLane::Prograde, game::StationKeeping::Orbit,
                                        game::K_AUTHORITY_NODE));
    state.advanceTurns(state.commandLog().back().effectTurn - state.turn());
  }
  ASSERT_EQ(state.fleets().front().bandIndex, K_MILLER_BAND);
  ASSERT_DOUBLE_EQ(state.fleets().front().fuelUnits, 0.0);
  // The host, which sees the empty tank, is refused at issue.
  EXPECT_FALSE(session.issuePlaceFleet(1, 1, game::OrbitLane::Prograde,
                                       game::StationKeeping::Orbit, game::K_AUTHORITY_NODE));

  // The colony cannot see it: its order is sent, and fizzles on arrival.
  ASSERT_TRUE(session.issuePlaceFleet(1, 1, game::OrbitLane::Prograde,
                                      game::StationKeeping::Orbit, game::K_FIRST_COLONY_NODE));
  const std::int64_t effectTurn = state.commandLog().back().effectTurn;
  state.advanceTurns(effectTurn - state.turn());
  EXPECT_EQ(state.fleets().front().bandIndex, K_MILLER_BAND);
  // Fleet and colony share Miller's radius, so the reply lands that turn.
  const auto fizzle = std::ranges::find_if(state.arrivals(), [](const game::ArrivalRecord &arrival) {
    return arrival.sender == game::K_NO_NODE;
  });
  ASSERT_NE(fizzle, state.arrivals().end());
  EXPECT_EQ(fizzle->destination, game::K_FIRST_COLONY_NODE);
  EXPECT_EQ(fizzle->fleet, 1U);
  EXPECT_EQ(fizzle->emitTurn, effectTurn);
  EXPECT_EQ(fizzle->arrivalTurn, effectTurn);
}
