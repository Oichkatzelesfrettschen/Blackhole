/**
 * @file constellation_test.cpp
 * @brief Determinism, causal delay, delayed intel, control denial, and the
 *        non-dominance invariant of the multi-system constellation.
 *
 * The determinism checks exercise two factions across two systems with the AI
 * active, the case a single-faction, single-system run cannot catch: a stray
 * unordered iteration would only diverge here. The balance check pins the shape
 * the harness prints -- a concentrated line loses to the rival's domination clock
 * while a fortress line denies the rival and wins -- so a retune that breaks the
 * forced-contest design fails here instead of silently drifting.
 */

#include <gtest/gtest.h>

#include <cmath>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "game/campaign_view.h"
#include "game/constellation.h"
#include "game/constellation_session.h"
#include "game/constellation_sim_lines.h"
#include "game/constellation_types.h"
#include "game/constellation_view.h"
#include "game/fleet.h"
#include "game/kerr_time_field.h"
#include "game/observer.h"

namespace {

using constellation_sim::PlayerLine;
using constellation_sim::runLine;

constexpr std::uint64_t K_SEED = 42;
constexpr double K_SOLAR_MASS_G = 1.989e33;

game::SystemSpec microSystem() {
  const game::KerrTimeField field(1.0e6 * K_SOLAR_MASS_G, 0.0);
  const double rS = field.schwarzschildRadiusCm();
  return game::SystemSpec{.blackHoleMassG = 1.0e6 * K_SOLAR_MASS_G,
                          .spinDimensionless = 0.0,
                          .authorityRadiusCm = 200.0 * rS,
                          .bandRadiusCm = {3.0 * rS, 10.0 * rS}};
}

// A minimal single-system config for the micro control-denial test.
game::ConstellationConfig microConfig() {
  game::ConstellationConfig config;
  config.secondsPerTurn = 86400.0;
  config.systems = {microSystem()};
  config.controlPointsPerBandPerTurn = 1.0;
  return config;
}

// Two linked systems, no AI, so a controlled placement's control state is stable
// and the delayed-intel lag can be measured against a fixed truth. The 30
// light-day link makes the interstellar observation delay about 30 turns.
game::ConstellationConfig microTwoSystemConfig() {
  game::ConstellationConfig config;
  config.secondsPerTurn = 86400.0;
  config.systems = {microSystem(), microSystem()};
  const double separationCm = 30.0 * 86400.0 * 2.99792458e10;
  config.links = {game::InterSystemLink{.a = 0, .b = 1, .separationCm = separationCm}};
  config.controlPointsPerBandPerTurn = 1.0;
  return config;
}

} // namespace

// Two runs of the same scenario -- two factions, two systems, AI stepping every
// turn -- serialize to an identical digest. A non-canonical iteration anywhere in
// the multi-faction state would break this and nothing else.
TEST(Constellation, DeterministicAcrossFactionsAndSystems) {
  EXPECT_EQ(runLine(K_SEED, 400, PlayerLine::Contest).digest,
            runLine(K_SEED, 400, PlayerLine::Contest).digest);
  EXPECT_EQ(runLine(K_SEED, 400, PlayerLine::Outer).digest,
            runLine(K_SEED, 400, PlayerLine::Outer).digest);
}

// Advancing turn by turn is the only mode; a longer run reaching a decision keeps
// the same digest as an identical replay -- op-order invariance across a decided
// campaign.
TEST(Constellation, DecidedRunIsReproducible) {
  const auto first = runLine(K_SEED, 1400, PlayerLine::Contest);
  const auto second = runLine(K_SEED, 1400, PlayerLine::Contest);
  EXPECT_EQ(first.digest, second.digest);
  EXPECT_EQ(first.turn, second.turn);
  EXPECT_EQ(first.winner, second.winner);
}

// A fleet ordered to the other system enters interstellar transit for many turns
// -- the flat light-crossing time at half c -- holding no band until it arrives.
TEST(Constellation, InterstellarTravelTakesManyTurns) {
  game::ConstellationSession session(K_SEED);
  const game::FactionId player = session.player();
  const game::FleetId fleet = session.constellation().fleets().front().id;
  ASSERT_EQ(session.constellation().fleets().front().faction, player);

  // Send it from system 0 to system 1, band 1.
  ASSERT_TRUE(session.movePlayerFleet(fleet, 1, 1));
  // The order itself is delayed to the fleet; advance until it has departed.
  bool everInTransit = false;
  for (int turn = 0; turn < 200; ++turn) {
    session.constellation().advanceTurn();
    for (const game::ConstellationFleet &current : session.constellation().fleets()) {
      if (current.id == fleet && current.inTransit) {
        everInTransit = true;
      }
    }
  }
  EXPECT_TRUE(everInTransit); // a 40 light-day hop at 0.5c is ~80 turns of transit
}

// A faction one system away does not learn who holds a remote band until the
// light between the two authorities arrives. With the truth held fixed -- alpha
// holds system 0 band 0, no AI to disturb it -- beta's belief is unknown for the
// crossing time and only then catches up.
TEST(Constellation, RemoteIntelLagsThenCatchesUp) {
  game::Constellation constellation(microTwoSystemConfig());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FactionId beta = constellation.addFaction(game::FactionPolicy::Scripted, 1);
  static_cast<void>(beta);
  constellation.addFleet(alpha, 0, game::FleetCapability::Extraction, 0);

  // Beta's home is system 1; index 1 in the faction list. Within the first few
  // turns the interstellar signal has not crossed, so beta believes nothing.
  for (int turn = 0; turn < 5; ++turn) {
    constellation.advanceTurn();
  }
  ASSERT_EQ(constellation.renderSnapshot().systems.at(0).bandController.at(0), alpha);
  EXPECT_EQ(constellation.perceivedController(1, 0, 0), game::K_INVALID_FACTION_ID);

  // After the ~30-turn crossing, beta's belief matches the stable truth.
  for (int turn = 0; turn < 40; ++turn) {
    constellation.advanceTurn();
  }
  EXPECT_EQ(constellation.perceivedController(1, 0, 0), alpha);
}

// Two factions on the same band contest it: neither holds it, so a control point
// that one faction banked alone stops accruing the moment the other arrives.
TEST(Constellation, CoLocationDeniesControl) {
  game::Constellation constellation(microConfig());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FactionId beta = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  constellation.addFleet(alpha, 0, game::FleetCapability::Extraction, 0);

  // Alpha alone on band 0 banks a point per turn.
  constellation.advanceTurn();
  const double soloScore = constellation.factions().front().controlScore;
  EXPECT_GT(soloScore, 0.0);

  // Beta joins band 0: the band is contested, so alpha's score no longer grows.
  constellation.addFleet(beta, 0, game::FleetCapability::Research, 0);
  const double before = constellation.factions().front().controlScore;
  constellation.advanceTurn();
  EXPECT_DOUBLE_EQ(constellation.factions().front().controlScore, before);
  EXPECT_DOUBLE_EQ(constellation.factions().at(1).controlScore, 0.0);
}

// The forced-contest invariant, against the Expansionist rival: a concentrated
// player loses to the rival's domination, a fortress player denies the rival and
// wins. The mechanism assertions -- the rival crosses the control threshold in
// the ignored lines and is held below it in the fortress line -- are structural
// and host-independent; the Won/Lost status is the softer check, kept off the
// deadline cliff by a ~75-turn win margin.
TEST(Constellation, ConcentratedLinesLoseToDominationFortressWins) {
  const double victoryControl =
      game::defaultConstellationConfig(K_SEED).victoryControlScore;

  const auto outer = runLine(K_SEED, 1400, PlayerLine::Outer);
  EXPECT_EQ(outer.overallStatus, game::CampaignStatus::Lost);
  EXPECT_EQ(outer.winner, outer.view.refereeStandings.at(1).id); // the rival won
  EXPECT_GE(outer.view.refereeStandings.at(1).controlScore, victoryControl); // by domination

  const auto allIn = runLine(K_SEED, 1400, PlayerLine::AllIn);
  EXPECT_EQ(allIn.overallStatus, game::CampaignStatus::Lost);
  EXPECT_EQ(allIn.winner, allIn.view.refereeStandings.at(1).id);
  EXPECT_GE(allIn.view.refereeStandings.at(1).controlScore, victoryControl);

  const auto contest = runLine(K_SEED, 1400, PlayerLine::Contest);
  EXPECT_EQ(contest.overallStatus, game::CampaignStatus::Won);
  EXPECT_EQ(contest.winner, contest.view.playerFaction);
  EXPECT_GE(contest.view.refereeStandings.at(0).controlScore, victoryControl); // player reached it
  EXPECT_LT(contest.view.refereeStandings.at(1).controlScore, victoryControl); // rival denied

  // The rival's domination fires sooner against the lines that ignore it than the
  // fortress ever allows -- concentration is the fast way to lose.
  EXPECT_LT(outer.turn, contest.turn);
  EXPECT_LT(allIn.turn, outer.turn);
}

namespace {

constexpr double K_SECONDS_PER_DAY = 86400.0;
constexpr double K_LIGHT_DAY_CM = K_SECONDS_PER_DAY * 2.99792458e10;

// Three micro systems in a chain: 0 -- 1 -- 2, 30 light-days per link, and no
// direct 0 -- 2 link.
game::ConstellationConfig chainConfig() {
  game::ConstellationConfig config;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.systems = {microSystem(), microSystem(), microSystem()};
  config.links = {game::InterSystemLink{.a = 0, .b = 1, .separationCm = 30.0 * K_LIGHT_DAY_CM},
                  game::InterSystemLink{.a = 1, .b = 2, .separationCm = 30.0 * K_LIGHT_DAY_CM}};
  return config;
}

// Radial light leg from band `band` of a micro system to its authority.
double microRadialSec(int band) {
  const game::SystemSpec spec = microSystem();
  const game::KerrTimeField field(spec.blackHoleMassG, spec.spinDimensionless);
  return field.signalDelaySec(spec.bandRadiusCm.at(static_cast<std::size_t>(band)),
                              spec.authorityRadiusCm);
}

// Turn on which an observation emitted on turn 1 arrives after delaySec.
std::int64_t arrivalTurn(double delaySec) {
  return 1 + static_cast<std::int64_t>(std::ceil(delaySec / K_SECONDS_PER_DAY));
}

} // namespace

// Falsifier: an observer two links away (no direct link) learning that alpha
// holds system 0 band 0 before the radial leg plus both 30-day hops could
// carry it, or never learning it; the one-hop observer likewise against one
// hop. Before the path matrix, the unlinked observer saw it on turn 1.
TEST(Constellation, ChainedSystemsLearnAfterTheSummedLightPath) {
  game::Constellation constellation(chainConfig());
  ASSERT_TRUE(constellation.valid());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  constellation.addFaction(game::FactionPolicy::Scripted, 1);
  constellation.addFaction(game::FactionPolicy::Scripted, 2);
  ASSERT_NE(constellation.addFleet(alpha, 0, game::FleetCapability::Extraction, 0),
            game::K_INVALID_FLEET_ID);

  const double radialSec = microRadialSec(0);
  const std::int64_t oneHop = arrivalTurn(radialSec + (30.0 * K_SECONDS_PER_DAY));
  const std::int64_t twoHops = arrivalTurn(radialSec + (60.0 * K_SECONDS_PER_DAY));
  ASSERT_EQ(twoHops, 62);
  while (constellation.turn() < twoHops) {
    constellation.advanceTurn();
    const bool oneHopKnows = constellation.perceivedController(1, 0, 0) == alpha;
    const bool twoHopKnows = constellation.perceivedController(2, 0, 0) == alpha;
    EXPECT_EQ(oneHopKnows, constellation.turn() >= oneHop) << "turn " << constellation.turn();
    EXPECT_EQ(twoHopKnows, constellation.turn() >= twoHops) << "turn " << constellation.turn();
  }
  EXPECT_EQ(constellation.perceivedController(2, 0, 0), alpha);
}

// Falsifier: a rival homed in the same M87-mass system perceiving a hold on
// the 1.7M band before the radial light leg to the authority (about 154 days)
// has elapsed -- the leg the observation delay once skipped.
TEST(Constellation, SameSystemIntelWaitsForTheRadialLeg) {
  const game::KerrTimeField field(6.5e9 * K_SOLAR_MASS_G, 0.9);
  const double massCm = field.gravitationalRadiusCm();
  game::ConstellationConfig config;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.systems = {game::SystemSpec{.blackHoleMassG = 6.5e9 * K_SOLAR_MASS_G,
                                     .spinDimensionless = 0.9,
                                     .authorityRadiusCm = 400.0 * massCm,
                                     .bandRadiusCm = {1.7 * massCm, 20.0 * massCm}}};
  game::Constellation constellation(config);
  ASSERT_TRUE(constellation.valid());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  constellation.addFaction(game::FactionPolicy::Scripted, 0);
  ASSERT_NE(constellation.addFleet(alpha, 0, game::FleetCapability::Extraction, 0,
                                   game::OrbitLane::Prograde, game::StationKeeping::Hover),
            game::K_INVALID_FLEET_ID);
  const std::int64_t expected =
      arrivalTurn(field.signalDelaySec(1.7 * massCm, 400.0 * massCm));
  ASSERT_GT(expected, 150);
  while (constellation.turn() < expected) {
    constellation.advanceTurn();
    EXPECT_EQ(constellation.perceivedController(1, 0, 0) == alpha,
              constellation.turn() >= expected)
        << "turn " << constellation.turn();
  }
}

// Falsifier: a disconnected system accepting an order, or banking yield, from
// a faction whose home no chain of links reaches -- the zero-delay channel the
// unlinked-pair fallback once opened.
TEST(Constellation, UnreachableSystemsNeverExchangeSignals) {
  game::ConstellationConfig config;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.systems = {microSystem(), microSystem()};
  config.workProperHoursPerReport = 1.0;
  game::Constellation constellation(config);
  ASSERT_TRUE(constellation.valid());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FactionId beta = constellation.addFaction(game::FactionPolicy::Scripted, 1);
  const game::FleetId stranded =
      constellation.addFleet(alpha, 1, game::FleetCapability::Extraction, 0);
  ASSERT_NE(stranded, game::K_INVALID_FLEET_ID);
  EXPECT_FALSE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = stranded, .targetSystem = 1, .targetBand = 1}));
  constellation.advanceTurns(50);
  EXPECT_DOUBLE_EQ(constellation.factions().front().energyUnits, 0.0);
  EXPECT_EQ(constellation.perceivedController(0, 1, 0), game::K_INVALID_FACTION_ID);
  EXPECT_EQ(constellation.perceivedController(1, 1, 0), alpha);
  static_cast<void>(beta);
}

// Falsifier: a rival 30 light-days from the winning band refused an order
// before light from that band could carry the decision, or still accepted
// after it lands; or the winner, whose band sits a fraction of a day from its
// own authority, accepting an order once that radial leg has elapsed.
TEST(Constellation, OutcomeLatchesPerFactionAfterLight) {
  game::ConstellationConfig config = microTwoSystemConfig();
  config.victoryControlScore = 3.0;
  config.fleetInitialFuelUnits = 1.0e6;
  game::Constellation constellation(config);
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FactionId beta = constellation.addFaction(game::FactionPolicy::Scripted, 1);
  const game::FleetId alphaFleet =
      constellation.addFleet(alpha, 0, game::FleetCapability::Extraction, 0);
  const game::FleetId betaFleet =
      constellation.addFleet(beta, 1, game::FleetCapability::Extraction, 0);
  ASSERT_NE(betaFleet, game::K_INVALID_FLEET_ID);

  // Alpha and beta each hold a band from turn 1; alpha is registered first,
  // so the lowest-id tie-break makes alpha the winner on turn 3, at its band.
  constellation.advanceTurns(3);
  ASSERT_EQ(constellation.winner(), alpha);
  const game::ConstellationCommand alphaHop{.fleet = alphaFleet, .targetSystem = 0, .targetBand = 1};
  constellation.advanceTurn(); // turn 4: the radial leg (< 1 day) has landed
  EXPECT_FALSE(constellation.issueCommand(alpha, alphaHop));

  const game::ConstellationCommand hop{.fleet = betaFleet, .targetSystem = 1, .targetBand = 1};
  const std::int64_t noticeTurn = arrivalTurn(microRadialSec(0) + (30.0 * K_SECONDS_PER_DAY)) + 2;
  while (constellation.turn() < noticeTurn - 1) {
    constellation.advanceTurn();
  }
  EXPECT_TRUE(constellation.issueCommand(beta, hop)) << "turn " << constellation.turn();
  constellation.advanceTurn();
  EXPECT_EQ(constellation.turn(), noticeTurn);
  EXPECT_FALSE(constellation.issueCommand(beta, hop)) << "turn " << constellation.turn();
}

// Falsifier: an authority 30 light-days from its fleet refusing an order its
// last report says is affordable because of a fuel spend it cannot yet know
// of, its view showing the fleet's new band before the report could arrive,
// or its view never catching up once the report does.
TEST(Constellation, OwnFleetStateArrivesOnlyByReport) {
  game::ConstellationConfig config = microTwoSystemConfig();
  config.fleetInitialFuelUnits = 20.0; // exactly one band hop
  config.fuelPerBandHop = 20.0;
  game::Constellation constellation(config);
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FactionId beta = constellation.addFaction(game::FactionPolicy::Scripted, 1);
  const game::FleetId remote = constellation.addFleet(alpha, 1, game::FleetCapability::Research, 0);
  ASSERT_NE(remote, game::K_INVALID_FLEET_ID);
  // Only the owner can command it.
  EXPECT_FALSE(constellation.issueCommand(
      beta, game::ConstellationCommand{.fleet = remote, .targetSystem = 1, .targetBand = 1}));

  const game::ConstellationCommand toOuter{.fleet = remote, .targetSystem = 1, .targetBand = 1};
  const game::ConstellationCommand toInner{.fleet = remote, .targetSystem = 1, .targetBand = 0};
  ASSERT_TRUE(constellation.issueCommand(alpha, toOuter));
  const std::int64_t effect = 0 + static_cast<std::int64_t>(std::ceil(
                                      (microRadialSec(0) + (30.0 * K_SECONDS_PER_DAY)) /
                                      K_SECONDS_PER_DAY));
  const std::int64_t reportArrives =
      effect + static_cast<std::int64_t>(
                   std::ceil((microRadialSec(0) + (30.0 * K_SECONDS_PER_DAY)) / K_SECONDS_PER_DAY));
  while (constellation.turn() < effect + 5) {
    constellation.advanceTurn();
  }
  // The fleet has moved and spent its fuel; its authority still holds the old
  // report, so a second hop it believes affordable is accepted at issue.
  // (Repeating the pending hop would be refused as a no-op; this one changes
  // lane.)
  ASSERT_EQ(constellation.fleets().front().bandIndex, 1);
  ASSERT_DOUBLE_EQ(constellation.fleets().front().fuelUnits, 0.0);
  EXPECT_EQ(constellation.renderSnapshot().fleets.front().bandIndex, 0);
  EXPECT_FALSE(constellation.issueCommand(alpha, toOuter));
  EXPECT_TRUE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = remote,
                                        .targetSystem = 1,
                                        .targetBand = 1,
                                        .lane = game::OrbitLane::Retrograde}));

  while (constellation.turn() < reportArrives) {
    constellation.advanceTurn();
  }
  const game::ConstellationViewSnapshot view = constellation.renderSnapshot();
  EXPECT_EQ(view.fleets.front().bandIndex, 1);
  EXPECT_EQ(view.fleets.front().reportedTurn, effect);
  // Now the authority knows the tank is empty: the hop back is refused.
  EXPECT_FALSE(constellation.issueCommand(alpha, toInner));
}

namespace {

/** One turn of a fleet's transit, as seen from outside. */
struct TransitStep {
  bool coasting = false;  ///< In transit before and after the turn.
  bool arrived = false;   ///< In transit before, landed after.
  double agedDays = 0.0;  ///< Proper days the crew aged this turn.
  game::SystemId system = game::K_INVALID_SYSTEM_ID;
  int bandIndex = 0;
};

TransitStep stepFront(game::Constellation &constellation) {
  const game::ConstellationFleet before = constellation.fleets().front();
  constellation.advanceTurn();
  const game::ConstellationFleet &after = constellation.fleets().front();
  return TransitStep{.coasting = before.inTransit && after.inTransit,
                     .arrived = before.inTransit && !after.inTransit,
                     .agedDays = (after.properTimeSec - before.properTimeSec) / K_SECONDS_PER_DAY,
                     .system = after.system,
                     .bandIndex = after.bandIndex};
}

} // namespace

// Falsifier: a crew coasting a 40 light-day hop at 0.5c aging anything but
// sqrt(1 - 0.25) = 0.866 of each coordinate day, or the fleet leaving its
// origin system's books before it arrives (the destination learns of it only
// on arrival).
TEST(Constellation, TransitAgesCrewsRelativisticallyAndArrivesOnArrival) {
  game::ConstellationSession session(K_SEED);
  game::Constellation &constellation = session.constellation();
  ASSERT_TRUE(session.movePlayerFleet(constellation.fleets().front().id, 1, 1));
  const double coastRate = std::sqrt(1.0 - (0.5 * 0.5));
  int transitTurns = 0;
  TransitStep step;
  for (int turn = 0; turn < 400 && !step.arrived; ++turn) {
    step = stepFront(constellation);
    if (step.coasting) {
      ++transitTurns;
      EXPECT_NEAR(step.agedDays, coastRate, 1e-12);
      EXPECT_EQ(step.system, 0U) << "still booked in the origin system while coasting";
    }
  }
  ASSERT_TRUE(step.arrived);
  EXPECT_EQ(step.system, 1U);
  EXPECT_EQ(step.bandIndex, 1);
  EXPECT_EQ(transitTurns, 79); // an 80-turn hop: departure turn plus 79 full coasting turns
}

// Falsifier: two constellations differing only in one system's spin deficit,
// or in one fleet's station keeping, serializing to the same bytes.
TEST(Constellation, DigestCarriesObserverAndSpinDeficit) {
  const auto build = [](double spin, game::StationKeeping station) {
    game::ConstellationConfig config = microTwoSystemConfig();
    config.systems.at(1).spinDimensionless = spin;
    game::Constellation constellation(config);
    const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
    constellation.addFleet(alpha, 0, game::FleetCapability::Research, 1, game::OrbitLane::Prograde,
                           station);
    return constellation.serializeState();
  };
  EXPECT_NE(build(0.0, game::StationKeeping::Orbit), build(0.0, game::StationKeeping::Hover));
  EXPECT_NE(build(0.0, game::StationKeeping::Orbit), build(0.5, game::StationKeeping::Orbit));
  EXPECT_EQ(build(0.5, game::StationKeeping::Hover), build(0.5, game::StationKeeping::Hover));
}

// Falsifier: an order addressed to the slot where a fleet was last reported
// acting on that fleet after it has moved to another system -- reaching it
// faster than light could -- or the fizzled order staying in flight forever.
// Chain 0 -(100 ld)- 1 -(5 ld)- 2: the fleet leaves system 1 for system 2, and
// an intra-system hop addressed to system 1 lands after it has gone.
TEST(Constellation, OrderToAMovedFleetFizzlesAtItsAddress) {
  game::ConstellationConfig config;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.systems = {microSystem(), microSystem(), microSystem()};
  config.links = {game::InterSystemLink{.a = 0, .b = 1, .separationCm = 100.0 * K_LIGHT_DAY_CM},
                  game::InterSystemLink{.a = 1, .b = 2, .separationCm = 5.0 * K_LIGHT_DAY_CM}};
  config.fleetInitialFuelUnits = 1.0e6;
  game::Constellation constellation(config);
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FleetId fleet = constellation.addFleet(alpha, 1, game::FleetCapability::Research, 0);
  ASSERT_TRUE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = fleet, .targetSystem = 2, .targetBand = 0}));
  constellation.advanceTurns(130);
  ASSERT_EQ(constellation.fleets().front().system, 2U); // departed t101, arrived t111
  ASSERT_EQ(constellation.renderSnapshot().fleets.front().system, 1U); // report still in flight
  ASSERT_TRUE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = fleet, .targetSystem = 1, .targetBand = 1}));
  bool everLeftSystem2 = false;
  for (int turn = 0; turn < 400; ++turn) {
    constellation.advanceTurn();
    const game::ConstellationFleet &now = constellation.fleets().front();
    everLeftSystem2 = everLeftSystem2 || now.inTransit || now.system != 2U;
  }
  EXPECT_FALSE(everLeftSystem2);
  // Both reports and the non-delivery notice are home by now: the authority
  // sees the fleet in system 2 and can order it again.
  const game::ConstellationViewSnapshot view = constellation.renderSnapshot();
  EXPECT_EQ(view.fleets.front().system, 2U);
  EXPECT_TRUE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = fleet, .targetSystem = 2, .targetBand = 1}));
}

namespace {

// Alpha homed in system 0 holds only a band in system 1, 30 light-days away;
// beta is homed in system 1. Control target 3 is reached at that band on turn 3.
struct RemoteWin {
  game::Constellation constellation;
  game::FactionId alpha = game::K_INVALID_FACTION_ID;
  game::FactionId beta = game::K_INVALID_FACTION_ID;
  game::FleetId alphaFleet = game::K_INVALID_FLEET_ID;
};

game::ConstellationConfig remoteWinConfig() {
  game::ConstellationConfig config = microTwoSystemConfig();
  config.victoryControlScore = 3.0;
  config.fleetInitialFuelUnits = 1.0e6;
  return config;
}

} // namespace

// Falsifier: alpha's authority learning of a win (or crediting the control
// that earned it) before the report from its band 30 light-days away could
// arrive -- the instant self-latch the referee's crossing once granted.
TEST(Constellation, WinnerLearnsOnlyWhenItsReportArrives) {
  game::Constellation constellation(remoteWinConfig());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  constellation.addFaction(game::FactionPolicy::Scripted, 1);
  const game::FleetId fleet = constellation.addFleet(alpha, 1, game::FleetCapability::Research, 0);
  ASSERT_NE(fleet, game::K_INVALID_FLEET_ID);
  const game::ConstellationCommand hop{.fleet = fleet, .targetSystem = 1, .targetBand = 1};
  // The decision happens at turn 3; its news reaches alpha after the radial
  // leg plus 30 days.
  const std::int64_t learned = arrivalTurn(microRadialSec(0) + (30.0 * K_SECONDS_PER_DAY)) + 2;
  while (constellation.turn() < learned - 1) {
    constellation.advanceTurn();
    EXPECT_FALSE(constellation.factions().front().outcomeKnown) << "turn " << constellation.turn();
  }
  EXPECT_EQ(constellation.winner(), alpha);
  // The reports of turns 1 and 2 have landed; turn 3's, which crossed the
  // target, arrives with the decision.
  EXPECT_DOUBLE_EQ(constellation.factions().front().knownControlScore, 2.0);
  EXPECT_TRUE(constellation.issueCommand(alpha, hop));
  constellation.advanceTurn();
  EXPECT_TRUE(constellation.factions().front().outcomeKnown);
  EXPECT_FALSE(constellation.issueCommand(alpha, hop));
}

// Falsifier: beta, homed in the system where alpha's winning band lies,
// learning of the decision later than the radial leg from that band to its
// own authority -- the notice once routed from alpha's distant home instead.
TEST(Constellation, OutcomeNoticeLeavesFromTheDecidingBand) {
  game::Constellation constellation(remoteWinConfig());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  constellation.addFaction(game::FactionPolicy::Scripted, 1);
  ASSERT_NE(constellation.addFleet(alpha, 1, game::FleetCapability::Research, 0),
            game::K_INVALID_FLEET_ID);
  constellation.advanceTurns(3);
  ASSERT_EQ(constellation.winner(), alpha);
  EXPECT_FALSE(constellation.factions().at(1).outcomeKnown);
  constellation.advanceTurn(); // turn 4 = 3 + ceil(radial leg of about 2000 s)
  EXPECT_TRUE(constellation.factions().at(1).outcomeKnown);
  EXPECT_FALSE(constellation.factions().front().outcomeKnown);
}

namespace {

// The player homed in system 1, the rival in system 0 winning at its own band
// on turn 3; the player's authority hears of it after the radial leg plus 30
// days. Returns the snapshots on the turn before and the turn the news lands.
struct NoticeSnapshots {
  game::FactionId player = game::K_INVALID_FACTION_ID;
  game::FactionId rival = game::K_INVALID_FACTION_ID;
  game::ConstellationViewSnapshot before;
  game::ConstellationViewSnapshot after;
};

NoticeSnapshots snapshotsAroundNotice() {
  game::Constellation constellation(remoteWinConfig());
  NoticeSnapshots result;
  result.player = constellation.addFaction(game::FactionPolicy::Scripted, 1);
  result.rival = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  constellation.addFleet(result.rival, 0, game::FleetCapability::Research, 0);
  const std::int64_t learned = arrivalTurn(microRadialSec(0) + (30.0 * K_SECONDS_PER_DAY)) + 2;
  while (constellation.turn() < learned - 1) {
    constellation.advanceTurn();
  }
  result.before = constellation.renderSnapshot();
  constellation.advanceTurn();
  result.after = constellation.renderSnapshot();
  return result;
}

} // namespace

// Falsifier: the player's snapshot showing a decided outcome, a winner, or a
// cleared turn before news of the rival's win (30 light-days away) reaches the
// player's authority, or the referee block failing to show the truth at once.
TEST(Constellation, SnapshotHidesTheOutcomeUntilKnown) {
  const NoticeSnapshots snapshots = snapshotsAroundNotice();
  const game::ConstellationViewSnapshot &before = snapshots.before;
  EXPECT_EQ(before.overallStatus, game::CampaignStatus::Ongoing);
  EXPECT_EQ(before.winner, game::K_INVALID_FACTION_ID);
  EXPECT_EQ(before.player.id, snapshots.player);
  EXPECT_EQ(before.player.status, game::CampaignStatus::Ongoing);
  EXPECT_EQ(before.player.clearedTurn, 0);
  EXPECT_EQ(before.refereeStatus, game::CampaignStatus::Lost);
  EXPECT_EQ(before.refereeWinner, snapshots.rival);
  EXPECT_EQ(before.refereeStandings.at(1).clearedTurn, 3);
  EXPECT_EQ(before.refereeInstability.size(), 2U);
}

// Falsifier: once the news lands, the player's snapshot showing anything but
// the loss -- its own status still Ongoing (a loser's referee status never
// changes), a cleared turn for a loss, or no winner.
TEST(Constellation, SnapshotShowsTheLossOnceKnown) {
  const NoticeSnapshots snapshots = snapshotsAroundNotice();
  const game::ConstellationViewSnapshot &after = snapshots.after;
  EXPECT_EQ(after.overallStatus, game::CampaignStatus::Lost);
  EXPECT_EQ(after.winner, snapshots.rival);
  EXPECT_EQ(after.player.status, game::CampaignStatus::Lost);
  EXPECT_EQ(after.player.clearedTurn, 0);
}

// Falsifier: an order that would leave a fleet where it is already bound --
// its reported slot with no order pending, or the target of its pending
// order -- entering the log, or a link of zero separation (a zero-delay
// channel) being accepted.
TEST(Constellation, NoOpOrdersAndZeroLinksAreRefused) {
  game::Constellation constellation(microConfig());
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FleetId fleet = constellation.addFleet(alpha, 0, game::FleetCapability::Research, 0);
  const game::ConstellationCommand stay{.fleet = fleet, .targetSystem = 0, .targetBand = 0};
  const game::ConstellationCommand hop{.fleet = fleet, .targetSystem = 0, .targetBand = 1};
  const std::vector<std::uint8_t> before = constellation.serializeState();
  EXPECT_FALSE(constellation.issueCommand(alpha, stay));
  EXPECT_EQ(constellation.serializeState(), before);
  EXPECT_TRUE(constellation.issueCommand(alpha, hop));
  EXPECT_FALSE(constellation.issueCommand(alpha, hop)); // duplicates the pending order
  EXPECT_TRUE(constellation.issueCommand(alpha, stay)); // countermands it

  game::ConstellationConfig zeroLink = microTwoSystemConfig();
  zeroLink.links.front().separationCm = 0.0;
  EXPECT_FALSE(game::Constellation(zeroLink).valid());
}

// Falsifier: two orders sent on one turn to a fleet on the inner band of an
// M87-mass system -- to the middle band and to the outer band, whose light
// legs home differ by weeks -- leaving the authority holding anything but the
// fleet's true final state and newest report once every signal has landed.
// The second order was addressed to the inner band, so it fizzles there; the
// fleet's report counter orders its reports whatever their return delays.
TEST(Constellation, SameTurnOrdersLeaveTheNewestReport) {
  const game::KerrTimeField field(6.5e9 * K_SOLAR_MASS_G, 0.0);
  const double massCm = field.gravitationalRadiusCm();
  game::ConstellationConfig config;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.fleetInitialFuelUnits = 1.0e6;
  config.systems = {game::SystemSpec{.blackHoleMassG = 6.5e9 * K_SOLAR_MASS_G,
                                     .spinDimensionless = 0.0,
                                     .authorityRadiusCm = 400.0 * massCm,
                                     .bandRadiusCm = {6.0 * massCm, 20.0 * massCm,
                                                      100.0 * massCm}}};
  game::Constellation constellation(config);
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FleetId fleet = constellation.addFleet(alpha, 0, game::FleetCapability::Research, 0);
  ASSERT_TRUE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = fleet, .targetSystem = 0, .targetBand = 1}));
  ASSERT_TRUE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = fleet, .targetSystem = 0, .targetBand = 2}));
  constellation.advanceTurns(400); // two ~150-day legs out and home
  const game::ConstellationFleet &truth = constellation.fleets().front();
  const game::ConstellationViewSnapshot view = constellation.renderSnapshot();
  const game::ConstellationFleetView &known = view.fleets.front();
  EXPECT_EQ(truth.bandIndex, 1);
  EXPECT_EQ(known.bandIndex, truth.bandIndex);
  EXPECT_EQ(truth.reportsSent, 1U);
  EXPECT_TRUE(constellation.issueCommand(
      alpha, game::ConstellationCommand{.fleet = fleet, .targetSystem = 0, .targetBand = 2}));
}
