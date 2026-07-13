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

#include <cstdint>

#include "game/campaign_view.h"
#include "game/constellation.h"
#include "game/constellation_session.h"
#include "game/constellation_sim_lines.h"
#include "game/constellation_types.h"
#include "game/constellation_view.h"
#include "game/fleet.h"
#include "game/kerr_time_field.h"

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
  EXPECT_EQ(outer.winner, outer.view.factions.at(1).id); // the rival won
  EXPECT_GE(outer.view.factions.at(1).controlScore, victoryControl); // by domination

  const auto allIn = runLine(K_SEED, 1400, PlayerLine::AllIn);
  EXPECT_EQ(allIn.overallStatus, game::CampaignStatus::Lost);
  EXPECT_EQ(allIn.winner, allIn.view.factions.at(1).id);
  EXPECT_GE(allIn.view.factions.at(1).controlScore, victoryControl);

  const auto contest = runLine(K_SEED, 1400, PlayerLine::Contest);
  EXPECT_EQ(contest.overallStatus, game::CampaignStatus::Won);
  EXPECT_EQ(contest.winner, contest.view.playerFaction);
  EXPECT_GE(contest.view.factions.at(0).controlScore, victoryControl); // player reached it
  EXPECT_LT(contest.view.factions.at(1).controlScore, victoryControl); // rival denied

  // The rival's domination fires sooner against the lines that ignore it than the
  // fortress ever allows -- concentration is the fast way to lose.
  EXPECT_LT(outer.turn, contest.turn);
  EXPECT_LT(allIn.turn, outer.turn);
}
