/**
 * @file campaign_instability_test.cpp
 * @brief Falsification gates for the CAMPAIGN-6 instability mechanic: the
 *        disturbance rises each turn and erodes yield, a prograde ergoregion
 *        fleet's containment suppresses it, deep work wears integrity faster,
 *        the mechanic is inert by default, and the whole thing stays
 *        deterministic.
 *
 * Turns are one day long so proper-day arithmetic is exact: at the spinning
 * fake's ergoregion band (radius 960, rate 0.1, depth 0.5) a working fleet logs
 * 0.1 proper-day per turn; at the outer band (995, rate 1.0) it logs 1.0.
 */

#include <gtest/gtest.h>

#include "campaign_test_field.h"
#include "game/campaign.h"
#include "game/command.h"
#include "game/fleet.h"

namespace {

using campaign_test::FakeSpinningField;

constexpr double K_DAY = 86400.0;
constexpr int K_ERGO_BAND = 0; // radius 960: inside the ergoregion, depth 0.5.
constexpr int K_OUTER_BAND = 1; // radius 995: outside the static limit.

// Day-long turns over the spinning fake. Authority at 1000, bands {960, 995}.
game::CampaignConfig instabilityConfig() {
  game::CampaignConfig config;
  config.seed = 7;
  config.secondsPerTurn = K_DAY;
  config.authorityRadiusCm = 1000.0;
  config.bandRadiusCm = {960.0, 995.0};
  return config;
}

game::Command assignTask(game::FleetId fleet, double costSec) {
  game::Command command;
  command.type = game::CommandType::AssignTask;
  command.fleet = fleet;
  command.properTimeCostSec = costSec;
  return command;
}

double fleetReliability(const game::CampaignState &campaign, game::FleetId fleet) {
  for (const game::Fleet &candidate : campaign.fleets()) {
    if (candidate.id == fleet) {
      return candidate.reliability;
    }
  }
  return -1.0;
}

} // namespace

// Instability accumulates by exactly instabilityPerTurn each turn when nothing
// contains it.
TEST(CampaignInstability, RisesByRatePerTurnUncontained) {
  const FakeSpinningField field;
  game::CampaignConfig config = instabilityConfig();
  config.instabilityPerTurn = 0.5;
  game::CampaignState campaign(config, field);
  campaign.advanceTurns(10);
  EXPECT_DOUBLE_EQ(campaign.instability(), 5.0);
  EXPECT_DOUBLE_EQ(campaign.stabilization(), 0.0);
}

// A prograde ergoregion fleet at work suppresses instability: with containment
// on, the disturbance ends lower and stabilization accrues.
TEST(CampaignInstability, ProgradeErgoContainmentSuppresses) {
  const FakeSpinningField field;
  game::CampaignConfig base = instabilityConfig();
  base.instabilityPerTurn = 0.5;

  // Control: containment disabled -- instability rises the full 0.5 per turn.
  const game::CampaignConfig controlConfig = base;
  game::CampaignState control(controlConfig, field);
  const game::FleetId controlFleet =
      control.addFleet(game::FleetCapability::Research, K_ERGO_BAND, game::OrbitLane::Prograde);
  ASSERT_NE(controlFleet, game::K_INVALID_FLEET_ID);
  ASSERT_TRUE(control.issueCommand(assignTask(controlFleet, 1.0e9))); // never completes: works every turn
  control.advanceTurns(10);

  // Contained: the same deep prograde worker now produces containment.
  game::CampaignConfig containedConfig = base;
  containedConfig.ergoContainmentPerProperDay = 4.0; // 0.1 day * 4 * depth 0.5 = 0.2 per turn
  game::CampaignState contained(containedConfig, field);
  const game::FleetId deepFleet =
      contained.addFleet(game::FleetCapability::Research, K_ERGO_BAND, game::OrbitLane::Prograde);
  ASSERT_NE(deepFleet, game::K_INVALID_FLEET_ID);
  ASSERT_TRUE(contained.issueCommand(assignTask(deepFleet, 1.0e9)));
  contained.advanceTurns(10);

  EXPECT_DOUBLE_EQ(control.instability(), 5.0);
  EXPECT_LT(contained.instability(), control.instability());
  EXPECT_GT(contained.stabilization(), 0.0);
  // Net per turn: +0.5 rise - 0.2 containment = +0.3, so 3.0 after 10 turns.
  EXPECT_DOUBLE_EQ(contained.instability(), 3.0);
  EXPECT_DOUBLE_EQ(contained.stabilization(), 2.0);
}

// Rising instability erodes banked yield: the penalised run banks less than an
// otherwise identical run with the penalty disabled.
TEST(CampaignInstability, YieldPenaltyReducesBankedEnergy) {
  const FakeSpinningField field;
  game::CampaignConfig base = instabilityConfig();
  base.instabilityPerTurn = 1.0;

  // A 30-day task at the outer band (rate 1.0) completes on turn 30, by when
  // instability has risen to 29 -- so the penalty, which reads the instability
  // entering the completing turn, actually bites.
  const double taskCostSec = 30.0 * K_DAY;

  const game::CampaignConfig noPenalty = base; // penalty coefficient stays 0
  game::CampaignState clean(noPenalty, field);
  const game::FleetId cleanFleet = clean.addFleet(game::FleetCapability::Extraction, K_OUTER_BAND);
  ASSERT_NE(cleanFleet, game::K_INVALID_FLEET_ID);
  ASSERT_TRUE(clean.issueCommand(assignTask(cleanFleet, taskCostSec)));
  clean.advanceTurns(40);

  game::CampaignConfig penalised = base;
  penalised.instabilityYieldPenaltyPerUnit = 0.2;
  game::CampaignState eroded(penalised, field);
  const game::FleetId erodedFleet = eroded.addFleet(game::FleetCapability::Extraction, K_OUTER_BAND);
  ASSERT_NE(erodedFleet, game::K_INVALID_FLEET_ID);
  ASSERT_TRUE(eroded.issueCommand(assignTask(erodedFleet, taskCostSec)));
  eroded.advanceTurns(40);

  EXPECT_GT(clean.energyUnits(), 0.0);
  EXPECT_GT(eroded.energyUnits(), 0.0);
  EXPECT_LT(eroded.energyUnits(), clean.energyUnits());
}

// Deep prograde work wears a fleet faster than equivalent outer work: the
// ergoregion hazard is the integrity the dive spends.
TEST(CampaignInstability, ErgoHazardWearsDeepFleetFaster) {
  const FakeSpinningField field;
  game::CampaignConfig config = instabilityConfig();
  config.reliabilityWearPerProperDay = 0.001; // gentle baseline wear both feel
  config.ergoHazardWearPerProperDay = 0.5;    // deep prograde hazard
  config.reliabilityFloor = 0.0;              // let the difference show without clamping
  game::CampaignState campaign(config, field);
  const game::FleetId deep =
      campaign.addFleet(game::FleetCapability::Research, K_ERGO_BAND, game::OrbitLane::Prograde);
  const game::FleetId outer = campaign.addFleet(game::FleetCapability::Research, K_OUTER_BAND);
  ASSERT_NE(deep, game::K_INVALID_FLEET_ID);
  ASSERT_NE(outer, game::K_INVALID_FLEET_ID);
  ASSERT_TRUE(campaign.issueCommand(assignTask(deep, 1.0e9)));
  ASSERT_TRUE(campaign.issueCommand(assignTask(outer, 1.0e9)));
  campaign.advanceTurns(20);

  // The outer fleet works more proper time (rate 1.0 vs 0.1), yet the deep fleet
  // still ends less reliable: the depth-scaled hazard dominates.
  EXPECT_LT(fleetReliability(campaign, deep), fleetReliability(campaign, outer));
}

// With every instability knob at its default, the mechanic is inert: no
// instability, no stabilization, and yield is untouched.
TEST(CampaignInstability, DisabledByDefaultIsInert) {
  const FakeSpinningField field;
  const game::CampaignConfig config = instabilityConfig(); // all instability knobs default 0
  game::CampaignState campaign(config, field);
  const game::FleetId fleet =
      campaign.addFleet(game::FleetCapability::Research, K_ERGO_BAND, game::OrbitLane::Prograde);
  ASSERT_NE(fleet, game::K_INVALID_FLEET_ID);
  ASSERT_TRUE(campaign.issueCommand(assignTask(fleet, 1.0e9)));
  campaign.advanceTurns(25);
  EXPECT_DOUBLE_EQ(campaign.instability(), 0.0);
  EXPECT_DOUBLE_EQ(campaign.stabilization(), 0.0);
}

// The mechanic is deterministic: two independently built campaigns with the
// same instability config and command log serialize to identical bytes.
TEST(CampaignInstability, DeterministicUnderContainment) {
  const FakeSpinningField field;
  game::CampaignConfig config = instabilityConfig();
  config.instabilityPerTurn = 0.5;
  config.instabilityYieldPenaltyPerUnit = 0.1;
  config.ergoContainmentPerProperDay = 4.0;
  config.ergoHazardWearPerProperDay = 0.2;

  const auto play = [&](game::CampaignState &campaign) {
    const game::FleetId deep =
        campaign.addFleet(game::FleetCapability::Extraction, K_ERGO_BAND, game::OrbitLane::Prograde);
    campaign.issueCommand(assignTask(deep, K_DAY));
    campaign.advanceTurns(30);
  };

  game::CampaignState first(config, field);
  game::CampaignState second(config, field);
  play(first);
  play(second);
  EXPECT_EQ(first.serializeState(), second.serializeState());
  EXPECT_EQ(first.stateDigest(), second.stateDigest());
}
