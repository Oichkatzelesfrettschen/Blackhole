/**
 * @file campaign_economy_test.cpp
 * @brief Falsification gates for the campaign economy: yield banked only on
 *        report arrival, band-scaled yield, reliability wear, fuel charging
 *        at effect time, and latched victory/loss outcomes.
 */

#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "campaign_test_field.h"
#include "game/campaign.h"
#include "game/campaign_view.h"
#include "game/command.h"
#include "game/fleet.h"

namespace {

using campaign_test::FakeSpinningField;
using campaign_test::FakeTimeField;
using campaign_test::fakeConfig;

game::Command assignTask(game::FleetId fleet, double costSec) {
  game::Command command;
  command.type = game::CommandType::AssignTask;
  command.fleet = fleet;
  command.properTimeCostSec = costSec;
  return command;
}

game::Command placeFleet(game::FleetId fleet, int targetBand) {
  game::Command command;
  command.type = game::CommandType::PlaceFleet;
  command.fleet = fleet;
  command.targetBand = targetBand;
  return command;
}

game::Command placeFleetLane(game::FleetId fleet, int targetBand, game::OrbitLane lane) {
  game::Command command = placeFleet(fleet, targetBand);
  command.lane = lane;
  return command;
}

// Two bands: 960 (inside the ergoregion, rate 0.1) and 995 (outside, rate 1.0).
game::CampaignConfig spinningConfig() {
  game::CampaignConfig config;
  config.seed = 5;
  config.secondsPerTurn = 1.0;
  config.authorityRadiusCm = 1000.0;
  config.bandRadiusCm = {960.0, 995.0};
  return config;
}

} // namespace

TEST(CampaignEconomy, YieldIsBankedOnReportArrivalNotCompletion) {
  const FakeTimeField field;
  game::CampaignState campaign(fakeConfig(), field);
  ASSERT_TRUE(campaign.valid());
  const game::FleetId farFleet = campaign.addFleet(game::FleetCapability::Extraction, 1);
  ASSERT_TRUE(campaign.issueCommand(assignTask(farFleet, 0.5)));

  // Order lands turn 5 and completes turn 5; the report needs 5 more turns.
  campaign.advanceTurns(9);
  EXPECT_DOUBLE_EQ(campaign.energyUnits(), 0.0)
      << "value must not exist at the authority before its report arrives";
  campaign.advanceTurn(); // turn 10
  const double expectedYield = (0.5 / 3600.0) / 1.0; // properHours / rate, reliability 1
  EXPECT_DOUBLE_EQ(campaign.energyUnits(), expectedYield);
  ASSERT_EQ(campaign.intelLog().size(), 1U);
  EXPECT_DOUBLE_EQ(campaign.intelLog().front().yieldUnits, expectedYield);
}

TEST(CampaignEconomy, DeepWorkYieldsMorePerProperHour) {
  const FakeTimeField field;
  game::CampaignState nearCampaign(fakeConfig(), field);
  game::CampaignState farCampaign(fakeConfig(), field);
  const game::FleetId nearFleet = nearCampaign.addFleet(game::FleetCapability::Extraction, 0);
  const game::FleetId farFleet = farCampaign.addFleet(game::FleetCapability::Extraction, 1);
  ASSERT_TRUE(nearCampaign.issueCommand(assignTask(nearFleet, 0.5)));
  ASSERT_TRUE(farCampaign.issueCommand(assignTask(farFleet, 0.5)));
  // Long enough for both reports: near needs 40 + ceil(0.5/0.1)=5 + 40 turns.
  nearCampaign.advanceTurns(100);
  farCampaign.advanceTurns(100);
  ASSERT_GT(nearCampaign.energyUnits(), 0.0);
  ASSERT_GT(farCampaign.energyUnits(), 0.0);
  // Same proper-time cost, rate 0.1 vs 1.0: the deep task is worth 10x.
  EXPECT_DOUBLE_EQ(nearCampaign.energyUnits(), 10.0 * farCampaign.energyUnits());
}

TEST(CampaignEconomy, ReliabilityWearsOnlyWhileWorking) {
  const FakeTimeField field;
  game::CampaignConfig config = fakeConfig();
  config.reliabilityWearPerProperDay = 86400.0 * 0.01; // 0.01 per proper second worked
  config.reliabilityFloor = 0.9;
  game::CampaignState campaign(config, field);
  const game::FleetId worker = campaign.addFleet(game::FleetCapability::Fabrication, 1);
  const game::FleetId idler = campaign.addFleet(game::FleetCapability::Relay, 1);
  ASSERT_NE(idler, game::K_INVALID_FLEET_ID);
  ASSERT_TRUE(campaign.issueCommand(assignTask(worker, 3.0)));
  campaign.advanceTurns(20); // order lands t5, work t5-t7 (3 proper seconds)
  EXPECT_NEAR(campaign.fleets().at(0).reliability, 1.0 - 0.03, 1e-12);
  EXPECT_DOUBLE_EQ(campaign.fleets().at(1).reliability, 1.0) << "idle fleets do not wear";

  // The floor stops wear: a long task cannot degrade a fleet below it.
  ASSERT_TRUE(campaign.issueCommand(assignTask(worker, 50.0)));
  campaign.advanceTurns(100);
  EXPECT_DOUBLE_EQ(campaign.fleets().at(0).reliability, 0.9);
}

TEST(CampaignEconomy, FuelIsChargedAtEffectTimeAndUnaffordableMovesFizzle) {
  const FakeTimeField field;
  game::CampaignConfig config = fakeConfig();
  config.fleetInitialFuelUnits = 30.0;
  config.fuelPerBandHop = 20.0;
  game::CampaignState campaign(config, field);
  const game::FleetId fleet = campaign.addFleet(game::FleetCapability::Research, 1);

  // Two orders issued back-to-back from band 1: "go to band 0" (1 hop, 20
  // fuel, affordable) and "stay on band 1" (0 hops at issue). Both land turn
  // 5 in issue order. After the first executes the fleet is on band 0 with 10
  // fuel; the second now needs a 20-fuel hop back and fizzles.
  ASSERT_TRUE(campaign.issueCommand(placeFleet(fleet, 0)));
  ASSERT_TRUE(campaign.issueCommand(placeFleet(fleet, 1)));

  campaign.advanceTurns(4);
  EXPECT_DOUBLE_EQ(campaign.fleets().front().fuelUnits, 30.0)
      << "fuel is charged at effect time, not at issue";
  EXPECT_EQ(campaign.fleets().front().bandIndex, 1);

  campaign.advanceTurn(); // turn 5: both orders land
  EXPECT_EQ(campaign.fleets().front().bandIndex, 0) << "unaffordable second move fizzled";
  EXPECT_DOUBLE_EQ(campaign.fleets().front().fuelUnits, 10.0);

  // Issue-time gate: a hop the fleet cannot afford is rejected outright.
  EXPECT_FALSE(campaign.issueCommand(placeFleet(fleet, 1)));
}

TEST(CampaignEconomy, VictoryLatchesAndClosesTheOrderBook) {
  const FakeTimeField field;
  game::CampaignConfig config = fakeConfig();
  config.victoryEnergyUnits = 1e-5; // first report wins
  config.deadlineTurn = 1000;
  game::CampaignState campaign(config, field);
  const game::FleetId fleet = campaign.addFleet(game::FleetCapability::Extraction, 1);
  ASSERT_TRUE(campaign.issueCommand(assignTask(fleet, 0.5)));
  campaign.advanceTurns(10); // report arrives turn 10
  EXPECT_EQ(campaign.status(), game::CampaignStatus::Won);
  EXPECT_FALSE(campaign.issueCommand(assignTask(fleet, 0.5)))
      << "a decided campaign takes no further orders";
  campaign.advanceTurns(2000); // past the deadline: the outcome stays latched
  EXPECT_EQ(campaign.status(), game::CampaignStatus::Won);
}

TEST(CampaignEconomy, DeadlineWithoutEnergyIsALoss) {
  const FakeTimeField field;
  game::CampaignConfig config = fakeConfig();
  config.victoryEnergyUnits = 1000.0;
  config.deadlineTurn = 3;
  game::CampaignState campaign(config, field);
  const game::FleetId fleet = campaign.addFleet(game::FleetCapability::Research, 1);
  campaign.advanceTurns(2);
  EXPECT_EQ(campaign.status(), game::CampaignStatus::Ongoing);
  campaign.advanceTurn(); // turn 3 == deadline
  EXPECT_EQ(campaign.status(), game::CampaignStatus::Lost);
  EXPECT_FALSE(campaign.issueCommand(assignTask(fleet, 1.0)));
}

TEST(CampaignEconomy, ReplayStaysByteIdenticalWithEconomyActive) {
  const FakeTimeField field;
  auto runCampaign = [&field]() {
    game::CampaignConfig config = fakeConfig();
    config.victoryEnergyUnits = 5e-4;
    config.deadlineTurn = 200;
    config.reliabilityWearPerProperDay = 86400.0 * 0.001;
    game::CampaignState campaign(config, field);
    const game::FleetId nearFleet = campaign.addFleet(game::FleetCapability::Extraction, 0);
    const game::FleetId farFleet = campaign.addFleet(game::FleetCapability::Verification, 1);
    EXPECT_TRUE(campaign.issueCommand(assignTask(nearFleet, 2.0)));
    EXPECT_TRUE(campaign.issueCommand(assignTask(farFleet, 1.0)));
    campaign.advanceTurns(60);
    EXPECT_TRUE(campaign.issueCommand(placeFleet(farFleet, 0)));
    campaign.advanceTurns(120);
    return campaign.serializeState();
  };
  const std::vector<std::uint8_t> firstRun = runCampaign();
  const std::vector<std::uint8_t> secondRun = runCampaign();
  EXPECT_EQ(firstRun, secondRun);
}

TEST(CampaignFrameDragging, RetrogradeIsRefusedInsideTheErgosphere) {
  const FakeSpinningField field;
  game::CampaignState campaign(spinningConfig(), field);
  ASSERT_TRUE(campaign.valid());
  // Band 0 (960) is inside the ergosphere: retrograde placement is impossible.
  EXPECT_EQ(campaign.addFleet(game::FleetCapability::Extraction, 0, game::OrbitLane::Retrograde),
            game::K_INVALID_FLEET_ID);
  // Prograde there is fine, and retrograde on the outer band (995) is fine.
  EXPECT_NE(campaign.addFleet(game::FleetCapability::Extraction, 0, game::OrbitLane::Prograde),
            game::K_INVALID_FLEET_ID);
  const game::FleetId outer =
      campaign.addFleet(game::FleetCapability::Relay, 1, game::OrbitLane::Retrograde);
  ASSERT_NE(outer, game::K_INVALID_FLEET_ID);
  // An order that would send the outer retrograde fleet into the ergoregion is
  // rejected at issue time.
  EXPECT_FALSE(campaign.issueCommand(placeFleetLane(outer, 0, game::OrbitLane::Retrograde)));
  // The same destination on the prograde lane is accepted.
  EXPECT_TRUE(campaign.issueCommand(placeFleetLane(outer, 0, game::OrbitLane::Prograde)));
}

TEST(CampaignFrameDragging, ProgradeErgoregionWorkBanksThePenroseBonus) {
  const FakeSpinningField field;
  auto bankedYield = [&field](double bonus) {
    game::CampaignConfig config = spinningConfig();
    config.frameDragYieldBonus = bonus;
    game::CampaignState campaign(config, field);
    const game::FleetId fleet =
        campaign.addFleet(game::FleetCapability::Extraction, 0, game::OrbitLane::Prograde);
    EXPECT_NE(fleet, game::K_INVALID_FLEET_ID);
    EXPECT_TRUE(campaign.issueCommand(assignTask(fleet, 0.5)));
    campaign.advanceTurns(200); // deep band: slow proper time + long delays
    return campaign.energyUnits();
  };
  const double plainYield = bankedYield(0.0);
  const double bonusYield = bankedYield(2.0);
  ASSERT_GT(plainYield, 0.0);
  // Band 960 depth = (970 - 960)/(970 - 950) = 0.5, so bonus factor = 1 + 2*0.5
  // = 2.0: the prograde ergoregion fleet banks exactly twice the plain yield.
  EXPECT_NEAR(bonusYield, 2.0 * plainYield, 1e-9 * bonusYield);
}

TEST(CampaignFrameDragging, RetrogradeAndOuterBandsGetNoBonus) {
  const FakeSpinningField field;
  game::CampaignConfig config = spinningConfig();
  config.frameDragYieldBonus = 2.0;
  // Outer band fleet (995, outside the ergosphere) earns no frame-drag bonus.
  game::CampaignState outerCampaign(config, field);
  const game::FleetId outerFleet =
      outerCampaign.addFleet(game::FleetCapability::Extraction, 1, game::OrbitLane::Prograde);
  EXPECT_TRUE(outerCampaign.issueCommand(assignTask(outerFleet, 0.5)));
  outerCampaign.advanceTurns(200);

  game::CampaignConfig noBonus = spinningConfig();
  noBonus.frameDragYieldBonus = 0.0;
  game::CampaignState controlCampaign(noBonus, field);
  const game::FleetId controlFleet =
      controlCampaign.addFleet(game::FleetCapability::Extraction, 1, game::OrbitLane::Prograde);
  EXPECT_TRUE(controlCampaign.issueCommand(assignTask(controlFleet, 0.5)));
  controlCampaign.advanceTurns(200);

  EXPECT_DOUBLE_EQ(outerCampaign.energyUnits(), controlCampaign.energyUnits())
      << "outside the ergosphere the bonus coefficient is irrelevant";
}
