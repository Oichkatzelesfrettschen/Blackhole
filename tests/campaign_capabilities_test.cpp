/**
 * @file campaign_capabilities_test.cpp
 * @brief Falsification gates for the distinct fleet-capability effects: yield
 *        multipliers, band-local fabrication refuel and verification restore,
 *        relay overhead reduction floored at the geodesic delay, and the
 *        reliability corruption cliff plus its verification interlock.
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

using campaign_test::FakeTimeField;

// Small radii so signal delays are a handful of turns: authority 70, bands at
// 50 (deep) and 60. The FakeTimeField rate is 0.1 at these radii and its delay
// is the plain radial separation, so every number below is exact.
game::CampaignConfig capConfig() {
  game::CampaignConfig config;
  config.seed = 9;
  config.secondsPerTurn = 1.0;
  config.authorityRadiusCm = 70.0;
  config.bandRadiusCm = {50.0, 60.0};
  return config;
}

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

const game::IntelView *findIntel(const game::CampaignViewSnapshot &view, game::FleetId fleet) {
  for (const game::IntelView &report : view.intel) {
    if (report.fleet == fleet) {
      return &report;
    }
  }
  return nullptr;
}

} // namespace

TEST(CampaignCapabilities, YieldMultiplierScalesBankedEnergy) {
  const FakeTimeField field;
  game::CampaignConfig config = capConfig();
  config.capabilityYieldMultiplier = {1.25, 1.0, 0.75, 0.75, 1.5}; // R, F, L, V, E
  game::CampaignState campaign(config, field);
  const game::FleetId extraction = campaign.addFleet(game::FleetCapability::Extraction, 1);
  const game::FleetId research = campaign.addFleet(game::FleetCapability::Research, 1);
  ASSERT_TRUE(campaign.issueCommand(assignTask(extraction, 1.0)));
  ASSERT_TRUE(campaign.issueCommand(assignTask(research, 1.0)));
  campaign.advanceTurns(60);

  const game::CampaignViewSnapshot view = campaign.renderSnapshot();
  const game::IntelView *extractionReport = findIntel(view, extraction);
  const game::IntelView *researchReport = findIntel(view, research);
  ASSERT_NE(extractionReport, nullptr);
  ASSERT_NE(researchReport, nullptr);
  // Same band, rate, reliability and task cost: the only difference is the
  // capability multiplier, so the yield ratio is exactly 1.5 / 1.25.
  EXPECT_NEAR(extractionReport->yieldUnits / researchReport->yieldUnits, 1.5 / 1.25, 1e-9);
}

TEST(CampaignCapabilities, FabricationRefuelsOnlyItsBand) {
  const FakeTimeField field;
  game::CampaignConfig config = capConfig();
  config.fleetInitialFuelUnits = 100.0;
  config.fuelPerBandHop = 10.0;
  config.fabricationFuelRestore = 30.0;
  game::CampaignState campaign(config, field);
  const game::FleetId fabricator = campaign.addFleet(game::FleetCapability::Fabrication, 1);
  const game::FleetId mover = campaign.addFleet(game::FleetCapability::Research, 0);
  const game::FleetId offBand = campaign.addFleet(game::FleetCapability::Research, 1);
  // Move both spenders once so each is down 10 fuel: mover ends co-band with the
  // fabricator (band 1), offBand ends away from it (band 0).
  ASSERT_TRUE(campaign.issueCommand(placeFleet(mover, 1)));
  ASSERT_TRUE(campaign.issueCommand(placeFleet(offBand, 0)));
  ASSERT_TRUE(campaign.issueCommand(assignTask(fabricator, 2.0)));
  campaign.advanceTurns(80);

  const std::vector<game::Fleet> &fleets = campaign.fleets();
  // fleets: [0]=fabricator band1, [1]=mover band1, [2]=offBand band0.
  EXPECT_EQ(fleets.at(1).bandIndex, 1);
  EXPECT_EQ(fleets.at(2).bandIndex, 0);
  EXPECT_DOUBLE_EQ(fleets.at(1).fuelUnits, 100.0) << "co-band fleet refuelled (90 + 30, capped)";
  EXPECT_DOUBLE_EQ(fleets.at(2).fuelUnits, 90.0) << "off-band fleet untouched";
}

TEST(CampaignCapabilities, VerificationRestoresReliabilityOnlyItsBand) {
  const FakeTimeField field;
  game::CampaignConfig config = capConfig();
  config.reliabilityWearPerProperDay = 86400.0 * 0.2; // 0.2 reliability per proper second
  config.reliabilityFloor = 0.1;
  config.verificationReliabilityRestore = 0.15;
  game::CampaignState campaign(config, field);
  const game::FleetId verifier = campaign.addFleet(game::FleetCapability::Verification, 1);
  const game::FleetId coBand = campaign.addFleet(game::FleetCapability::Research, 1);
  const game::FleetId offBand = campaign.addFleet(game::FleetCapability::Research, 0);
  // Every fleet works a 1-second task: each wears 0.2. Verification's completion
  // then restores 0.15 to its band only.
  ASSERT_TRUE(campaign.issueCommand(assignTask(verifier, 1.0)));
  ASSERT_TRUE(campaign.issueCommand(assignTask(coBand, 1.0)));
  ASSERT_TRUE(campaign.issueCommand(assignTask(offBand, 1.0)));
  campaign.advanceTurns(80);

  const std::vector<game::Fleet> &fleets = campaign.fleets();
  // [0]=verifier band1, [1]=coBand band1, [2]=offBand band0.
  EXPECT_NEAR(fleets.at(2).reliability, 0.8, 1e-9) << "off-band worn 0.2, no restore";
  EXPECT_NEAR(fleets.at(1).reliability, 0.95, 1e-9) << "co-band worn 0.2 then restored 0.15";
  EXPECT_GT(fleets.at(1).reliability, fleets.at(2).reliability);
}

TEST(CampaignCapabilities, RelayReducesOverheadNeverBelowGeodesic) {
  const FakeTimeField field;
  auto transitTurns = [&field](bool withRelay) {
    game::CampaignConfig config = capConfig();
    config.signalOverheadFactor = 1.5;
    config.relayDelayFraction = 0.4;
    game::CampaignState campaign(config, field);
    const game::FleetId deep = campaign.addFleet(game::FleetCapability::Extraction, 0); // radius 50
    // A fleet on band 1 (radius 60) sits between the deep fleet and the
    // authority (70). Only a Relay there provides coverage.
    campaign.addFleet(withRelay ? game::FleetCapability::Relay : game::FleetCapability::Research, 1);
    EXPECT_TRUE(campaign.issueCommand(assignTask(deep, 1.0)));
    campaign.advanceTurns(120);
    const game::CampaignViewSnapshot view = campaign.renderSnapshot();
    const game::IntelView *report = findIntel(view, deep);
    EXPECT_NE(report, nullptr);
    return report != nullptr ? (report->receivedTurn - report->completedTurn) : -1;
  };
  // Geodesic delay deep<->authority is |70-50| = 20 s. Overhead 1.5 -> 30 turns
  // without a relay; one covering relay cuts overhead to 1.5*0.6 = 0.9 -> floored
  // at 1.0 -> 20 turns, the geodesic delay itself, never below it.
  const std::int64_t withoutRelay = transitTurns(false);
  const std::int64_t withRelay = transitTurns(true);
  EXPECT_EQ(withoutRelay, 30);
  EXPECT_EQ(withRelay, 20);
  EXPECT_GE(withRelay, 20) << "a relay must never beat light";
}

TEST(CampaignCapabilities, CorruptionDiscountsYieldAndVerificationPreventsIt) {
  const FakeTimeField field;
  // Base config: heavy wear drives a lone worker below the corruption threshold.
  auto bankedYield = [&field](bool withVerifier) {
    game::CampaignConfig config = capConfig();
    config.reliabilityWearPerProperDay = 86400.0 * 0.05; // 0.05 per proper second
    config.reliabilityFloor = 0.1;
    config.reliabilityCorruptionThreshold = 0.9;
    config.corruptedYieldFraction = 0.4;
    config.verificationReliabilityRestore = 0.2;
    game::CampaignState campaign(config, field);
    const game::FleetId worker = campaign.addFleet(game::FleetCapability::Extraction, 1);
    if (withVerifier) {
      const game::FleetId verifier = campaign.addFleet(game::FleetCapability::Verification, 1);
      // The verifier's task finishes one proper-second before the worker's, so
      // its band-local restore lands late enough that the worker is above the
      // threshold at its own completion.
      EXPECT_TRUE(campaign.issueCommand(assignTask(verifier, 3.9)));
    }
    // 4 proper-seconds of work wears the worker 0.2 -> 0.8, below the 0.9
    // threshold, so its report corrupts unless verification restores it.
    EXPECT_TRUE(campaign.issueCommand(assignTask(worker, 4.0)));
    campaign.advanceTurns(120);
    const game::CampaignViewSnapshot view = campaign.renderSnapshot();
    const game::IntelView *report = findIntel(view, worker);
    EXPECT_NE(report, nullptr);
    return report;
  };
  const game::IntelView *unsupported = bankedYield(false);
  const game::IntelView *supported = bankedYield(true);
  ASSERT_NE(unsupported, nullptr);
  ASSERT_NE(supported, nullptr);
  EXPECT_TRUE(unsupported->corrupted) << "a worn worker's telemetry corrupts";
  EXPECT_FALSE(supported->corrupted) << "co-band verification keeps it above threshold";
  EXPECT_GT(supported->yieldUnits, unsupported->yieldUnits);
}

TEST(CampaignCapabilities, BandLocalEffectsAreOrderIndependent) {
  const FakeTimeField field;
  game::CampaignConfig config = capConfig();
  config.fleetInitialFuelUnits = 100.0;
  config.fuelPerBandHop = 10.0;
  config.fabricationFuelRestore = 30.0;
  game::CampaignState campaign(config, field);
  // A co-band fleet before the fabricator in the vector, and one after it: both
  // must be refuelled identically, proving the effect is applied post-loop and
  // not mid-iteration.
  const game::FleetId before = campaign.addFleet(game::FleetCapability::Research, 0);
  const game::FleetId fabricator = campaign.addFleet(game::FleetCapability::Fabrication, 1);
  const game::FleetId after = campaign.addFleet(game::FleetCapability::Research, 0);
  ASSERT_TRUE(campaign.issueCommand(placeFleet(before, 1)));
  ASSERT_TRUE(campaign.issueCommand(placeFleet(after, 1)));
  ASSERT_TRUE(campaign.issueCommand(assignTask(fabricator, 2.0)));
  campaign.advanceTurns(80);
  const std::vector<game::Fleet> &fleets = campaign.fleets();
  // [0]=before band1, [1]=fabricator band1, [2]=after band1.
  EXPECT_DOUBLE_EQ(fleets.at(0).fuelUnits, fleets.at(2).fuelUnits)
      << "fleets before and after the fabricator refuel identically";
  EXPECT_DOUBLE_EQ(fleets.at(0).fuelUnits, 100.0);
}
