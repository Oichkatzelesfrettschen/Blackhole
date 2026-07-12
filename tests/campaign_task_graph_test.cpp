/**
 * @file campaign_task_graph_test.cpp
 * @brief Falsification gates for campaign causality and determinism: no
 *        command or completion report takes effect before its integer arrival
 *        turn, identical seed + command log replays byte-identically, deep
 *        fleets accrue less proper time, and an at-horizon placement is
 *        rejected before any task can advance.
 */

#include <gtest/gtest.h>

#include <cmath>
#include <cstdint>
#include <vector>

#include "game/blackhole_time_field.h"
#include "game/campaign.h"
#include "game/campaign_view.h"
#include "game/command.h"
#include "game/fleet.h"
#include "game/task_graph.h"
#include "game/time_field.h"

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;

// Programmable field: delay is the plain radial separation in seconds, the
// proper-time rate is 0.1 below radius 970 and 1.0 above it. With one second
// per turn every arrival turn in these tests is exact by construction.
class FakeTimeField final : public game::TimeField {
public:
  [[nodiscard]] double properTimeRate(double radiusCm) const override {
    return radiusCm < 970.0 ? 0.1 : 1.0;
  }
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override {
    return std::fabs(toRadiusCm - fromRadiusCm);
  }
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override {
    return std::isfinite(radiusCm) && radiusCm > 1.0;
  }
};

game::CampaignConfig fakeConfig() {
  game::CampaignConfig config;
  config.seed = 11;
  config.secondsPerTurn = 1.0;
  config.authorityRadiusCm = 1000.0; // rate 1.0 at the authority station
  config.bandRadiusCm = {960.0, 995.0}; // near: delay 40, rate 0.1; far: delay 5, rate 1.0
  return config;
}

} // namespace

TEST(CampaignCausality, CommandTakesEffectOnlyAtItsArrivalTurn) {
  const FakeTimeField field;
  game::CampaignState campaign(fakeConfig(), field);
  ASSERT_TRUE(campaign.valid());
  const game::FleetId farFleet = campaign.addFleet(game::FleetCapability::Research, 1);
  ASSERT_NE(farFleet, game::K_INVALID_FLEET_ID);

  game::Command assign;
  assign.type = game::CommandType::AssignTask;
  assign.fleet = farFleet;
  assign.properTimeCostSec = 0.5;
  ASSERT_TRUE(campaign.issueCommand(assign)); // issue turn 0, delay 5 -> effect turn 5

  campaign.advanceTurns(4);
  EXPECT_TRUE(campaign.taskGraph().tasks().empty())
      << "an order in flight must not create work early";
  campaign.advanceTurn(); // turn 5: order lands, task activates and completes
  ASSERT_EQ(campaign.taskGraph().tasks().size(), 1U);
  EXPECT_EQ(campaign.taskGraph().tasks().front().state, game::TaskState::Complete);
}

TEST(CampaignCausality, CompletionReportArrivesOnlyAtItsArrivalTurn) {
  const FakeTimeField field;
  game::CampaignState campaign(fakeConfig(), field);
  ASSERT_TRUE(campaign.valid());
  const game::FleetId farFleet = campaign.addFleet(game::FleetCapability::Research, 1);
  ASSERT_NE(farFleet, game::K_INVALID_FLEET_ID);

  game::Command assign;
  assign.type = game::CommandType::AssignTask;
  assign.fleet = farFleet;
  assign.properTimeCostSec = 0.5;
  ASSERT_TRUE(campaign.issueCommand(assign));

  // Order lands turn 5 and completes the same turn; the report needs another
  // 5 turns back out to the authority station.
  campaign.advanceTurns(9);
  EXPECT_TRUE(campaign.intelLog().empty())
      << "telemetry must not be known before its arrival turn";
  campaign.advanceTurn(); // turn 10
  ASSERT_EQ(campaign.intelLog().size(), 1U);
  EXPECT_EQ(campaign.intelLog().front().receivedTurn, 10);
  EXPECT_EQ(campaign.intelLog().front().completedTurn, 5);
}

TEST(CampaignDeterminism, SameSeedAndCommandLogReplayByteIdentically) {
  const FakeTimeField field;
  auto runCampaign = [&field]() {
    game::CampaignState campaign(fakeConfig(), field);
    EXPECT_TRUE(campaign.valid());
    const game::FleetId nearFleet = campaign.addFleet(game::FleetCapability::Extraction, 0);
    const game::FleetId farFleet = campaign.addFleet(game::FleetCapability::Verification, 1);
    game::Command assign;
    assign.type = game::CommandType::AssignTask;
    assign.fleet = nearFleet;
    assign.properTimeCostSec = 3.0;
    EXPECT_TRUE(campaign.issueCommand(assign));
    campaign.advanceTurns(20);
    game::Command redeploy;
    redeploy.type = game::CommandType::PlaceFleet;
    redeploy.fleet = farFleet;
    redeploy.targetBand = 0;
    EXPECT_TRUE(campaign.issueCommand(redeploy));
    campaign.advanceTurns(30);
    return campaign.serializeState();
  };
  const std::vector<std::uint8_t> firstRun = runCampaign();
  const std::vector<std::uint8_t> secondRun = runCampaign();
  EXPECT_EQ(firstRun, secondRun);
}

TEST(CampaignEconomy, NearBandFleetAccruesLessProperTimePerTurn) {
  const FakeTimeField field;
  game::CampaignState campaign(fakeConfig(), field);
  ASSERT_TRUE(campaign.valid());
  const game::FleetId nearFleet = campaign.addFleet(game::FleetCapability::Extraction, 0);
  const game::FleetId farFleet = campaign.addFleet(game::FleetCapability::Verification, 1);
  ASSERT_NE(nearFleet, game::K_INVALID_FLEET_ID);
  ASSERT_NE(farFleet, game::K_INVALID_FLEET_ID);
  campaign.advanceTurns(10);
  const game::Fleet &near = campaign.fleets().at(0);
  const game::Fleet &far = campaign.fleets().at(1);
  EXPECT_DOUBLE_EQ(near.properTimeSec, 10.0 * 0.1);
  EXPECT_DOUBLE_EQ(far.properTimeSec, 10.0 * 1.0);
  EXPECT_LT(near.properTimeSec, far.properTimeSec);
}

TEST(CampaignHorizonGate, AtHorizonPlacementIsRejectedBeforeAnyTaskAdvances) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  game::CampaignConfig config;
  config.seed = 3;
  config.secondsPerTurn = 3600.0;
  config.authorityRadiusCm = 100.0 * horizonCm;
  config.bandRadiusCm = {0.5 * horizonCm, 10.0 * horizonCm}; // band 0 is inside the horizon

  auto buildCampaign = [&](bool issueBadPlacement) {
    game::CampaignState campaign(config, field);
    EXPECT_TRUE(campaign.valid());
    const game::FleetId fleet = campaign.addFleet(game::FleetCapability::Research, 1);
    EXPECT_NE(fleet, game::K_INVALID_FLEET_ID);
    game::Command assign;
    assign.type = game::CommandType::AssignTask;
    assign.fleet = fleet;
    assign.properTimeCostSec = 3600.0;
    EXPECT_TRUE(campaign.issueCommand(assign));
    if (issueBadPlacement) {
      game::Command badPlacement;
      badPlacement.type = game::CommandType::PlaceFleet;
      badPlacement.fleet = fleet;
      badPlacement.targetBand = 0;
      EXPECT_FALSE(campaign.issueCommand(badPlacement))
          << "inside-horizon placement must be rejected at issue time";
    }
    campaign.advanceTurns(8);
    return campaign;
  };

  const game::CampaignState withRejectedOrder = buildCampaign(true);
  const game::CampaignState control = buildCampaign(false);
  // The rejected order left no trace: log, tasks, and bytes match a campaign
  // that never issued it.
  EXPECT_EQ(withRejectedOrder.commandLog().size(), control.commandLog().size());
  EXPECT_EQ(withRejectedOrder.serializeState(), control.serializeState());
  EXPECT_EQ(withRejectedOrder.stateDigest(), control.stateDigest());
}

TEST(CampaignHorizonGate, FleetCannotBeStationedInsideTheHorizonAtSetup) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  game::CampaignConfig config;
  config.seed = 3;
  config.secondsPerTurn = 3600.0;
  config.authorityRadiusCm = 100.0 * horizonCm;
  config.bandRadiusCm = {0.5 * horizonCm, 10.0 * horizonCm};
  game::CampaignState campaign(config, field);
  ASSERT_TRUE(campaign.valid());
  EXPECT_EQ(campaign.addFleet(game::FleetCapability::Research, 0), game::K_INVALID_FLEET_ID);
  EXPECT_TRUE(campaign.fleets().empty());
}

TEST(CampaignView, RenderSnapshotTracksSignalsWithoutLeakingEarlyState) {
  const FakeTimeField field;
  game::CampaignState campaign(fakeConfig(), field);
  ASSERT_TRUE(campaign.valid());
  const game::FleetId farFleet = campaign.addFleet(game::FleetCapability::Research, 1);
  ASSERT_NE(farFleet, game::K_INVALID_FLEET_ID);

  game::Command assign;
  assign.type = game::CommandType::AssignTask;
  assign.fleet = farFleet;
  assign.properTimeCostSec = 0.5;
  ASSERT_TRUE(campaign.issueCommand(assign)); // effect turn 5, report lands turn 10

  // While the order is in flight the view shows the signal, not its effect.
  campaign.advanceTurns(3);
  const game::CampaignViewSnapshot inFlight = campaign.renderSnapshot();
  EXPECT_EQ(inFlight.turn, 3);
  ASSERT_EQ(inFlight.ordersInFlight.size(), 1U);
  EXPECT_EQ(inFlight.ordersInFlight.front().fleet, farFleet);
  EXPECT_EQ(inFlight.ordersInFlight.front().effectTurn, 5);
  EXPECT_TRUE(inFlight.reportsInFlight.empty());
  ASSERT_EQ(inFlight.fleets.size(), 1U);
  EXPECT_EQ(inFlight.fleets.front().activeTasks + inFlight.fleets.front().pendingTasks, 0U);

  // After the order lands and the task completes, the report is the signal.
  campaign.advanceTurns(3); // turn 6
  const game::CampaignViewSnapshot reporting = campaign.renderSnapshot();
  EXPECT_TRUE(reporting.ordersInFlight.empty());
  ASSERT_EQ(reporting.reportsInFlight.size(), 1U);
  EXPECT_EQ(reporting.reportsInFlight.front().effectTurn, 10);
  EXPECT_EQ(reporting.fleets.front().completedTasks, 1U);
  EXPECT_TRUE(reporting.intel.empty());

  campaign.advanceTurns(4); // turn 10
  const game::CampaignViewSnapshot arrived = campaign.renderSnapshot();
  EXPECT_TRUE(arrived.reportsInFlight.empty());
  ASSERT_EQ(arrived.intel.size(), 1U);
  EXPECT_EQ(arrived.intel.front().receivedTurn, 10);

  // Band views carry the field the map draws: rates, delays, validity.
  ASSERT_EQ(arrived.bands.size(), 2U);
  EXPECT_TRUE(arrived.bands.at(0).validStation);
  EXPECT_DOUBLE_EQ(arrived.bands.at(0).properTimeRate, 0.1);
  EXPECT_DOUBLE_EQ(arrived.bands.at(0).delayToAuthoritySec, 40.0);
  EXPECT_DOUBLE_EQ(arrived.bands.at(1).properTimeRate, 1.0);
  EXPECT_DOUBLE_EQ(arrived.fleets.front().properTimeRate, 1.0);
  EXPECT_DOUBLE_EQ(arrived.coordinateTimeSec, 10.0);
}

TEST(CampaignView, InvalidBandRendersAsForbiddenZone) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  game::CampaignConfig config;
  config.secondsPerTurn = 3600.0;
  config.authorityRadiusCm = 100.0 * horizonCm;
  config.bandRadiusCm = {0.5 * horizonCm, 10.0 * horizonCm};
  const game::CampaignState campaign(config, field);
  ASSERT_TRUE(campaign.valid());
  const game::CampaignViewSnapshot view = campaign.renderSnapshot();
  EXPECT_DOUBLE_EQ(view.innerBoundaryRadiusCm, horizonCm);
  ASSERT_EQ(view.bands.size(), 2U);
  EXPECT_FALSE(view.bands.at(0).validStation);
  EXPECT_DOUBLE_EQ(view.bands.at(0).properTimeRate, 0.0);
  EXPECT_TRUE(view.bands.at(1).validStation);
  EXPECT_GT(view.authorityProperTimeRate, 0.99);
}

TEST(TaskGraph, PrerequisitesGateActivation) {
  game::TaskGraph graph;
  const game::TaskId first = graph.addTask(1, 1.0);
  const game::TaskId second = graph.addTask(1, 1.0, {first});
  graph.activateEligible();
  EXPECT_EQ(graph.find(first)->state, game::TaskState::Active);
  EXPECT_EQ(graph.find(second)->state, game::TaskState::Pending)
      << "a task must wait for its prerequisites";
  // A large budget cannot leak into a still-pending successor.
  const std::vector<game::TaskId> completedFirst = graph.advanceFleetTasks(1, 10.0);
  ASSERT_EQ(completedFirst.size(), 1U);
  EXPECT_EQ(completedFirst.front(), first);
  EXPECT_EQ(graph.find(second)->state, game::TaskState::Pending);
  graph.activateEligible();
  const std::vector<game::TaskId> completedSecond = graph.advanceFleetTasks(1, 10.0);
  ASSERT_EQ(completedSecond.size(), 1U);
  EXPECT_EQ(completedSecond.front(), second);
}
