/**
 * @file campaign_session.cpp
 * @brief Default campaign scenario construction and command helpers.
 */

#include "game/campaign_session.h"

#include <cstdint>

#include "game/campaign.h"
#include "game/command.h"
#include "game/fleet.h"
#include "game/kerr_time_field.h"

namespace game {

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;
constexpr double K_SECONDS_PER_DAY = 86400.0;
constexpr double K_SECONDS_PER_HOUR = 3600.0;

CampaignConfig defaultConfig(const KerrTimeField &field, std::uint64_t seed) {
  // Bands are anchored to r_s = 2M, a spin-independent length scale, so a
  // spinning hole keeps the same physical band radii (and the same outer-game
  // economics) as the non-rotating scenario. Band 0 is the ergoregion band:
  // 0.85 r_s = 1.7M sits between the horizon (1.436M at a* = 0.9) and the
  // static limit (2M). Index order tracks physical radius so redeployment fuel,
  // charged per band hop, scales with distance.
  const double rS = field.schwarzschildRadiusCm();
  CampaignConfig config;
  config.seed = seed;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.authorityRadiusCm = 200.0 * rS;
  config.bandRadiusCm = {0.85 * rS, 3.0 * rS, 10.0 * rS, 50.0 * rS};
  // Objective tuned so pure outer-band play falls short (~221 energy) but a
  // fleet committed to the deep prograde ergoregion lane clears it: the
  // frame-dragging bonus is the path to victory, not an optional flourish.
  config.victoryEnergyUnits = 260.0;
  config.deadlineTurn = 1200;
  config.fleetInitialFuelUnits = 100.0;
  config.fuelPerBandHop = 20.0;
  config.reliabilityWearPerProperDay = 0.002;
  config.reliabilityFloor = 0.5;
  // A prograde fleet at the ergoregion floor (depth ~0.53 at 1.7M) yields up
  // to ~1.8x -- the Penrose-flavoured reward for daring the deep prograde lane.
  config.frameDragYieldBonus = 1.5;
  return config;
}

} // namespace

CampaignSession::CampaignSession(std::uint64_t seed, double spinDimensionless)
    : field_(K_M87_MASS_G, spinDimensionless), state_(defaultConfig(field_, seed), field_) {
  // Six specialist fleets across the three outer bands (1/2/3); the ergoregion
  // band (index 0) starts empty -- the player chooses whether to send a scarce
  // fleet into the deep prograde lane for the frame-dragging bonus.
  state_.addFleet(FleetCapability::Extraction, 1);
  state_.addFleet(FleetCapability::Research, 1);
  state_.addFleet(FleetCapability::Fabrication, 2);
  state_.addFleet(FleetCapability::Relay, 2);
  state_.addFleet(FleetCapability::Verification, 3);
  state_.addFleet(FleetCapability::Research, 3);
}

bool CampaignSession::issueAssignTask(FleetId fleet, double costHours) {
  Command command;
  command.type = CommandType::AssignTask;
  command.fleet = fleet;
  command.properTimeCostSec = costHours * K_SECONDS_PER_HOUR;
  return state_.issueCommand(command);
}

bool CampaignSession::issuePlaceFleet(FleetId fleet, int targetBand, OrbitLane lane) {
  Command command;
  command.type = CommandType::PlaceFleet;
  command.fleet = fleet;
  command.targetBand = targetBand;
  command.lane = lane;
  return state_.issueCommand(command);
}

} // namespace game
