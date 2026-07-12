/**
 * @file campaign_session.cpp
 * @brief Default campaign scenario construction and command helpers.
 */

#include "game/campaign_session.h"

#include <cstdint>

#include "game/blackhole_time_field.h"
#include "game/campaign.h"
#include "game/command.h"
#include "game/fleet.h"

namespace game {

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;
constexpr double K_SECONDS_PER_DAY = 86400.0;
constexpr double K_SECONDS_PER_HOUR = 3600.0;

CampaignConfig defaultConfig(const BlackholeTimeField &field, std::uint64_t seed) {
  const double horizonCm = field.horizonRadiusCm();
  CampaignConfig config;
  config.seed = seed;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.authorityRadiusCm = 200.0 * horizonCm;
  config.bandRadiusCm = {3.0 * horizonCm, 10.0 * horizonCm, 50.0 * horizonCm};
  // Objective sized for roughly three order->work->report round trips (each
  // ~300 one-day turns at this scale): reach the target before the deadline.
  config.victoryEnergyUnits = 300.0;
  config.deadlineTurn = 1200;
  config.fleetInitialFuelUnits = 100.0;
  config.fuelPerBandHop = 20.0;
  config.reliabilityWearPerProperDay = 0.002;
  config.reliabilityFloor = 0.5;
  return config;
}

} // namespace

CampaignSession::CampaignSession(std::uint64_t seed)
    : field_(K_M87_MASS_G), state_(defaultConfig(field_, seed), field_) {
  state_.addFleet(FleetCapability::Extraction, 0);
  state_.addFleet(FleetCapability::Research, 0);
  state_.addFleet(FleetCapability::Fabrication, 1);
  state_.addFleet(FleetCapability::Relay, 1);
  state_.addFleet(FleetCapability::Verification, 2);
  state_.addFleet(FleetCapability::Research, 2);
}

bool CampaignSession::issueAssignTask(FleetId fleet, double costHours) {
  Command command;
  command.type = CommandType::AssignTask;
  command.fleet = fleet;
  command.properTimeCostSec = costHours * K_SECONDS_PER_HOUR;
  return state_.issueCommand(command);
}

bool CampaignSession::issuePlaceFleet(FleetId fleet, int targetBand) {
  Command command;
  command.type = CommandType::PlaceFleet;
  command.fleet = fleet;
  command.targetBand = targetBand;
  return state_.issueCommand(command);
}

} // namespace game
