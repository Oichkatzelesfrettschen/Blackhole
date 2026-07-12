/**
 * @file campaign_session.cpp
 * @brief Default campaign scenario construction and command helpers.
 */

#include "game/campaign_session.h"

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

CampaignConfig defaultConfig(const BlackholeTimeField &field) {
  const double horizonCm = field.horizonRadiusCm();
  CampaignConfig config;
  config.seed = 1;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.authorityRadiusCm = 200.0 * horizonCm;
  config.bandRadiusCm = {3.0 * horizonCm, 10.0 * horizonCm, 50.0 * horizonCm};
  return config;
}

} // namespace

CampaignSession::CampaignSession()
    : field_(K_M87_MASS_G), state_(defaultConfig(field_), field_) {
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
