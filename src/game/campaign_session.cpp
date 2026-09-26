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
#include "game/observer.h"

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
  // The objective is sized so the deadline bites: full outer commitment clears
  // it only in the last tenth of the 1200 turns, so the energy race is tense and
  // any dive that drops throughput forfeits it. There is no half-measure -- a
  // fleet or two sent deep banks neither enough energy to win the race nor enough
  // stabilization to take the alternate victory (see the instability block); the
  // two winning lines are full-outer for energy or an all-in dive for
  // stabilization. The value is measured against orbiting outer fleets, whose
  // slower geodesic clocks price each proper hour higher than a hovering clock
  // would: with wins disabled, outer banks about 9% above it by the deadline and
  // the solo dive about 4% below.
  config.victoryEnergyUnits = 3325.0;
  config.deadlineTurn = 1200;
  config.fleetInitialFuelUnits = 100.0;
  config.fuelPerBandHop = 20.0;
  config.reliabilityWearPerProperDay = 0.002;
  config.reliabilityFloor = 0.5;
  // A prograde fleet at the ergoregion floor (depth ~0.53 at 1.7M) yields up
  // to ~1.8x -- the Penrose-flavoured reward for daring the deep prograde lane.
  config.frameDragYieldBonus = 1.5;
  // Capability effects (index order Research/Fabrication/Relay/Verification/
  // Extraction). Extraction and Research produce the energy; Relay, Fabrication,
  // and Verification are support, worth less raw yield but enabling the rest.
  config.capabilityYieldMultiplier = {1.25, 1.0, 0.75, 0.75, 1.5};
  // Signals carry a 40% coordination overhead that a relay on the path removes
  // 30% of per hop, toward the light-speed floor.
  config.signalOverheadFactor = 1.4;
  config.relayDelayFraction = 0.3;
  // Fabrication refuels co-band fleets (enables sustained redeployment); each
  // verification run restores 5% reliability to co-band fleets.
  config.fabricationFuelRestore = 30.0;
  config.verificationReliabilityRestore = 0.05;
  // Telemetry from a fleet worn below 0.9 reliability banks only 40% of its
  // yield until verification restores it -- the deep dive's hazard.
  config.reliabilityCorruptionThreshold = 0.9;
  config.corruptedYieldFraction = 0.4;
  // Instability: the singularity destabilizes over the campaign,
  // eroding all yield. Uncontained outer play still clears the objective (it
  // survives to the deadline) but slows as the disturbance grows; a sustained
  // prograde ergoregion presence produces containment that holds instability
  // down, clearing sooner and banking a stabilization score -- bought by wearing
  // the deep fleet's integrity. No single line dominates: outer keeps its fleets
  // whole, the dive clears fast and stabilizes. Tuned against campaign_sim.
  config.instabilityPerTurn = 0.02;
  config.instabilityYieldPenaltyPerUnit = 0.04;
  config.ergoContainmentPerProperDay = 0.12;
  config.ergoHazardWearPerProperDay = 0.15;
  // Stabilization is a sacrifice: a deep prograde fleet keeps only a tenth of its
  // yield, so the stabilizing line banks less raw energy than pure outer play --
  // it is a rival objective, not a bonus. Reaching 8 units of cumulative
  // stabilization is an ALTERNATE victory (tame the singularity), a path only a
  // fleet-wide commitment reaches and only by forgoing the energy win. Two ends,
  // one choice.
  config.containmentYieldRetention = 0.1;
  config.victoryStabilizationUnits = 8.0;
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

bool CampaignSession::issuePlaceFleet(FleetId fleet, int targetBand, OrbitLane lane,
                                      StationKeeping station) {
  Command command;
  command.type = CommandType::PlaceFleet;
  command.fleet = fleet;
  command.targetBand = targetBand;
  command.lane = lane;
  command.station = station;
  return state_.issueCommand(command);
}

} // namespace game
