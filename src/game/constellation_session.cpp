/**
 * @file constellation_session.cpp
 * @brief Default two-system contest scenario and player command helpers.
 */

#include "game/constellation_session.h"

#include <cstdint>
#include <vector>

#include "game/constellation.h"
#include "game/constellation_types.h"
#include "game/fleet.h"
#include "game/kerr_time_field.h"
#include "game/observer.h"

namespace game {

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;
constexpr double K_SGRA_MASS_G = 4.1e6 * K_SOLAR_MASS_G;
constexpr double K_SECONDS_PER_DAY = 86400.0;
constexpr double K_C_CM_PER_S = 2.99792458e10;
constexpr double K_SPIN = 0.9;

// Bands anchored to r_s = 2M (spin-independent) as in the single-hole scenario:
// an ergoregion band at 0.85 r_s, then 3/10/50 r_s. The authority sits far out.
std::vector<double> bandsForRadius(double schwarzschildRadiusCm) {
  return {0.85 * schwarzschildRadiusCm, 3.0 * schwarzschildRadiusCm, 10.0 * schwarzschildRadiusCm,
          50.0 * schwarzschildRadiusCm};
}

SystemSpec systemSpec(double blackHoleMassG) {
  const KerrTimeField field(blackHoleMassG, K_SPIN);
  const double rS = field.schwarzschildRadiusCm();
  return SystemSpec{.blackHoleMassG = blackHoleMassG,
                    .spinDimensionless = K_SPIN,
                    .authorityRadiusCm = 200.0 * rS,
                    .bandRadiusCm = bandsForRadius(rS)};
}

} // namespace

ConstellationConfig defaultConstellationConfig(std::uint64_t seed) {
  ConstellationConfig config;
  config.seed = seed;
  config.secondsPerTurn = K_SECONDS_PER_DAY;
  config.systems = {systemSpec(K_M87_MASS_G), systemSpec(K_SGRA_MASS_G)};
  // A 40 light-day separation: crossing it -- for a signal or a fleet -- costs
  // tens of turns, so a rival's expansion in the far system is both learned about
  // late and answered late. That lag is the strategic price of a two-system map.
  const double separationCm = 40.0 * K_SECONDS_PER_DAY * K_C_CM_PER_S;
  config.links = {InterSystemLink{.a = 0, .b = 1, .separationCm = separationCm}};

  // Three ways to win, tuned against constellation_sim so that domination
  // (control) is the binding threat against the Expansionist rival. A
  // concentrated player -- racing energy from home, or diving every fleet for
  // stabilization -- lets that rival fan out and cross the control threshold
  // first (turns 786 and 584), losing. Only a fortress line that holds all four
  // home bands both denies the rival (stalling it below the threshold) and banks
  // enough control to win itself (turn 1325), so contesting is forced rather than
  // optional. The energy and stabilization targets sit past what a concentrated
  // line reaches before the rival's clock fires, so neither is a shortcut around
  // the contest. This shape is proven against the Expansionist policy, which
  // over-extends into the player's system; robustness to a hold-home rival is a
  // later balancing pass.
  config.victoryEnergyUnits = 60000.0;
  config.victoryStabilizationUnits = 60.0;
  config.victoryControlScore = 1490.0;
  config.deadlineTurn = 1400;

  config.workProperHoursPerReport = 24.0;
  // Fuel is generous in this slice so time, not logistics, is the binding cost of
  // spreading across systems; a fuel economy is future tuning.
  config.fleetInitialFuelUnits = 1.0e6;
  config.fuelPerBandHop = 20.0;
  config.interSystemTravelSpeedFraction = 0.5;
  config.interSystemTravelFuelUnits = 50.0;

  config.capabilityYieldMultiplier = {1.25, 1.0, 0.75, 0.75, 1.5};
  config.reliabilityWearPerProperDay = 0.002;
  config.reliabilityFloor = 0.5;
  config.frameDragYieldBonus = 1.5;
  config.instabilityPerTurn = 0.02;
  config.instabilityYieldPenaltyPerUnit = 0.04;
  config.ergoContainmentPerProperDay = 0.12;
  config.ergoHazardWearPerProperDay = 0.15;
  config.containmentYieldRetention = 0.1;
  config.controlPointsPerBandPerTurn = 1.0;
  return config;
}

ConstellationSession::ConstellationSession(std::uint64_t seed, FactionPolicy rivalPolicy)
    : constellation_(defaultConstellationConfig(seed)),
      // The player holds system 0; the rival (Expansionist by default) holds system 1. The
      // player is registered first, so overallStatus reports the player's fate.
      player_(constellation_.addFaction(FactionPolicy::Scripted, 0)),
      rival_(constellation_.addFaction(rivalPolicy, 1)) {
  // Four player specialists start on system 0's outer bands (1/2/3), with a spare
  // on band 1 the player can dive or send to contest the rival.
  constellation_.addFleet(player_, 0, FleetCapability::Extraction, 1);
  constellation_.addFleet(player_, 0, FleetCapability::Research, 1);
  constellation_.addFleet(player_, 0, FleetCapability::Verification, 2);
  constellation_.addFleet(player_, 0, FleetCapability::Fabrication, 3);

  // Four rival fleets start stacked on system 1's band 1; the Expansionist policy
  // fans them out across both systems' bands over the following turns.
  constellation_.addFleet(rival_, 1, FleetCapability::Extraction, 1);
  constellation_.addFleet(rival_, 1, FleetCapability::Research, 1);
  constellation_.addFleet(rival_, 1, FleetCapability::Fabrication, 1);
  constellation_.addFleet(rival_, 1, FleetCapability::Relay, 1);
}

bool ConstellationSession::movePlayerFleet(FleetId fleet, SystemId targetSystem, int targetBand,
                                           OrbitLane lane, StationKeeping station) {
  return constellation_.issueCommand(
      player_, ConstellationCommand{.fleet = fleet,
                                    .targetSystem = targetSystem,
                                    .targetBand = targetBand,
                                    .lane = lane,
                                    .station = station});
}

} // namespace game
