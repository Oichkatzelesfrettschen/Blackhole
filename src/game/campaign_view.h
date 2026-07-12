/**
 * @file campaign_view.h
 * @brief Immutable render-facing view of the campaign for the UI layer.
 *
 * CampaignViewSnapshot is what the strategic map and campaign panels consume:
 * plain values copied out of CampaignState, no pointers or references into
 * campaign storage, so the UI can hold a snapshot across frames while the
 * campaign advances. It is a VIEW contract, distinct from serializeState()
 * (the byte-level determinism artifact): fields here exist because a panel
 * draws them, and the struct may grow per UI slice without touching the
 * serialization format.
 */

#ifndef BLACKHOLE_GAME_CAMPAIGN_VIEW_H
#define BLACKHOLE_GAME_CAMPAIGN_VIEW_H

#include <cstdint>
#include <vector>

#include "game/command.h"
#include "game/fleet.h"

namespace game {

/** @brief Terminal outcomes latch: the first Won/Lost evaluation sticks even
 *         though coordinate time keeps flowing afterwards. */
enum class CampaignStatus : std::uint8_t {
  Ongoing = 0,
  Won = 1,  ///< Banked energy reached the victory target by the deadline.
  Lost = 2, ///< The deadline passed first.
};

/** @brief One orbital band as the map draws it. rate/delay are filled only
 *         when the band is a valid station radius; an invalid band (at or
 *         inside the horizon) renders as a forbidden zone. */
struct BandView {
  int index = 0;
  double radiusCm = 0.0;
  bool validStation = false;
  bool insideErgosphere = false;        ///< Inside the static limit: retrograde forbidden.
  double properTimeRate = 0.0;          ///< dtau/dt on this band.
  double delayToAuthoritySec = 0.0;     ///< One-way signal delay to the authority station.
  double frameDragRateRadPerSec = 0.0;  ///< Frame-dragging angular velocity (0 without spin).
};

struct FleetView {
  FleetId id = K_INVALID_FLEET_ID;
  FleetCapability capability = FleetCapability::Research;
  int bandIndex = 0;
  double reliability = 1.0;
  double properTimeSec = 0.0;   ///< Accumulated local proper time tau.
  double properTimeRate = 0.0;  ///< Current dtau/dt (the fleet's band rate).
  double fuelUnits = 0.0;       ///< Remaining redeployment budget.
  OrbitLane lane = OrbitLane::Prograde; ///< Orbital direction.
  std::uint32_t pendingTasks = 0;
  std::uint32_t activeTasks = 0;
  std::uint32_t completedTasks = 0;
};

/** @brief A command the player issued that has not yet reached its fleet. */
struct OrderInFlightView {
  CommandType type = CommandType::PlaceFleet;
  FleetId fleet = K_INVALID_FLEET_ID;
  std::int64_t issueTurn = 0;
  std::int64_t effectTurn = 0;
};

/** @brief A completion report travelling back to the authority station. The
 *         map may draw the signal; the intel log gains it only on arrival. */
struct ReportInFlightView {
  TaskId task = K_INVALID_TASK_ID;
  FleetId fleet = K_INVALID_FLEET_ID;
  std::int64_t completedTurn = 0;
  std::int64_t effectTurn = 0;
};

/** @brief What the authority station has learned so far. Yield appears here
 *         and nowhere earlier: energy is banked on arrival, not completion. */
struct IntelView {
  std::int64_t receivedTurn = 0;
  std::int64_t completedTurn = 0;
  TaskId task = K_INVALID_TASK_ID;
  FleetId fleet = K_INVALID_FLEET_ID;
  double yieldUnits = 0.0;
};

struct CampaignViewSnapshot {
  std::int64_t turn = 0;
  double secondsPerTurn = 0.0;
  double coordinateTimeSec = 0.0;
  CampaignStatus status = CampaignStatus::Ongoing;
  double energyUnits = 0.0;        ///< Banked yield (credited on report arrival).
  double victoryEnergyUnits = 0.0; ///< Win target; zero disables the objective.
  std::int64_t deadlineTurn = 0;   ///< Loss turn; zero disables the deadline.
  double ergosphereRadiusCm = 0.0; ///< Static limit; equals the horizon without spin.
  double spinDimensionless = 0.0;  ///< Black-hole spin a/M (0 for Schwarzschild).
  double authorityRadiusCm = 0.0;
  double authorityProperTimeRate = 0.0;
  double innerBoundaryRadiusCm = 0.0; ///< Horizon radius; zero for fields without one.
  std::vector<BandView> bands;
  std::vector<FleetView> fleets;
  std::vector<OrderInFlightView> ordersInFlight;
  std::vector<ReportInFlightView> reportsInFlight;
  std::vector<IntelView> intel;
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_VIEW_H
