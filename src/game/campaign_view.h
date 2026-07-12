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

/** @brief One orbital band as the map draws it. rate/delay are filled only
 *         when the band is a valid station radius; an invalid band (at or
 *         inside the horizon) renders as a forbidden zone. */
struct BandView {
  int index = 0;
  double radiusCm = 0.0;
  bool validStation = false;
  double properTimeRate = 0.0;       ///< dtau/dt on this band.
  double delayToAuthoritySec = 0.0;  ///< One-way signal delay to the authority station.
};

struct FleetView {
  FleetId id = K_INVALID_FLEET_ID;
  FleetCapability capability = FleetCapability::Research;
  int bandIndex = 0;
  double reliability = 1.0;
  double properTimeSec = 0.0;   ///< Accumulated local proper time tau.
  double properTimeRate = 0.0;  ///< Current dtau/dt (the fleet's band rate).
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

/** @brief What the authority station has learned so far. */
struct IntelView {
  std::int64_t receivedTurn = 0;
  std::int64_t completedTurn = 0;
  TaskId task = K_INVALID_TASK_ID;
  FleetId fleet = K_INVALID_FLEET_ID;
};

struct CampaignViewSnapshot {
  std::int64_t turn = 0;
  double secondsPerTurn = 0.0;
  double coordinateTimeSec = 0.0;
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
