/**
 * @file constellation_view.h
 * @brief Immutable render-facing view of the constellation for the UI layer.
 *
 * The galaxy map and faction panels consume plain values copied out of the
 * Constellation -- no pointers into its storage -- so the UI can hold a snapshot
 * across frames while the campaign advances. As with the single hole's
 * CampaignViewSnapshot this is a VIEW contract, separate from serializeState():
 * fields exist here because a panel draws them and may grow per UI slice without
 * touching the byte format.
 */

#ifndef BLACKHOLE_GAME_CONSTELLATION_VIEW_H
#define BLACKHOLE_GAME_CONSTELLATION_VIEW_H

#include <cstdint>
#include <vector>

#include "game/campaign_view.h"
#include "game/constellation_types.h"
#include "game/fleet.h"
#include "game/observer.h"

namespace game {

struct FactionStanding {
  FactionId id = K_INVALID_FACTION_ID;
  FactionPolicy policy = FactionPolicy::Scripted;
  SystemId homeSystem = K_INVALID_SYSTEM_ID;
  double energyUnits = 0.0;
  double stabilizationUnits = 0.0;
  double controlScore = 0.0;
  CampaignStatus status = CampaignStatus::Ongoing;
  std::int64_t clearedTurn = 0;
  std::uint32_t fleetCount = 0;      ///< Fleets this faction has (including in transit).
  std::uint32_t heldBandCount = 0;   ///< Bands the player's authority believes it holds.
};

struct SystemStanding {
  SystemId id = K_INVALID_SYSTEM_ID;
  double instability = 0.0;
  double spinDimensionless = 0.0;
  std::uint32_t bandCount = 0;
  /// Controller per band as the player's authority last learned it; invalid =
  /// unknown, empty, or contested.
  std::vector<FactionId> bandController;
};

struct ConstellationFleetView {
  FleetId id = K_INVALID_FLEET_ID;
  FactionId faction = K_INVALID_FACTION_ID;
  SystemId system = K_INVALID_SYSTEM_ID;
  FleetCapability capability = FleetCapability::Research;
  int bandIndex = 0;
  OrbitLane lane = OrbitLane::Prograde;
  Observer observer = Observer::CircularOrbitPrograde;
  double reliability = 1.0;
  bool inTransit = false;
  std::int64_t transitArrivalTurn = 0;
  std::int64_t reportedTurn = 0; ///< Turn the fleet sent the state shown here.
};

struct ConstellationViewSnapshot {
  std::int64_t turn = 0;
  double secondsPerTurn = 0.0;
  CampaignStatus overallStatus = CampaignStatus::Ongoing;
  FactionId winner = K_INVALID_FACTION_ID;
  FactionId playerFaction = K_INVALID_FACTION_ID;
  double victoryEnergyUnits = 0.0;
  double victoryStabilizationUnits = 0.0;
  double victoryControlScore = 0.0;
  std::int64_t deadlineTurn = 0;
  std::vector<FactionStanding> factions;
  std::vector<SystemStanding> systems;
  std::vector<ConstellationFleetView> fleets;
  std::vector<InterSystemLink> links;
};

} // namespace game

#endif // BLACKHOLE_GAME_CONSTELLATION_VIEW_H
