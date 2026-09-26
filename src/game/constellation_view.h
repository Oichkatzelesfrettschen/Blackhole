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
  std::uint32_t heldBandCount = 0;   ///< Bands held uncontested (perceived or true, per block).
};

/// One system as the player sees it: static geometry plus perceived control.
/// Its live instability is referee truth and lives in refereeInstability.
struct SystemStanding {
  SystemId id = K_INVALID_SYSTEM_ID;
  double spinDimensionless = 0.0;
  double spinDeficit = 1.0; ///< 1 - |a|, exact near extremal spin.
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
  SystemId transitDestSystem = K_INVALID_SYSTEM_ID; ///< Destination while in transit.
  std::int64_t reportedTurn = 0; ///< Turn the fleet sent the state shown here.
};

/**
 * @brief What the player sees. Every field above the referee block is what the
 *        player's authority knows: the outcome only once news of the decision
 *        has reached it, its own scores as reports have credited them, band
 *        control as intel has delivered it, and its fleets as they last
 *        reported. The referee block is the truth no authority holds; it
 *        exists for harnesses, tests, and the post-game record and is named so
 *        a panel cannot mistake it for knowledge.
 */
struct ConstellationViewSnapshot {
  std::int64_t turn = 0;
  double secondsPerTurn = 0.0;
  CampaignStatus overallStatus = CampaignStatus::Ongoing; ///< Ongoing until the player learns the outcome.
  FactionId winner = K_INVALID_FACTION_ID;                ///< Invalid until the player learns the outcome.
  FactionId playerFaction = K_INVALID_FACTION_ID;
  double victoryEnergyUnits = 0.0;
  double victoryStabilizationUnits = 0.0;
  double victoryControlScore = 0.0;
  std::int64_t deadlineTurn = 0;
  /// The player's standing as its authority credits it: banked energy, known
  /// stabilization and control, perceived held bands; status (Won or Lost)
  /// only once the outcome is known, clearedTurn only for a known win.
  FactionStanding player;
  std::vector<SystemStanding> systems;
  std::vector<ConstellationFleetView> fleets;
  std::vector<InterSystemLink> links;

  // Referee truth -- known to no authority.
  CampaignStatus refereeStatus = CampaignStatus::Ongoing; ///< The player's true outcome.
  FactionId refereeWinner = K_INVALID_FACTION_ID;
  std::vector<FactionStanding> refereeStandings; ///< Every faction's true scores and held bands.
  std::vector<double> refereeInstability;        ///< Each system's true instability, by SystemId.
};

} // namespace game

#endif // BLACKHOLE_GAME_CONSTELLATION_VIEW_H
