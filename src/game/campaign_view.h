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
#include <string>
#include <vector>

#include "game/command.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/station_node.h"

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
  bool admitsOrbit = false;             ///< A bound prograde circular orbit exists here.
  bool stableOrbit = false;             ///< ...and it is stable (at or outside the prograde ISCO).
  bool admitsRetrogradeOrbit = false;   ///< A bound retrograde circular orbit exists here.
  bool stableRetrogradeOrbit = false;   ///< ...and it is stable (at or outside the retrograde ISCO).
  /// dtau/dt of a prograde orbit here, or of a hovering station where no bound
  /// orbit exists (below the marginally bound radius).
  double properTimeRate = 0.0;
  double delayToAuthoritySec = 0.0;     ///< One-way signal delay to the authority station.
  double frameDragRateRadPerSec = 0.0;  ///< Frame-dragging angular velocity (0 without spin).
};

struct FleetView {
  FleetId id = K_INVALID_FLEET_ID;
  FleetCapability capability = FleetCapability::Research;
  int bandIndex = 0;
  double reliability = 1.0;
  double properTimeSec = 0.0;   ///< Accumulated local proper time tau.
  double properTimeRate = 0.0;  ///< Current dtau/dt of the fleet's worldline on its band.
  Observer observer = Observer::CircularOrbitPrograde; ///< Orbiting or hovering.
  bool unstableOrbit = false; ///< On an orbit inside its ISCO, held by station-keeping thrust.
  double fuelUnits = 0.0;       ///< Remaining redeployment budget.
  OrbitLane lane = OrbitLane::Prograde; ///< Orbital direction.
  double yieldMultiplier = 1.0;  ///< Capability yield multiplier.
  bool telemetryCorrupted = false; ///< Reliability below the corruption threshold.
  /// False in a colony's perceived view: the fleet reports to the host, so
  /// reliability, tau, rate, fuel, and task counts are unknown there (zero).
  bool telemetryKnown = true;
  /// False when the viewer cannot place the fleet; bandIndex is then
  /// meaningless. A colony places a fleet only where it last ordered it.
  bool positionKnown = true;
  std::uint32_t pendingTasks = 0;
  std::uint32_t activeTasks = 0;
  std::uint32_t completedTasks = 0;
};

/** @brief A command the player issued that has not yet reached its fleet. */
struct OrderInFlightView {
  CommandType type = CommandType::PlaceFleet;
  FleetId fleet = K_INVALID_FLEET_ID;
  NodeId origin = K_AUTHORITY_NODE; ///< Station the order left from.
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
  bool corrupted = false; ///< Yield was discounted for unreliable telemetry.
};

/** @brief A communicating station: the host or a colony, with its exact
 *         local clock. */
struct NodeView {
  NodeId id = K_AUTHORITY_NODE;
  bool isColony = false;
  double radiusCm = 0.0;
  Observer observer = Observer::Hovering;
  double properTimeRate = 0.0;     ///< The clock's quantized dtau/dt.
  double properTimeSec = 0.0;      ///< Local proper time (display value of the Q48 clock).
  bool dark = false;               ///< Silent: emits and receives nothing.
  std::int64_t techPoints = 0;
  std::int64_t techTier = 0;
  std::int64_t missionProperSec = 0; ///< Colony mission length; 0 = unbounded.
  /// Coordinate turn the values above describe: the present for the viewer's
  /// own station, the emission turn of the latest arrival for a remote one.
  std::int64_t asOfTurn = 0;
  bool heard = true; ///< False for a remote station nothing has arrived from.
};

/** @brief A story event's inbox text, looked up by a notice's payload id. */
struct EventTextView {
  std::uint32_t id = 0;
  std::string name;
  std::string text;
  EventCategory category = EventCategory::Info;
};

struct TechLevelView {
  std::int64_t points = 0;
  std::string name;
};

struct CampaignViewSnapshot {
  /// The station whose knowledge this view holds. The authority's view is the
  /// campaign's full snapshot; a colony's is CampaignState::perceivedSnapshot.
  NodeId perceivedBy = K_AUTHORITY_NODE;
  std::int64_t turn = 0;
  double secondsPerTurn = 0.0;
  double coordinateTimeSec = 0.0;
  CampaignStatus status = CampaignStatus::Ongoing;
  double energyUnits = 0.0;        ///< Banked yield (credited on report arrival).
  double victoryEnergyUnits = 0.0; ///< Win target; zero disables the objective.
  std::int64_t deadlineTurn = 0;   ///< Loss turn; zero disables the deadline.
  // Outcome vector the player weights: energy above, plus the
  // singularity's instability and the stabilization/integrity/speed a deep
  // prograde lane buys against it. All zero when the mechanic is disabled.
  double instability = 0.0;        ///< Current disturbance level; erodes all yield.
  double stabilization = 0.0;      ///< Cumulative containment produced by ergoregion work.
  double victoryStabilizationUnits = 0.0; ///< Alternate win: tame the singularity; 0 = off.
  double fleetIntegrity = 1.0;     ///< Lowest fleet reliability -- the cost the dive pays.
  std::int64_t clearedTurn = 0;    ///< Turn a victory was reached; 0 until won.
  double ergosphereRadiusCm = 0.0; ///< Static limit; equals the horizon without spin.
  double spinDimensionless = 0.0;  ///< Black-hole spin a/M (0 for Schwarzschild).
  double spinDeficit = 1.0;        ///< 1 - |a|, exact near extremal spin.
  Observer authorityObserver = Observer::Hovering; ///< How the authority holds its radius.
  double reliabilityCorruptionThreshold = 0.0; ///< Below this a fleet's reports corrupt; 0 = off.
  double authorityRadiusCm = 0.0;
  double authorityProperTimeRate = 0.0;
  double innerBoundaryRadiusCm = 0.0; ///< Horizon radius; zero for fields without one.
  std::vector<BandView> bands;
  std::vector<FleetView> fleets;
  std::vector<OrderInFlightView> ordersInFlight;
  std::vector<ReportInFlightView> reportsInFlight;
  std::vector<IntelView> intel;
  // Colonies and the story. The tech axis of the outcome is the highest tier
  // any colony holds; victoryTechTier (0 = off) wins outright.
  std::vector<NodeView> nodes;              ///< Host at index 0, then colonies.
  std::vector<ArrivalRecord> arrivals;      ///< Node deliveries that have arrived, in order.
  /// Story signals still travelling; arrivalTurn is the quantized effect turn.
  std::vector<ArrivalRecord> nodeSignalsInFlight;
  std::int64_t colonyReportsInFlight = 0;   ///< Production reports still travelling to the host.
  std::vector<EventTextView> eventTexts;    ///< Story events by id.
  std::vector<TechLevelView> techTiers;     ///< Story tiers by points.
  std::int64_t colonyTechTier = 0;
  std::int64_t victoryTechTier = 0;
  double energyLostToDarkness = 0.0;        ///< Production that reached a dark host.
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_VIEW_H
