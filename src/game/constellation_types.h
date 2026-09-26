/**
 * @file constellation_types.h
 * @brief Value types for the multi-system, multi-faction constellation core.
 *
 * The constellation layers a competitive 4X on the single-hole campaign: several
 * black-hole systems linked by interstellar distance, several factions contesting
 * the orbital bands of each. It reuses the physics primitives (KerrTimeField, the
 * FleetCapability/OrbitLane vocabulary, the shared economy atoms) but keeps its
 * own fleet record so the frozen single-hole CampaignState is untouched.
 *
 * Every container here is a vector kept in ascending-id order, and every
 * identifier is a stable integer, because the constellation's determinism law is
 * stricter than the single hole's: with N factions across M systems, a single
 * unordered iteration would silently diverge the digest. Canonical order is
 * ascending SystemId, then FactionId, then FleetId, everywhere state is touched.
 */

#ifndef BLACKHOLE_GAME_CONSTELLATION_TYPES_H
#define BLACKHOLE_GAME_CONSTELLATION_TYPES_H

#include <cstdint>
#include <vector>

#include "game/campaign_view.h"
#include "game/fleet.h"
#include "game/kerr_time_field.h"

namespace game {

using SystemId = std::uint32_t;
using FactionId = std::uint32_t;

inline constexpr SystemId K_INVALID_SYSTEM_ID = 0xFFFFFFFFU;
inline constexpr FactionId K_INVALID_FACTION_ID = 0;

/** @brief How a faction decides its orders. Scripted takes orders only from an
 *         external command log (the human player, or a test's commitment line);
 *         the rest are deterministic AI policies stepped each turn. */
enum class FactionPolicy : std::uint8_t {
  Scripted = 0,     ///< No AI: orders arrive from outside (player or test).
  Expansionist = 1, ///< Spreads to hold as many uncontested bands as it can reach.
  Extractor = 2,    ///< Concentrates fleets on its highest-rate home bands for energy.
  Contester = 3,    ///< Moves onto the bands a leading rival is believed to hold.
};

[[nodiscard]] const char *factionPolicyName(FactionPolicy policy);

/** @brief One black hole and its orbital board. The field is owned by value
 *         (KerrTimeField is a handful of doubles); systems are built once at
 *         construction and never resized, so SystemId is a stable index. */
struct OrbitalSystem {
  KerrTimeField field;
  double authorityRadiusCm = 0.0;   ///< This system's command origin.
  Observer authorityObserver = Observer::Hovering; ///< The authority's clock.
  std::vector<double> bandRadiusCm; ///< Orbital bands, ascending radius, indexed by bandIndex.
  double instability = 0.0;         ///< Rises each turn; deep prograde work in THIS system contains it.
};

/** @brief A fleet in the constellation. Distinct from the frozen game::Fleet:
 *         it carries a faction and a system, and it can be in interstellar
 *         transit (belonging to no band until it arrives). */
struct ConstellationFleet {
  FleetId id = K_INVALID_FLEET_ID; ///< Unique across the whole constellation.
  FactionId faction = K_INVALID_FACTION_ID;
  SystemId system = K_INVALID_SYSTEM_ID; ///< Current system; the destination while in transit.
  FleetCapability capability = FleetCapability::Research;
  int bandIndex = 0;
  OrbitLane lane = OrbitLane::Prograde;
  Observer observer = Observer::CircularOrbitPrograde; ///< Clock-carrying worldline on its band.
  double reliability = 1.0;
  double properTimeSec = 0.0;        ///< Accumulated local proper time.
  double pendingWorkProperSec = 0.0; ///< Proper time worked since the last yield report.
  double fuelUnits = 0.0;
  bool inTransit = false;             ///< True between systems; holds no band.
  std::int64_t transitArrivalTurn = 0; ///< Turn an in-transit fleet reaches its destination.
  int transitDestBand = 0;            ///< Band it settles onto on arrival.
  OrbitLane transitDestLane = OrbitLane::Prograde;
  /// Worldline it adopts on arrival.
  Observer transitDestObserver = Observer::CircularOrbitPrograde;
};

/** @brief A faction's cumulative outcome across the whole constellation. */
struct FactionState {
  FactionId id = K_INVALID_FACTION_ID;
  FactionPolicy policy = FactionPolicy::Scripted;
  SystemId homeSystem = K_INVALID_SYSTEM_ID;
  double energyUnits = 0.0;        ///< Banked yield (credited on delayed report arrival).
  double stabilizationUnits = 0.0; ///< Containment produced across all systems.
  double controlScore = 0.0;       ///< Cumulative uncontested band-holds -- the breadth axis.
  CampaignStatus status = CampaignStatus::Ongoing;
  std::int64_t clearedTurn = 0; ///< Turn this faction reached a victory; 0 until then.
};

/** @brief An undirected interstellar link: a flat-space separation between two
 *         systems' authority stations. The dominant term in cross-system delay
 *         and travel, since the separation dwarfs either hole's r_s. */
struct InterSystemLink {
  SystemId a = K_INVALID_SYSTEM_ID;
  SystemId b = K_INVALID_SYSTEM_ID;
  double separationCm = 0.0;
};

} // namespace game

#endif // BLACKHOLE_GAME_CONSTELLATION_TYPES_H
