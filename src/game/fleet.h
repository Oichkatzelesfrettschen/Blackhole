/**
 * @file fleet.h
 * @brief Fleets of specialized intelligences and their stable identifiers.
 *
 * Fleets reference tasks by stable TaskId values only -- never by pointer or
 * reference into task storage -- so a Fleet is trivially copyable and the
 * campaign serialization stays pointer-free. The task graph owns task storage.
 */

#ifndef BLACKHOLE_GAME_FLEET_H
#define BLACKHOLE_GAME_FLEET_H

#include <cstdint>
#include <vector>

namespace game {

using FleetId = std::uint32_t;
using TaskId = std::uint32_t;

inline constexpr FleetId K_INVALID_FLEET_ID = 0;
inline constexpr TaskId K_INVALID_TASK_ID = 0;

enum class FleetCapability : std::uint8_t {
  Research = 0,     ///< Discovers orbital phenomena, reduces uncertainty.
  Fabrication = 1,  ///< Builds relays, habitats, extractors, observatories.
  Relay = 2,        ///< Improves information flow (never faster than light).
  Verification = 3, ///< Checks claims, detects corrupted telemetry.
  Extraction = 4,   ///< Harvests near-horizon resources under time pressure.
};

[[nodiscard]] const char *capabilityName(FleetCapability capability);

struct Fleet {
  FleetId id = K_INVALID_FLEET_ID;
  FleetCapability capability = FleetCapability::Research;
  int bandIndex = 0;            ///< Index into the campaign's orbital band table.
  double reliability = 1.0;     ///< Degrades with proper time worked; scales task yield.
  double properTimeSec = 0.0;   ///< Accumulated local proper time tau.
  double fuelUnits = 0.0;       ///< Redeployment budget; charged per band hop at effect time.
  std::vector<TaskId> assignedTasks;
};

/** @brief Accrues one coordinate turn of local proper time on the fleet:
 *         tau += properTimeRate * secondsPerTurn. */
void accrueProperTime(Fleet &fleet, double properTimeRate, double secondsPerTurn);

} // namespace game

#endif // BLACKHOLE_GAME_FLEET_H
