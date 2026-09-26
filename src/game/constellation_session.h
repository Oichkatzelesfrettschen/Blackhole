/**
 * @file constellation_session.h
 * @brief Owns one live constellation and the canonical two-system contest scenario.
 *
 * The default scenario is a tight cluster of two spinning holes tens of light-days
 * apart -- close enough that orders, reports, and intel cross between them within a
 * campaign, unlike the megaparsec gulf between real galaxies. The player holds one
 * system, an Expansionist rival the other. The rival, left alone, fans its fleets
 * across both systems' bands and wins by domination before either the energy or the
 * stabilization race can complete, so the player must spend fleets contesting it.
 */

#ifndef BLACKHOLE_GAME_CONSTELLATION_SESSION_H
#define BLACKHOLE_GAME_CONSTELLATION_SESSION_H

#include <cstdint>

#include "game/constellation.h"
#include "game/constellation_types.h"

namespace game {

class ConstellationSession {
public:
  /** @brief The default two-system scenario; the rival runs `rivalPolicy`,
   *         Expansionist unless a caller sweeps rival behavior. */
  explicit ConstellationSession(std::uint64_t seed = 1,
                                FactionPolicy rivalPolicy = FactionPolicy::Expansionist);

  [[nodiscard]] Constellation &constellation() { return constellation_; }
  [[nodiscard]] const Constellation &constellation() const { return constellation_; }

  [[nodiscard]] FactionId player() const { return player_; }
  [[nodiscard]] FactionId rival() const { return rival_; }

  /** @brief Order one of the player's fleets, intra-system or interstellar,
   *         in orbit by default or hovering on thrust. */
  bool movePlayerFleet(FleetId fleet, SystemId targetSystem, int targetBand,
                       OrbitLane lane = OrbitLane::Prograde,
                       StationKeeping station = StationKeeping::Orbit);

private:
  Constellation constellation_;
  FactionId player_ = K_INVALID_FACTION_ID;
  FactionId rival_ = K_INVALID_FACTION_ID;
};

/** @brief The default scenario config, exposed so tests and the sim can inspect
 *         the victory thresholds without reaching into a live session. */
[[nodiscard]] ConstellationConfig defaultConstellationConfig(std::uint64_t seed);

} // namespace game

#endif // BLACKHOLE_GAME_CONSTELLATION_SESSION_H
