/**
 * @file command.h
 * @brief Player commands: the campaign's only mutation input besides advanceTurn.
 */

#ifndef BLACKHOLE_GAME_COMMAND_H
#define BLACKHOLE_GAME_COMMAND_H

#include <cstdint>

#include "game/fleet.h"

namespace game {

enum class CommandType : std::uint8_t {
  PlaceFleet = 0, ///< Move a fleet to another orbital band.
  AssignTask = 1, ///< Contract a new task to a fleet.
};

struct Command {
  CommandType type = CommandType::PlaceFleet;
  FleetId fleet = K_INVALID_FLEET_ID;
  int targetBand = 0;                   ///< PlaceFleet: destination band index.
  OrbitLane lane = OrbitLane::Prograde; ///< PlaceFleet: orbital direction to adopt.
  StationKeeping station = StationKeeping::Orbit; ///< PlaceFleet: orbit (geodesic) or hover (ZAMO).
  double properTimeCostSec = 0.0;       ///< AssignTask: local proper-time cost.
};

} // namespace game

#endif // BLACKHOLE_GAME_COMMAND_H
