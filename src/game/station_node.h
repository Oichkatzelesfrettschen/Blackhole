/**
 * @file station_node.h
 * @brief Communicating stations -- the host at the authority radius and the
 *        colonies -- with their exact local clocks and what has reached them.
 *
 * A node is a place signals leave from and arrive at. Each carries a Q48
 * ObserverClock at its worldline's dtau/dt, its story flags, its counters,
 * and, per sender, the latest arrival it has received: everything a story
 * trigger at that node may read. A colony additionally produces energy on its
 * own clock: every local tick of its mission window ships a production report
 * to the host, banked when it arrives and lost if the host has gone dark.
 */

#ifndef BLACKHOLE_GAME_STATION_NODE_H
#define BLACKHOLE_GAME_STATION_NODE_H

#include <array>
#include <cstdint>
#include <vector>

#include "game/event.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/observer_clock.h"

namespace game {

/** @brief A colony's placement and charter. */
struct ColonyConfig {
  int bandIndex = 0;
  Observer observer = Observer::CircularOrbitPrograde;
  std::int64_t localTickSec = 3600;   ///< Local production shift, in local seconds.
  double energyPerTick = 0.0;         ///< Energy each local tick ships to the host.
  std::int64_t missionProperSec = 0;  ///< Local mission length; the colony goes dark after it. 0 = unbounded.
};

/** @brief The latest arrival of each payload kind a node has received from
 *         one sender. Turns are -1 until something arrives. */
struct ReceivedFromNode {
  std::array<std::int64_t, 2> lastArrivalTurn{{-1, -1}}; ///< Indexed by EmitKind.
  std::array<std::int64_t, 2> count{{0, 0}};             ///< Indexed by EmitKind.
  // The sender as its latest-emitted arrival of any kind (packets, notices,
  // and a colony's production reports) stamped it: all a station knows of a
  // remote one's present.
  std::int64_t lastEmitTurn = -1;          ///< Emission turn of that arrival; -1 until one lands.
  std::int64_t lastSenderProperSec = 0;    ///< Sender's local clock at that emission.
  std::int64_t lastSenderTechPoints = 0;   ///< Sender's tech points at that emission.
  double lastSenderEnergyUnits = 0.0;      ///< Host's banked energy at that emission (host senders).
};

struct StationNode {
  NodeId id = K_AUTHORITY_NODE;
  double radiusCm = 0.0;
  Observer observer = Observer::Hovering;
  ObserverClock clock;
  std::uint64_t flags = 0;          ///< Bit i = story flag i; bit K_DARK_FLAG = dark.
  std::int64_t techPoints = 0;
  std::int64_t packetsEmitted = 0;  ///< Tech packets this node has sent.
  std::vector<ReceivedFromNode> received; ///< Indexed by sender node id.
  bool isColony = false;
  ColonyConfig colony{};            ///< Meaningful when isColony.

  [[nodiscard]] bool dark() const { return (flags & (std::uint64_t{1} << K_DARK_FLAG)) != 0; }
};

/** @brief A node-to-node delivery that reached its destination: the feed the
 *         inbox, the received clocks, and the tech list read. */
struct ArrivalRecord {
  EmitKind kind = EmitKind::Notice;
  EventCategory category = EventCategory::Info;
  NodeId sender = K_AUTHORITY_NODE;
  NodeId destination = K_AUTHORITY_NODE;
  std::int64_t emitTurn = 0;
  std::int64_t arrivalTurn = 0;
  std::int64_t senderProperSecAtEmit = 0; ///< Sender's whole local seconds at emission.
  /// The host's banked energy when it sent this (zero from a colony): what a
  /// colony can know of the host's economy, and only as of that emission.
  double senderEnergyUnitsAtEmit = 0.0;
  std::int64_t senderTechPointsAtEmit = 0; ///< Sender's tech points when it sent this.
  std::uint32_t payloadIndex = 0; ///< Tech packet ordinal from its sender, or the notice's event id.
  /// The replying fleet when sender is K_NO_NODE (a fizzled order's notice).
  FleetId fleet = K_INVALID_FLEET_ID;
  std::int64_t techPoints = 0;
};

} // namespace game

#endif // BLACKHOLE_GAME_STATION_NODE_H
