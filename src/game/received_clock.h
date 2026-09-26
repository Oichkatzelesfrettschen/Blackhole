/**
 * @file received_clock.h
 * @brief What a node knows of each remote node's clock: the sender's proper
 *        time when its latest arrival left ("received tau"), and how old that
 *        news is ("signal age").
 *
 * A remote clock is never observed directly, only through the last signal
 * that reached here. Received tau is the sender's whole local seconds stamped
 * at emission; the signal age is (now - emitTurn) coordinate turns, which the
 * receiver's own clock experiences as that span times its dtau/dt. Both are
 * pure functions of the arrival record, so the display never peeks at a
 * remote node's present; the same holds for the host's banked energy, which a
 * colony knows only as the value stamped on the host's latest arrival.
 */

#ifndef BLACKHOLE_GAME_RECEIVED_CLOCK_H
#define BLACKHOLE_GAME_RECEIVED_CLOCK_H

#include <cstddef>
#include <cstdint>
#include <vector>

#include "game/event.h"
#include "game/station_node.h"

namespace game {

struct ReceivedClock {
  NodeId sender = K_NO_NODE;
  bool heard = false;               ///< Anything from this sender has arrived.
  std::int64_t emitTurn = -1;       ///< Coordinate turn the latest arrival left.
  std::int64_t arrivalTurn = -1;
  std::int64_t senderProperSec = 0; ///< Received tau: the sender's clock at emission.
  double senderEnergyUnits = 0.0;   ///< The host's banked energy as of that emission.
};

/** @brief Latest arrival per sender at `receiver`, indexed by sender id for
 *         senders below nodeCount. */
[[nodiscard]] inline std::vector<ReceivedClock>
latestReceivedClocks(const std::vector<ArrivalRecord> &arrivals, NodeId receiver,
                     std::size_t nodeCount) {
  std::vector<ReceivedClock> clocks(nodeCount);
  for (std::size_t sender = 0; sender < nodeCount; ++sender) {
    clocks.at(sender).sender = static_cast<NodeId>(sender);
  }
  for (const ArrivalRecord &arrival : arrivals) {
    if (arrival.destination != receiver || arrival.sender >= nodeCount) {
      continue;
    }
    ReceivedClock &clock = clocks.at(arrival.sender);
    // Arrivals are in arrival order; a later arrival can still carry an older
    // emission only if it travelled longer, so the latest emission wins.
    if (!clock.heard || arrival.emitTurn >= clock.emitTurn) {
      clock.heard = true;
      clock.emitTurn = arrival.emitTurn;
      clock.arrivalTurn = arrival.arrivalTurn;
      clock.senderProperSec = arrival.senderProperSecAtEmit;
      clock.senderEnergyUnits = arrival.senderEnergyUnitsAtEmit;
    }
  }
  return clocks;
}

/** @brief Signal age in coordinate seconds at turn `nowTurn`. */
[[nodiscard]] inline double signalAgeCoordinateSec(const ReceivedClock &clock,
                                                   std::int64_t nowTurn, double secondsPerTurn) {
  return clock.heard ? static_cast<double>(nowTurn - clock.emitTurn) * secondsPerTurn : 0.0;
}

/** @brief Signal age as the receiver's own clock measures it. */
[[nodiscard]] inline double signalAgeLocalSec(const ReceivedClock &clock, std::int64_t nowTurn,
                                              double secondsPerTurn, double receiverRate) {
  return signalAgeCoordinateSec(clock, nowTurn, secondsPerTurn) * receiverRate;
}

} // namespace game

#endif // BLACKHOLE_GAME_RECEIVED_CLOCK_H
