/**
 * @file perceived_view.cpp
 * @brief A station's view of the campaign: static geometry, its own state,
 *        and everything else only as it has arrived.
 */

#include <cstdint>
#include <optional>
#include <vector>

#include "game/campaign.h"
#include "game/campaign_view.h"
#include "game/command.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/received_clock.h"
#include "game/station_node.h"

namespace game {

namespace {

/** @brief The observer's latest placement order for `fleet`, counted from its
 *         effect turn; nullopt when the observer never sent one. */
std::optional<Command> lastPlacement(const std::vector<LoggedCommand> &log, NodeId observer,
                                     FleetId fleet, std::int64_t now) {
  std::optional<Command> placement;
  std::int64_t latestEffect = -1;
  for (const LoggedCommand &logged : log) {
    const Command &command = logged.command;
    if (command.type == CommandType::PlaceFleet && command.originNode == observer &&
        command.fleet == fleet && logged.effectTurn <= now &&
        logged.effectTurn >= latestEffect) {
      latestEffect = logged.effectTurn;
      placement = command;
    }
  }
  return placement;
}

void blankTelemetry(FleetView &fleet) {
  fleet.telemetryKnown = false;
  fleet.reliability = 0.0;
  fleet.properTimeSec = 0.0;
  fleet.properTimeRate = 0.0;
  fleet.fuelUnits = 0.0;
  fleet.telemetryCorrupted = false;
  fleet.unstableOrbit = false;
  fleet.pendingTasks = 0;
  fleet.activeTasks = 0;
  fleet.completedTasks = 0;
}

} // namespace

CampaignViewSnapshot CampaignState::perceivedSnapshot(NodeId observer) const {
  CampaignViewSnapshot view = renderSnapshot();
  if (observer == K_AUTHORITY_NODE || observer >= nodes_.size()) {
    return view;
  }
  view.perceivedBy = observer;
  const std::int64_t now = clock_.turn();

  // Remote stations only as their latest arrival here stamped them.
  const std::vector<ReceivedClock> received =
      latestReceivedClocks(arrivals_, observer, nodes_.size());
  for (NodeView &node : view.nodes) {
    if (node.id == observer) {
      continue;
    }
    const ReceivedClock &clock = received.at(node.id);
    node.heard = clock.heard;
    node.asOfTurn = clock.heard ? clock.emitTurn : 0;
    node.properTimeSec = clock.heard ? static_cast<double>(clock.senderProperSec) : 0.0;
    node.dark = false; // silence is inferred by the story, never observed
    node.techPoints = 0;
    node.techTier = 0;
  }

  // The host's ledger: its bank as last stamped, nothing of its present.
  const ReceivedClock &host = received.at(K_AUTHORITY_NODE);
  view.energyUnits = host.heard ? host.senderEnergyUnits : 0.0;
  view.energyLostToDarkness = 0.0;
  view.instability = 0.0;
  view.stabilization = 0.0;
  view.fleetIntegrity = 0.0;
  view.status = CampaignStatus::Ongoing;
  view.clearedTurn = 0;
  view.intel.clear();
  view.reportsInFlight.clear();
  std::erase_if(view.ordersInFlight,
                [observer](const OrderInFlightView &order) { return order.origin != observer; });
  std::erase_if(view.nodeSignalsInFlight,
                [observer](const ArrivalRecord &signal) { return signal.sender != observer; });
  std::erase_if(view.arrivals,
                [observer](const ArrivalRecord &arrival) { return arrival.destination != observer; });

  // Fleets report to the host: no telemetry here, and a position only where
  // this station last sent them.
  for (FleetView &fleet : view.fleets) {
    blankTelemetry(fleet);
    const std::optional<Command> placement = lastPlacement(commandLog_, observer, fleet.id, now);
    fleet.positionKnown = placement.has_value();
    fleet.bandIndex = placement.has_value() ? placement->targetBand : 0;
    fleet.lane = placement.has_value() ? placement->lane : OrbitLane::Prograde;
    fleet.observer = placement.has_value() ? observerFor(placement->lane, placement->station)
                                           : Observer::Hovering;
  }
  return view;
}

} // namespace game
