/**
 * @file perceived_view.cpp
 * @brief A station's view of the campaign: static geometry, its own state,
 *        and everything else only as it has arrived.
 */

#include <algorithm>
#include <cstdint>
#include <optional>
#include <vector>

#include "game/campaign.h"
#include "game/campaign_view.h"
#include "game/command.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/observer.h"
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
  if (observer >= nodes_.size()) {
    return view;
  }
  view.perceivedBy = observer;
  const std::int64_t now = clock_.turn();

  // Remote stations only as their latest-emitted arrival here stamped them.
  const StationNode &self = nodes_.at(observer);
  for (NodeView &node : view.nodes) {
    if (node.id == observer) {
      continue;
    }
    const ReceivedFromNode &word = self.received.at(node.id);
    node.heard = word.lastEmitTurn >= 0;
    node.asOfTurn = node.heard ? word.lastEmitTurn : 0;
    node.properTimeSec = node.heard ? static_cast<double>(word.lastSenderProperSec) : 0.0;
    node.techPoints = node.heard ? word.lastSenderTechPoints : 0;
    node.techTier = std::ranges::count_if(config_.story.techTiers, [&node](const TechLevel &level) {
      return level.points <= node.techPoints;
    });
    node.dark = false; // silence is inferred by the story, never observed
  }
  // The tech axis as this station knows it: its own tier if it is a colony,
  // else the best tier any colony has reported.
  view.colonyTechTier = 0;
  for (const NodeView &node : view.nodes) {
    if (node.isColony) {
      view.colonyTechTier = std::max(view.colonyTechTier, node.techTier);
    }
  }
  std::erase_if(view.nodeSignalsInFlight,
                [observer](const ArrivalRecord &signal) { return signal.sender != observer; });
  std::erase_if(view.arrivals,
                [observer](const ArrivalRecord &arrival) { return arrival.destination != observer; });
  if (observer == K_AUTHORITY_NODE) {
    // The host's own ledger, intel, and fleet reports are host-local truth.
    return view;
  }

  // At a colony, the host's ledger exists only as its bank last stamped.
  const ReceivedFromNode &host = self.received.at(K_AUTHORITY_NODE);
  view.energyUnits = host.lastEmitTurn >= 0 ? host.lastSenderEnergyUnits : 0.0;
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
