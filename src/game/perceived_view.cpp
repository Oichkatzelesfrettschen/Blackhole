/**
 * @file perceived_view.cpp
 * @brief A station's view of the campaign: static geometry, its own state,
 *        and everything else only as it has arrived.
 */

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <numeric>
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

double CampaignState::estimatedDelaySec(double fromRadiusCm, double toRadiusCm) const {
  if (fromRadiusCm == toRadiusCm) {
    return 0.0;
  }
  return field_->signalDelaySec(fromRadiusCm, toRadiusCm) *
         std::max(1.0, config_.signalOverheadFactor);
}

std::vector<CampaignState::OrderBelief> CampaignState::orderBeliefs(NodeId observer) const {
  std::vector<OrderBelief> beliefs(commandLog_.size());
  const double originCm = nodes_.at(observer).radiusCm;
  // The longest the order could take to reach a fleet on any band.
  const std::int64_t worstTurns = std::accumulate(
      config_.bandRadiusCm.begin(), config_.bandRadiusCm.end(), std::int64_t{1},
      [&](std::int64_t worst, double bandCm) {
        return std::max(worst, clock_.ceilTurns(estimatedDelaySec(originCm, bandCm)));
      });
  // Where the observer believes a fleet is at `turn`: the target of its latest
  // placement believed complete by then.
  const auto believedBand = [&](FleetId fleet, std::int64_t turn,
                                std::size_t before) -> std::optional<int> {
    std::optional<int> band;
    std::int64_t latest = -1;
    for (std::size_t index = 0; index < before; ++index) {
      const LoggedCommand &logged = commandLog_.at(index);
      if (logged.command.originNode == observer && logged.command.fleet == fleet &&
          logged.command.type == CommandType::PlaceFleet &&
          beliefs.at(index).believedFromTurn <= turn &&
          beliefs.at(index).believedFromTurn >= latest) {
        latest = beliefs.at(index).believedFromTurn;
        band = logged.command.targetBand;
      }
    }
    return band;
  };
  for (std::size_t index = 0; index < commandLog_.size(); ++index) {
    const LoggedCommand &logged = commandLog_.at(index);
    if (logged.command.originNode != observer) {
      continue;
    }
    OrderBelief &belief = beliefs.at(index);
    const std::optional<int> band = believedBand(logged.command.fleet, logged.issueTurn, index);
    if (band.has_value()) {
      belief.estimatedEffectTurn =
          logged.issueTurn +
          std::max<std::int64_t>(1, clock_.ceilTurns(estimatedDelaySec(originCm,
                                                                       bandRadiusCm(*band))));
    }
    belief.believedFromTurn = belief.estimatedEffectTurn.value_or(logged.issueTurn + worstTurns);
  }
  return beliefs;
}

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
  view.colonyTechTier = std::accumulate(
      view.nodes.begin(), view.nodes.end(), std::int64_t{0},
      [](std::int64_t best, const NodeView &node) {
        return node.isColony ? std::max(best, node.techTier) : best;
      });
  std::erase_if(view.nodeSignalsInFlight,
                [observer](const ArrivalRecord &signal) { return signal.sender != observer; });
  std::erase_if(view.arrivals,
                [observer](const ArrivalRecord &arrival) { return arrival.destination != observer; });
  // A station knows the orders it sent, not those another station sent.
  std::erase_if(view.ordersInFlight,
                [observer](const OrderInFlightView &order) { return order.origin != observer; });
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

  // The station's own orders in flight show its estimate of their arrival,
  // not the engine's true effect turn (which encodes the fleet's position).
  const std::vector<OrderBelief> beliefs = orderBeliefs(observer);
  for (OrderInFlightView &order : view.ordersInFlight) {
    const OrderBelief &belief = beliefs.at(order.logIndex);
    order.effectTurnKnown = belief.estimatedEffectTurn.has_value();
    order.effectTurn = belief.estimatedEffectTurn.value_or(0);
  }

  // Fleets report to the host: no telemetry here, and a position only where
  // this station believes it last sent them.
  for (FleetView &fleet : view.fleets) {
    blankTelemetry(fleet);
    std::optional<Command> placement;
    std::int64_t latest = -1;
    for (std::size_t index = 0; index < commandLog_.size(); ++index) {
      const LoggedCommand &logged = commandLog_.at(index);
      if (logged.command.originNode == observer && logged.command.fleet == fleet.id &&
          logged.command.type == CommandType::PlaceFleet &&
          beliefs.at(index).believedFromTurn <= now &&
          beliefs.at(index).believedFromTurn >= latest) {
        latest = beliefs.at(index).believedFromTurn;
        placement = logged.command;
      }
    }
    fleet.positionKnown = placement.has_value();
    fleet.bandIndex = placement.has_value() ? placement->targetBand : 0;
    fleet.lane = placement.has_value() ? placement->lane : OrbitLane::Prograde;
    fleet.observer = placement.has_value() ? observerFor(placement->lane, placement->station)
                                           : Observer::Hovering;
  }
  return view;
}

} // namespace game
