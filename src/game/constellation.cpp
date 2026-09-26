/**
 * @file constellation.cpp
 * @brief Deterministic multi-system, multi-faction constellation implementation.
 */

#include "game/constellation.h"

#include <algorithm>
#include <iterator>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <utility>
#include <vector>

#include "game/campaign_view.h"
#include "game/constellation_types.h"
#include "game/constellation_view.h"
#include "game/economy.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/serialize_bytes.h"
#include "game/temporal_clock.h"

namespace game {

using serial::appendF64;
using serial::appendI64;
using serial::appendU32;
using serial::appendU64;
using serial::appendU8;

namespace {

constexpr double K_C_CM_PER_S = 2.99792458e10; ///< Speed of light.
constexpr double K_NO_LIGHT_PATH = -1.0;        ///< lightPathSec_ entry for an unreachable pair.

void appendFleetBelief(std::vector<std::uint8_t> &out, const FleetBelief &known) {
  appendU32(out, known.id);
  appendU32(out, known.system);
  appendI64(out, known.bandIndex);
  appendU8(out, static_cast<std::uint8_t>(known.lane));
  appendU8(out, static_cast<std::uint8_t>(known.observer));
  appendF64(out, known.reliability);
  appendF64(out, known.fuelUnits);
  appendU8(out, known.inTransit ? 1U : 0U);
  appendI64(out, known.transitArrivalTurn);
  appendU32(out, known.transitDestSystem);
  appendI64(out, known.transitDestBand);
  appendI64(out, known.asOfTurn);
}

} // namespace

const char *factionPolicyName(FactionPolicy policy) {
  switch (policy) {
  case FactionPolicy::Expansionist:
    return "expansionist";
  case FactionPolicy::Extractor:
    return "extractor";
  case FactionPolicy::Contester:
    return "contester";
  case FactionPolicy::Scripted:
  default:
    return "scripted";
  }
}

Constellation::Constellation(ConstellationConfig config)
    : config_(std::move(config)),
      valid_(std::isfinite(config_.secondsPerTurn) && config_.secondsPerTurn > 0.0 &&
             !config_.systems.empty() && config_.interSystemTravelSpeedFraction > 0.0 &&
             config_.interSystemTravelSpeedFraction < 1.0),
      clock_(valid_ ? config_.secondsPerTurn : 1.0) {
  if (!valid_) {
    return;
  }
  systems_.reserve(config_.systems.size());
  for (const SystemSpec &spec : config_.systems) {
    OrbitalSystem system{.field = KerrTimeField(spec.blackHoleMassG, spec.spinDimensionless),
                         .authorityRadiusCm = spec.authorityRadiusCm,
                         .authorityObserver = spec.authorityObserver,
                         .bandRadiusCm = spec.bandRadiusCm,
                         .instability = 0.0};
    // The authority station must be physically admissible for its observer; a
    // system whose command origin sits at or inside the horizon, or orbits
    // where no bound orbit exists, invalidates the whole constellation.
    if (!system.field.admitsObserver(spec.authorityRadiusCm, spec.authorityObserver)) {
      valid_ = false;
    }
    systems_.push_back(std::move(system));
  }
  // All-pairs light paths over the link graph (Floyd-Warshall, fixed loop
  // order so the sums are identical on every run). A link naming a missing
  // system or carrying a non-finite or negative separation invalidates the
  // constellation rather than silently opening a zero-delay channel.
  const std::size_t count = systems_.size();
  lightPathSec_.assign(count * count, K_NO_LIGHT_PATH);
  for (std::size_t index = 0; index < count; ++index) {
    lightPathSec_.at((index * count) + index) = 0.0;
  }
  for (const InterSystemLink &link : config_.links) {
    if (link.a >= count || link.b >= count || link.a == link.b ||
        !std::isfinite(link.separationCm) || link.separationCm < 0.0) {
      valid_ = false;
      continue;
    }
    const double linkSec = link.separationCm / K_C_CM_PER_S;
    double &forward = lightPathSec_.at((link.a * count) + link.b);
    if (forward < 0.0 || linkSec < forward) {
      forward = linkSec;
      lightPathSec_.at((link.b * count) + link.a) = linkSec;
    }
  }
  for (std::size_t via = 0; via < count; ++via) {
    for (std::size_t from = 0; from < count; ++from) {
      const double firstLeg = lightPathSec_.at((from * count) + via);
      if (firstLeg < 0.0) {
        continue;
      }
      for (std::size_t to = 0; to < count; ++to) {
        const double secondLeg = lightPathSec_.at((via * count) + to);
        if (secondLeg < 0.0) {
          continue;
        }
        double &direct = lightPathSec_.at((from * count) + to);
        if (direct < 0.0 || firstLeg + secondLeg < direct) {
          direct = firstLeg + secondLeg;
        }
      }
    }
  }
  lastEmittedController_.resize(systems_.size());
  for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
    lastEmittedController_.at(systemIndex)
        .assign(systems_.at(systemIndex).bandRadiusCm.size(), K_INVALID_FACTION_ID);
  }
}

std::size_t Constellation::factionIndex(FactionId faction) const {
  for (std::size_t index = 0; index < factions_.size(); ++index) {
    if (factions_.at(index).id == faction) {
      return index;
    }
  }
  return factions_.size();
}

ConstellationFleet *Constellation::findFleet(FleetId fleetId) {
  const auto fleet = std::ranges::find(fleets_, fleetId, &ConstellationFleet::id);
  return fleet == fleets_.end() ? nullptr : &*fleet;
}

const ConstellationFleet *Constellation::findFleet(FleetId fleetId) const {
  const auto fleet = std::ranges::find(fleets_, fleetId, &ConstellationFleet::id);
  return fleet == fleets_.end() ? nullptr : &*fleet;
}

double Constellation::bandRadiusCm(SystemId system, int bandIndex) const {
  return systems_.at(system).bandRadiusCm.at(static_cast<std::size_t>(bandIndex));
}

bool Constellation::validBand(SystemId system, int bandIndex) const {
  if (system >= systems_.size() || bandIndex < 0 ||
      static_cast<std::size_t>(bandIndex) >= systems_.at(system).bandRadiusCm.size()) {
    return false;
  }
  return systems_.at(system).field.isValidStationRadius(bandRadiusCm(system, bandIndex));
}

bool Constellation::placementAllowed(SystemId system, OrbitLane lane, StationKeeping station,
                                     int bandIndex) const {
  const KerrTimeField &field = systems_.at(system).field;
  const double radiusCm = bandRadiusCm(system, bandIndex);
  if (lane == OrbitLane::Retrograde &&
      (radiusCm < field.ergosphereRadiusCm() || station == StationKeeping::Hover)) {
    // Frame dragging forbids a retrograde hold inside the static limit, and a
    // hovering ZAMO carries no retrograde sense anywhere.
    return false;
  }
  return field.admitsObserver(radiusCm, observerFor(lane, station));
}

StationKeeping Constellation::defaultStation(SystemId system, int bandIndex) const {
  if (!validBand(system, bandIndex)) {
    return StationKeeping::Orbit;
  }
  return systems_.at(system).field.admitsObserver(bandRadiusCm(system, bandIndex),
                                                  Observer::CircularOrbitPrograde)
             ? StationKeeping::Orbit
             : StationKeeping::Hover;
}

double Constellation::linkSeparationCm(SystemId a, SystemId b) const {
  const auto link = std::ranges::find_if(config_.links, [a, b](const InterSystemLink &candidate) {
    return (candidate.a == a && candidate.b == b) || (candidate.a == b && candidate.b == a);
  });
  return link == config_.links.end() ? -1.0 : link->separationCm;
}

double Constellation::lightPathSec(SystemId a, SystemId b) const {
  return lightPathSec_.at((static_cast<std::size_t>(a) * systems_.size()) + b);
}

double Constellation::intraSystemDelaySec(SystemId system, int bandIndex) const {
  const OrbitalSystem &orbital = systems_.at(system);
  return orbital.field.signalDelaySec(bandRadiusCm(system, bandIndex), orbital.authorityRadiusCm);
}

double Constellation::orderDelaySec(FactionId faction, SystemId system, int bandIndex) const {
  const SystemId homeSystem = factions_.at(factionIndex(faction)).homeSystem;
  const double interstellar = lightPathSec(homeSystem, system);
  if (interstellar < 0.0) {
    return K_NO_LIGHT_PATH;
  }
  return interstellar + intraSystemDelaySec(system, bandIndex);
}

double Constellation::reportDelaySec(FactionId faction, SystemId system, int bandIndex) const {
  const SystemId homeSystem = factions_.at(factionIndex(faction)).homeSystem;
  const double interstellar = lightPathSec(system, homeSystem);
  if (interstellar < 0.0) {
    return K_NO_LIGHT_PATH;
  }
  return intraSystemDelaySec(system, bandIndex) + interstellar;
}

double Constellation::ergoregionDepth(const ConstellationFleet &fleet) const {
  const KerrTimeField &field = systems_.at(fleet.system).field;
  return economy::ergoregionDepth(bandRadiusCm(fleet.system, fleet.bandIndex),
                                  field.ergosphereRadiusCm(), field.innerBoundaryRadiusCm(),
                                  fleet.lane == OrbitLane::Prograde);
}

FactionId Constellation::addFaction(FactionPolicy policy, SystemId homeSystem) {
  if (!valid_ || homeSystem >= systems_.size()) {
    return K_INVALID_FACTION_ID;
  }
  FactionState faction;
  faction.id = nextFactionId_++;
  faction.policy = policy;
  faction.homeSystem = homeSystem;
  factions_.push_back(faction);
  if (playerFaction_ == K_INVALID_FACTION_ID) {
    playerFaction_ = faction.id;
  }
  // Extend the delayed-intel table with an all-unknown row for the new faction.
  std::vector<std::vector<FactionId>> perceivedRow(systems_.size());
  for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
    perceivedRow.at(systemIndex)
        .assign(systems_.at(systemIndex).bandRadiusCm.size(), K_INVALID_FACTION_ID);
  }
  perceived_.push_back(std::move(perceivedRow));
  ownBelief_.emplace_back();
  return faction.id;
}

FleetId Constellation::addFleet(FactionId faction, SystemId system, FleetCapability capability,
                                int bandIndex, OrbitLane lane, StationKeeping station) {
  if (!valid_ || factionIndex(faction) == factions_.size() || !validBand(system, bandIndex) ||
      !placementAllowed(system, lane, station, bandIndex)) {
    return K_INVALID_FLEET_ID;
  }
  ConstellationFleet fleet;
  fleet.id = nextFleetId_++;
  fleet.faction = faction;
  fleet.system = system;
  fleet.capability = capability;
  fleet.bandIndex = bandIndex;
  fleet.lane = lane;
  fleet.observer = observerFor(lane, station);
  fleet.fuelUnits = config_.fleetInitialFuelUnits;
  // Setup placement happens at the authority's direction, so the owner starts
  // with an exact record as of turn 0.
  ownBelief_.at(factionIndex(faction))
      .push_back(FleetBelief{.id = fleet.id,
                             .system = fleet.system,
                             .bandIndex = fleet.bandIndex,
                             .lane = fleet.lane,
                             .observer = fleet.observer,
                             .reliability = fleet.reliability,
                             .fuelUnits = fleet.fuelUnits,
                             .inTransit = false,
                             .transitArrivalTurn = 0,
                             .transitDestSystem = K_INVALID_SYSTEM_ID,
                             .transitDestBand = 0,
                             .asOfTurn = clock_.turn()});
  fleets_.push_back(std::move(fleet));
  return fleets_.back().id;
}

bool Constellation::issueCommand(FactionId faction, const ConstellationCommand &command) {
  if (!valid_ || factionIndex(faction) == factions_.size()) {
    return false;
  }
  // A faction stops only once news of the decision reaches its authority; a
  // rival light-days from the winner keeps ordering until then.
  if (factions_.at(factionIndex(faction)).outcomeKnown) {
    return false;
  }
  // A faction commands only its own fleets, and validates against what its
  // authority last heard about them: position, transit, and fuel as reported.
  // The effect-time checks in applyCommand judge the fleet's actual state.
  const FleetBelief *known = knownFleet(faction, command.fleet);
  if (known == nullptr || known->inTransit) {
    return false;
  }
  if (!validBand(command.targetSystem, command.targetBand) ||
      !placementAllowed(command.targetSystem, command.lane, command.station, command.targetBand)) {
    return false;
  }
  if (command.targetSystem == known->system) {
    const double fuelCost =
        config_.fuelPerBandHop * std::abs(command.targetBand - known->bandIndex);
    if (fuelCost > known->fuelUnits) {
      return false;
    }
  } else if (linkSeparationCm(known->system, command.targetSystem) < 0.0 ||
             config_.interSystemTravelFuelUnits > known->fuelUnits) {
    // Interstellar travel needs a direct link and its own fuel budget.
    return false;
  }

  // The order travels to where the fleet was last reported; an order to a
  // system no chain of links reaches can never arrive.
  const double delaySec = orderDelaySec(faction, known->system, known->bandIndex);
  if (delaySec < 0.0) {
    return false;
  }
  LoggedCommand logged;
  logged.command = command;
  logged.faction = faction;
  logged.issueTurn = clock_.turn();
  logged.effectTurn = clock_.turn() + clock_.ceilTurns(delaySec);
  logged.addressedSystem = known->system;
  logged.addressedBand = known->bandIndex;
  commandLog_.push_back(logged);

  Delivery delivery;
  delivery.kind = DeliveryKind::Command;
  delivery.effectTurn = logged.effectTurn;
  delivery.sequence = nextSequence_++;
  delivery.commandIndex = static_cast<std::uint32_t>(commandLog_.size() - 1);
  deliveryQueue_.push_back(delivery);
  return true;
}

void Constellation::applyCommand(std::uint32_t commandIndex) {
  const LoggedCommand &logged = commandLog_.at(commandIndex);
  ConstellationFleet *const fleet = findFleet(logged.command.fleet);
  if (fleet == nullptr || fleet->inTransit || fleet->system != logged.addressedSystem ||
      fleet->bandIndex != logged.addressedBand) {
    // The order reached the slot it was addressed to and the fleet had left:
    // it fizzles there -- it cannot chase the fleet faster than light -- and
    // the addressed station's non-delivery notice travels home from there.
    const double delaySec =
        reportDelaySec(logged.faction, logged.addressedSystem, logged.addressedBand);
    if (delaySec >= 0.0) {
      Delivery notice;
      notice.kind = DeliveryKind::OrderUndelivered;
      notice.effectTurn = clock_.turn() + clock_.ceilTurns(delaySec);
      notice.sequence = nextSequence_++;
      notice.commandIndex = commandIndex;
      notice.observerIndex = factionIndex(logged.faction);
      deliveryQueue_.push_back(notice);
    }
    return;
  }
  // The fleet answers every order it receives, from where it received it, so
  // the authority learns the outcome -- a move, a departure, or a fizzle.
  const SystemId receivedAtSystem = fleet->system;
  const int receivedAtBand = fleet->bandIndex;
  applyReceivedCommand(*fleet, logged.command);
  enqueueFleetStatus(*fleet, receivedAtSystem, receivedAtBand);
}

void Constellation::applyReceivedCommand(ConstellationFleet &fleet,
                                         const ConstellationCommand &command) {
  if (command.targetSystem == fleet.system) {
    const double fuelCost = config_.fuelPerBandHop * std::abs(command.targetBand - fleet.bandIndex);
    if (fuelCost <= fleet.fuelUnits && validBand(command.targetSystem, command.targetBand) &&
        placementAllowed(command.targetSystem, command.lane, command.station, command.targetBand)) {
      fleet.fuelUnits -= fuelCost;
      fleet.bandIndex = command.targetBand;
      fleet.lane = command.lane;
      fleet.observer = observerFor(command.lane, command.station);
    }
    return;
  }
  const double separationCm = linkSeparationCm(fleet.system, command.targetSystem);
  if (separationCm >= 0.0 && config_.interSystemTravelFuelUnits <= fleet.fuelUnits &&
      validBand(command.targetSystem, command.targetBand)) {
    fleet.fuelUnits -= config_.interSystemTravelFuelUnits;
    const double travelSec =
        separationCm / (config_.interSystemTravelSpeedFraction * K_C_CM_PER_S);
    // The fleet stays in its origin system's books until it arrives: it holds
    // no band there while coasting and joins the destination only on arrival.
    fleet.inTransit = true;
    fleet.transitArrivalTurn = clock_.turn() + clock_.ceilTurns(travelSec);
    fleet.transitDestSystem = command.targetSystem;
    fleet.transitDestBand = command.targetBand;
    fleet.transitDestLane = command.lane;
    fleet.transitDestObserver = observerFor(command.lane, command.station);
  }
}

void Constellation::deliverDue() {
  std::vector<Delivery> due;
  std::vector<Delivery> remaining;
  for (const Delivery &delivery : deliveryQueue_) {
    if (delivery.effectTurn <= clock_.turn()) {
      due.push_back(delivery);
    } else {
      remaining.push_back(delivery);
    }
  }
  std::ranges::stable_sort(due, [](const Delivery &lhs, const Delivery &rhs) {
    if (lhs.effectTurn != rhs.effectTurn) {
      return lhs.effectTurn < rhs.effectTurn;
    }
    return lhs.sequence < rhs.sequence;
  });
  // The queue holds only what is still in flight before any delivery runs, so
  // a report a delivered order emits (FleetStatus) joins it rather than being
  // overwritten.
  deliveryQueue_ = std::move(remaining);
  for (const Delivery &delivery : due) {
    switch (delivery.kind) {
    case DeliveryKind::Command:
      applyCommand(delivery.commandIndex);
      break;
    case DeliveryKind::YieldReport:
      factions_.at(factionIndex(delivery.faction)).energyUnits += delivery.yieldUnits;
      break;
    case DeliveryKind::ControlObservation:
      perceived_.at(delivery.observerIndex)
          .at(delivery.system)
          .at(static_cast<std::size_t>(delivery.bandIndex)) = delivery.controller;
      break;
    case DeliveryKind::ScoreReport: {
      FactionState &faction = factions_.at(delivery.observerIndex);
      faction.knownStabilizationUnits += delivery.stabilizationUnits;
      faction.knownControlScore += delivery.controlPoints;
      break;
    }
    case DeliveryKind::OrderUndelivered:
      commandLog_.at(delivery.commandIndex).undelivered = true;
      break;
    case DeliveryKind::OutcomeNotice:
      factions_.at(delivery.observerIndex).outcomeKnown = true;
      break;
    case DeliveryKind::FleetStatus: {
      std::vector<FleetBelief> &beliefs = ownBelief_.at(delivery.observerIndex);
      const auto found = std::ranges::find(beliefs, delivery.status.id, &FleetBelief::id);
      // Reports can cross in flight; the authority keeps the newest state.
      if (found != beliefs.end() && found->asOfTurn <= delivery.status.asOfTurn) {
        *found = delivery.status;
      }
      break;
    }
    }
  }
}

void Constellation::landArrivals() {
  for (ConstellationFleet &fleet : fleets_) {
    if (fleet.inTransit && fleet.transitArrivalTurn <= clock_.turn()) {
      fleet.inTransit = false;
      fleet.system = fleet.transitDestSystem;
      fleet.bandIndex = fleet.transitDestBand;
      fleet.lane = fleet.transitDestLane;
      fleet.observer = fleet.transitDestObserver;
      enqueueFleetStatus(fleet, fleet.system, fleet.bandIndex);
    }
  }
}

void Constellation::enqueueFleetStatus(const ConstellationFleet &fleet, SystemId fromSystem,
                                       int fromBand) {
  const double delaySec = reportDelaySec(fleet.faction, fromSystem, fromBand);
  if (delaySec < 0.0) {
    return; // No light path home: the authority never hears.
  }
  Delivery delivery;
  delivery.kind = DeliveryKind::FleetStatus;
  delivery.effectTurn = clock_.turn() + clock_.ceilTurns(delaySec);
  delivery.sequence = nextSequence_++;
  delivery.observerIndex = factionIndex(fleet.faction);
  delivery.status = FleetBelief{.id = fleet.id,
                                .system = fleet.system,
                                .bandIndex = fleet.bandIndex,
                                .lane = fleet.lane,
                                .observer = fleet.observer,
                                .reliability = fleet.reliability,
                                .fuelUnits = fleet.fuelUnits,
                                .inTransit = fleet.inTransit,
                                .transitArrivalTurn = fleet.transitArrivalTurn,
                                .transitDestSystem = fleet.transitDestSystem,
                                .transitDestBand = fleet.transitDestBand,
                                .asOfTurn = clock_.turn()};
  deliveryQueue_.push_back(delivery);
}

const FleetBelief *Constellation::knownFleet(FactionId faction, FleetId fleet) const {
  const std::size_t index = factionIndex(faction);
  if (index == factions_.size()) {
    return nullptr;
  }
  const std::vector<FleetBelief> &beliefs = ownBelief_.at(index);
  const auto found = std::ranges::find(beliefs, fleet, &FleetBelief::id);
  return found == beliefs.end() ? nullptr : &*found;
}

void Constellation::enqueueYieldReport(const ConstellationFleet &fleet, double yieldUnits) {
  const double delaySec = reportDelaySec(fleet.faction, fleet.system, fleet.bandIndex);
  if (delaySec < 0.0) {
    return; // No light path home: the report, and the value it carries, never arrives.
  }
  Delivery delivery;
  delivery.kind = DeliveryKind::YieldReport;
  delivery.effectTurn = clock_.turn() + clock_.ceilTurns(delaySec);
  delivery.sequence = nextSequence_++;
  delivery.faction = fleet.faction;
  delivery.yieldUnits = yieldUnits;
  deliveryQueue_.push_back(delivery);
}

void Constellation::runFleetWork() {
  std::vector<double> instabilityEntering(systems_.size());
  std::vector<double> containmentThisTurn(systems_.size(), 0.0);
  for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
    instabilityEntering.at(systemIndex) = systems_.at(systemIndex).instability;
  }
  const double reportThresholdSec = config_.workProperHoursPerReport * economy::K_SECONDS_PER_HOUR;
  const double beta = config_.interSystemTravelSpeedFraction;
  const double transitClockRate = std::sqrt((1.0 - beta) * (1.0 + beta));
  for (ConstellationFleet &fleet : fleets_) {
    if (fleet.inTransit) {
      // Interstellar coasting at beta = interSystemTravelSpeedFraction in flat
      // space: the crew ages sqrt(1 - beta^2) per coordinate second (the twin
      // effect), does no work, and holds no band.
      fleet.properTimeSec += properDeltaSec(transitClockRate, clock_.secondsPerTurn());
      continue;
    }
    const KerrTimeField &field = systems_.at(fleet.system).field;
    const double rate =
        field.properTimeRate(bandRadiusCm(fleet.system, fleet.bandIndex), fleet.observer);
    const double properDelta = properDeltaSec(rate, clock_.secondsPerTurn());
    fleet.properTimeSec += properDelta;
    fleet.pendingWorkProperSec += properDelta;
    const double depth = ergoregionDepth(fleet);

    if (properDelta > 0.0) {
      const double wornDays = properDelta / economy::K_SECONDS_PER_DAY;
      const double wearRate =
          config_.reliabilityWearPerProperDay + (config_.ergoHazardWearPerProperDay * depth);
      if (wearRate > 0.0) {
        fleet.reliability =
            std::max(config_.reliabilityFloor, fleet.reliability - (wearRate * wornDays));
      }
    }

    if (properDelta > 0.0 && config_.ergoContainmentPerProperDay > 0.0 && depth > 0.0) {
      const double workedDays = properDelta / economy::K_SECONDS_PER_DAY;
      const double produced = workedDays * config_.ergoContainmentPerProperDay * depth;
      containmentThisTurn.at(fleet.system) += produced;
      recordCredit(factionIndex(fleet.faction), fleet.system, fleet.bandIndex, produced, 0.0);
    }

    const double frameDrag = economy::frameDragYieldFactor(config_.frameDragYieldBonus, depth);
    const double capMultiplier =
        config_.capabilityYieldMultiplier.at(static_cast<std::size_t>(fleet.capability));
    const double instabilityFactor = economy::instabilityYieldFactor(
        instabilityEntering.at(fleet.system), config_.instabilityYieldPenaltyPerUnit);
    const bool stabilizing = config_.ergoContainmentPerProperDay > 0.0 && depth > 0.0;
    while (fleet.pendingWorkProperSec >= reportThresholdSec) {
      fleet.pendingWorkProperSec -= reportThresholdSec;
      double yieldUnits = economy::taskYieldUnits(reportThresholdSec, rate, fleet.reliability) *
                          frameDrag * capMultiplier * instabilityFactor;
      if (stabilizing) {
        yieldUnits *= config_.containmentYieldRetention;
      }
      enqueueYieldReport(fleet, yieldUnits);
    }
  }
  for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
    systems_.at(systemIndex).instability =
        std::max(0.0, instabilityEntering.at(systemIndex) + config_.instabilityPerTurn -
                          containmentThisTurn.at(systemIndex));
  }
}

FactionId Constellation::bandController(SystemId system, int bandIndex) const {
  FactionId holder = K_INVALID_FACTION_ID;
  bool contested = false;
  for (const ConstellationFleet &fleet : fleets_) {
    if (fleet.inTransit || fleet.system != system || fleet.bandIndex != bandIndex) {
      continue;
    }
    if (holder == K_INVALID_FACTION_ID) {
      holder = fleet.faction;
    } else if (fleet.faction != holder) {
      contested = true;
    }
  }
  return contested ? K_INVALID_FACTION_ID : holder;
}

void Constellation::scoreControlAndObserve() {
  for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
    const auto system = static_cast<SystemId>(systemIndex);
    const std::size_t bandCount = systems_.at(systemIndex).bandRadiusCm.size();
    for (std::size_t bandIndex = 0; bandIndex < bandCount; ++bandIndex) {
      const FactionId controller = bandController(system, static_cast<int>(bandIndex));
      if (controller != K_INVALID_FACTION_ID) {
        recordCredit(factionIndex(controller), system, static_cast<int>(bandIndex), 0.0,
                     config_.controlPointsPerBandPerTurn);
      }
      if (controller == lastEmittedController_.at(systemIndex).at(bandIndex)) {
        continue;
      }
      // A change in who holds this band becomes intel each faction learns after
      // light from the band reaches its authority: the radial leg to this
      // system's authority, then the light path to the observer's home. An
      // observer no chain of links reaches never learns of it.
      const double radialSec = intraSystemDelaySec(system, static_cast<int>(bandIndex));
      for (std::size_t observerIndex = 0; observerIndex < factions_.size(); ++observerIndex) {
        const double pathSec = lightPathSec(system, factions_.at(observerIndex).homeSystem);
        if (pathSec < 0.0) {
          continue;
        }
        Delivery delivery;
        delivery.kind = DeliveryKind::ControlObservation;
        delivery.effectTurn = clock_.turn() + clock_.ceilTurns(radialSec + pathSec);
        delivery.sequence = nextSequence_++;
        delivery.system = system;
        delivery.bandIndex = static_cast<int>(bandIndex);
        delivery.controller = controller;
        delivery.observerIndex = observerIndex;
        deliveryQueue_.push_back(delivery);
      }
      lastEmittedController_.at(systemIndex).at(bandIndex) = controller;
    }
  }
}

void Constellation::advanceTurn() {
  if (!valid_) {
    return;
  }
  clock_.advance();
  turnCredits_.clear();
  lastStabilizationSite_.assign(factions_.size(), CreditSite{});
  lastControlSite_.assign(factions_.size(), CreditSite{});
  deliverDue();
  landArrivals();
  runFleetWork();
  scoreControlAndObserve();
  sendScoreReports();
  stepFactionAI();
  evaluateOutcomes();
}

void Constellation::recordCredit(std::size_t factionIndexValue, SystemId system, int bandIndex,
                                 double stabilizationUnits, double controlPoints) {
  FactionState &faction = factions_.at(factionIndexValue);
  faction.stabilizationUnits += stabilizationUnits;
  faction.controlScore += controlPoints;
  if (stabilizationUnits > 0.0) {
    lastStabilizationSite_.at(factionIndexValue) = CreditSite{.system = system, .bandIndex = bandIndex};
  }
  if (controlPoints > 0.0) {
    lastControlSite_.at(factionIndexValue) = CreditSite{.system = system, .bandIndex = bandIndex};
  }
  turnCredits_.push_back(TurnCredit{.factionIndex = factionIndexValue,
                                    .system = system,
                                    .bandIndex = bandIndex,
                                    .stabilizationUnits = stabilizationUnits,
                                    .controlPoints = controlPoints});
}

void Constellation::sendScoreReports() {
  // One report per (faction, system, band): stable sort keeps the recording
  // order within a key, so the merged sums are identical on every run.
  std::ranges::stable_sort(turnCredits_, [](const TurnCredit &lhs, const TurnCredit &rhs) {
    if (lhs.factionIndex != rhs.factionIndex) {
      return lhs.factionIndex < rhs.factionIndex;
    }
    if (lhs.system != rhs.system) {
      return lhs.system < rhs.system;
    }
    return lhs.bandIndex < rhs.bandIndex;
  });
  for (std::size_t first = 0; first < turnCredits_.size();) {
    const TurnCredit &key = turnCredits_.at(first);
    double stabilizationUnits = 0.0;
    double controlPoints = 0.0;
    std::size_t next = first;
    while (next < turnCredits_.size() && turnCredits_.at(next).factionIndex == key.factionIndex &&
           turnCredits_.at(next).system == key.system &&
           turnCredits_.at(next).bandIndex == key.bandIndex) {
      stabilizationUnits += turnCredits_.at(next).stabilizationUnits;
      controlPoints += turnCredits_.at(next).controlPoints;
      ++next;
    }
    const double delaySec =
        reportDelaySec(factions_.at(key.factionIndex).id, key.system, key.bandIndex);
    if (delaySec >= 0.0) {
      Delivery delivery;
      delivery.kind = DeliveryKind::ScoreReport;
      delivery.effectTurn = clock_.turn() + clock_.ceilTurns(delaySec);
      delivery.sequence = nextSequence_++;
      delivery.observerIndex = key.factionIndex;
      delivery.stabilizationUnits = stabilizationUnits;
      delivery.controlPoints = controlPoints;
      deliveryQueue_.push_back(delivery);
    }
    first = next;
  }
}

double Constellation::siteDelaySec(const CreditSite &site, SystemId toSystem) const {
  const double pathSec = lightPathSec(site.system, toSystem);
  if (pathSec < 0.0) {
    return K_NO_LIGHT_PATH;
  }
  return (site.bandIndex >= 0 ? intraSystemDelaySec(site.system, site.bandIndex) : 0.0) + pathSec;
}

void Constellation::advanceTurns(std::int64_t turnCount) {
  assert(turnCount >= 0);
  for (std::int64_t step = 0; step < turnCount; ++step) {
    advanceTurn();
  }
}

void Constellation::evaluateOutcomes() {
  if (decided_) {
    return;
  }
  for (FactionState &faction : factions_) {
    if (faction.status != CampaignStatus::Ongoing) {
      continue;
    }
    const bool energyWin =
        config_.victoryEnergyUnits > 0.0 && faction.energyUnits >= config_.victoryEnergyUnits;
    const bool stabilizationWin = config_.victoryStabilizationUnits > 0.0 &&
                                  faction.stabilizationUnits >= config_.victoryStabilizationUnits;
    const bool controlWin =
        config_.victoryControlScore > 0.0 && faction.controlScore >= config_.victoryControlScore;
    if (energyWin || stabilizationWin || controlWin) {
      faction.status = CampaignStatus::Won;
      faction.clearedTurn = clock_.turn();
    }
  }
  // The lowest-id faction that just cleared is the winner: a fixed tie-break so a
  // simultaneous clear resolves identically on every run.
  const auto winningFaction = std::ranges::find(factions_, CampaignStatus::Won, &FactionState::status);
  if (winningFaction != factions_.end()) {
    decided_ = true;
    winner_ = winningFaction->id;
    overallStatus_ = winningFaction->id == playerFaction_ ? CampaignStatus::Won : CampaignStatus::Lost;
    // The decision is an event at the place the deciding credit happened: the
    // winner's authority for banked energy, else the band of its last
    // stabilization or control credit this turn (axes checked in that order).
    // Every authority, the winner's included, learns by light from there; one
    // no chain of links reaches never does.
    const auto winnerIndex =
        static_cast<std::size_t>(std::distance(factions_.begin(), winningFaction));
    CreditSite site{.system = winningFaction->homeSystem, .bandIndex = -1};
    const bool energyWin = config_.victoryEnergyUnits > 0.0 &&
                           winningFaction->energyUnits >= config_.victoryEnergyUnits;
    const bool stabilizationWin =
        config_.victoryStabilizationUnits > 0.0 &&
        winningFaction->stabilizationUnits >= config_.victoryStabilizationUnits;
    if (!energyWin && stabilizationWin &&
        lastStabilizationSite_.at(winnerIndex).system != K_INVALID_SYSTEM_ID) {
      site = lastStabilizationSite_.at(winnerIndex);
    } else if (!energyWin && !stabilizationWin &&
               lastControlSite_.at(winnerIndex).system != K_INVALID_SYSTEM_ID) {
      site = lastControlSite_.at(winnerIndex);
    }
    for (std::size_t observerIndex = 0; observerIndex < factions_.size(); ++observerIndex) {
      const double delaySec = siteDelaySec(site, factions_.at(observerIndex).homeSystem);
      if (delaySec < 0.0) {
        continue;
      }
      const std::int64_t delayTurns = clock_.ceilTurns(delaySec);
      if (delayTurns == 0) {
        factions_.at(observerIndex).outcomeKnown = true;
        continue;
      }
      Delivery delivery;
      delivery.kind = DeliveryKind::OutcomeNotice;
      delivery.effectTurn = clock_.turn() + delayTurns;
      delivery.sequence = nextSequence_++;
      delivery.observerIndex = observerIndex;
      deliveryQueue_.push_back(delivery);
    }
    return;
  }
  if (config_.deadlineTurn > 0 && clock_.turn() >= config_.deadlineTurn) {
    decided_ = true;
    overallStatus_ = CampaignStatus::Lost; // The player did not win in time.
    // The deadline is a coordinate turn every authority's calendar already
    // carries, so no signal has to travel for it.
    for (FactionState &faction : factions_) {
      faction.outcomeKnown = true;
    }
  }
}

bool Constellation::hasCommandInFlight(const FleetBelief &known) const {
  return std::ranges::any_of(commandLog_, [&](const LoggedCommand &logged) {
    return logged.command.fleet == known.id && logged.effectTurn > known.asOfTurn &&
           !logged.undelivered;
  });
}

bool Constellation::factionOccupies(FactionId faction, SystemId system, int bandIndex) const {
  const bool reported =
      std::ranges::any_of(ownBelief_.at(factionIndex(faction)), [&](const FleetBelief &known) {
        return known.inTransit
                   ? (known.transitDestSystem == system && known.transitDestBand == bandIndex)
                   : (known.system == system && known.bandIndex == bandIndex);
      });
  // The authority also knows what it has ordered: a slot an unanswered order
  // is sending a fleet to counts as claimed.
  return reported || std::ranges::any_of(commandLog_, [&](const LoggedCommand &logged) {
           if (logged.faction != faction || logged.command.targetSystem != system ||
               logged.command.targetBand != bandIndex) {
             return false;
           }
           const FleetBelief *known = knownFleet(faction, logged.command.fleet);
           return known != nullptr && logged.effectTurn > known->asOfTurn;
         });
}

bool Constellation::systemReachableFrom(SystemId fromSystem, SystemId toSystem) const {
  return fromSystem == toSystem || linkSeparationCm(fromSystem, toSystem) >= 0.0;
}

bool Constellation::fleetAvailable(const FleetBelief &known) const {
  return !known.inTransit && !hasCommandInFlight(known);
}

std::vector<ConstellationCommand>
Constellation::expansionistOrders(const FactionState &faction) const {
  // Spread onto distinct bands across reachable systems: find a fleet redundant
  // with a lower-id same-faction fleet on the same slot, and send it to the first
  // canonical valid slot the faction does not already occupy.
  const std::vector<FleetBelief> &beliefs = ownBelief_.at(factionIndex(faction.id));
  for (const FleetBelief &fleet : beliefs) {
    if (!fleetAvailable(fleet)) {
      continue;
    }
    const bool redundant = std::ranges::any_of(beliefs, [&](const FleetBelief &other) {
      return other.id < fleet.id && !other.inTransit && other.system == fleet.system &&
             other.bandIndex == fleet.bandIndex;
    });
    if (!redundant) {
      continue;
    }
    for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
      const auto system = static_cast<SystemId>(systemIndex);
      if (!systemReachableFrom(fleet.system, system)) {
        continue;
      }
      const std::size_t bandCount = systems_.at(systemIndex).bandRadiusCm.size();
      for (std::size_t bandIndex = 0; bandIndex < bandCount; ++bandIndex) {
        const int band = static_cast<int>(bandIndex);
        if (validBand(system, band) && !factionOccupies(faction.id, system, band)) {
          return {{.fleet = fleet.id,
                   .targetSystem = system,
                   .targetBand = band,
                   .lane = OrbitLane::Prograde,
                   .station = defaultStation(system, band)}};
        }
      }
    }
  }
  return {};
}

std::vector<ConstellationCommand>
Constellation::extractorOrders(const FactionState &faction) const {
  // Concentrate on the home system's deepest valid prograde band -- highest yield
  // per local hour -- moving one out-of-place fleet each turn.
  const SystemId home = faction.homeSystem;
  int deepestBand = -1;
  for (std::size_t bandIndex = 0; bandIndex < systems_.at(home).bandRadiusCm.size(); ++bandIndex) {
    const int band = static_cast<int>(bandIndex);
    if (validBand(home, band) &&
        (deepestBand < 0 || bandRadiusCm(home, band) < bandRadiusCm(home, deepestBand))) {
      deepestBand = band;
    }
  }
  if (deepestBand < 0) {
    return {};
  }
  for (const FleetBelief &fleet : ownBelief_.at(factionIndex(faction.id))) {
    if (!fleetAvailable(fleet)) {
      continue;
    }
    const bool inPlace = fleet.system == home && fleet.bandIndex == deepestBand;
    if (!inPlace && systemReachableFrom(fleet.system, home)) {
      return {{.fleet = fleet.id,
               .targetSystem = home,
               .targetBand = deepestBand,
               .lane = OrbitLane::Prograde,
               .station = defaultStation(home, deepestBand)}};
    }
  }
  return {};
}

std::vector<ConstellationCommand>
Constellation::contesterOrders(const FactionState &faction) const {
  // Deny the perceived leader: from this faction's delayed intel, find the rival
  // believed to hold the most bands and contest one of them.
  const std::size_t selfIndex = factionIndex(faction.id);
  std::vector<std::uint32_t> perceivedHeld(factions_.size(), 0);
  const std::vector<std::vector<FactionId>> &belief = perceived_.at(selfIndex);
  for (const std::vector<FactionId> &systemRow : belief) {
    for (const FactionId controller : systemRow) {
      if (controller != K_INVALID_FACTION_ID && controller != faction.id) {
        ++perceivedHeld.at(factionIndex(controller));
      }
    }
  }
  FactionId leader = K_INVALID_FACTION_ID;
  std::uint32_t leaderHeld = 0;
  for (std::size_t index = 0; index < factions_.size(); ++index) {
    if (perceivedHeld.at(index) > leaderHeld) {
      leaderHeld = perceivedHeld.at(index);
      leader = factions_.at(index).id;
    }
  }
  if (leader == K_INVALID_FACTION_ID) {
    return {};
  }
  for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
    const auto system = static_cast<SystemId>(systemIndex);
    for (std::size_t bandIndex = 0; bandIndex < belief.at(systemIndex).size(); ++bandIndex) {
      const int band = static_cast<int>(bandIndex);
      if (belief.at(systemIndex).at(bandIndex) != leader ||
          factionOccupies(faction.id, system, band) || !validBand(system, band)) {
        continue;
      }
      const std::vector<FleetBelief> &own = ownBelief_.at(selfIndex);
      const auto fleet = std::ranges::find_if(own, [&](const FleetBelief &candidate) {
        return fleetAvailable(candidate) && systemReachableFrom(candidate.system, system);
      });
      if (fleet != own.end()) {
        return {{.fleet = fleet->id,
                 .targetSystem = system,
                 .targetBand = band,
                 .lane = OrbitLane::Prograde,
                 .station = defaultStation(system, band)}};
      }
    }
  }
  return {};
}

std::vector<ConstellationCommand> Constellation::policyOrders(const FactionState &faction) const {
  switch (faction.policy) {
  case FactionPolicy::Expansionist:
    return expansionistOrders(faction);
  case FactionPolicy::Extractor:
    return extractorOrders(faction);
  case FactionPolicy::Contester:
    return contesterOrders(faction);
  case FactionPolicy::Scripted:
  default:
    return {};
  }
}

void Constellation::stepFactionAI() {
  for (const FactionState &faction : factions_) {
    if (faction.policy == FactionPolicy::Scripted || faction.status != CampaignStatus::Ongoing ||
        faction.outcomeKnown) {
      continue;
    }
    const std::vector<ConstellationCommand> orders = policyOrders(faction);
    for (const ConstellationCommand &order : orders) {
      static_cast<void>(issueCommand(faction.id, order));
    }
  }
}

ConstellationViewSnapshot Constellation::renderSnapshot() const {
  ConstellationViewSnapshot view;
  view.turn = clock_.turn();
  view.secondsPerTurn = clock_.secondsPerTurn();
  view.overallStatus = overallStatus_;
  view.winner = winner_;
  view.playerFaction = playerFaction_;
  view.victoryEnergyUnits = config_.victoryEnergyUnits;
  view.victoryStabilizationUnits = config_.victoryStabilizationUnits;
  view.victoryControlScore = config_.victoryControlScore;
  view.deadlineTurn = config_.deadlineTurn;

  // The view is the player's: band control as the player's authority has
  // learned it, never the referee's truth.
  const std::size_t playerIndex = factionIndex(playerFaction_);
  view.systems.reserve(systems_.size());
  for (std::size_t systemIndex = 0; systemIndex < systems_.size(); ++systemIndex) {
    SystemStanding standing;
    standing.id = static_cast<SystemId>(systemIndex);
    standing.instability = systems_.at(systemIndex).instability;
    standing.spinDimensionless = systems_.at(systemIndex).field.spinDimensionless();
    standing.spinDeficit = systems_.at(systemIndex).field.spinDeficit();
    const std::size_t bandCount = systems_.at(systemIndex).bandRadiusCm.size();
    standing.bandCount = static_cast<std::uint32_t>(bandCount);
    standing.bandController.reserve(bandCount);
    for (std::size_t bandIndex = 0; bandIndex < bandCount; ++bandIndex) {
      standing.bandController.push_back(
          perceivedController(playerIndex, standing.id, static_cast<int>(bandIndex)));
    }
    view.systems.push_back(std::move(standing));
  }

  view.factions.reserve(factions_.size());
  for (const FactionState &faction : factions_) {
    FactionStanding standing;
    standing.id = faction.id;
    standing.policy = faction.policy;
    standing.homeSystem = faction.homeSystem;
    standing.energyUnits = faction.energyUnits;
    standing.stabilizationUnits = faction.stabilizationUnits;
    standing.controlScore = faction.controlScore;
    standing.status = faction.status;
    standing.clearedTurn = faction.clearedTurn;
    standing.fleetCount = static_cast<std::uint32_t>(std::ranges::count_if(
        fleets_, [&](const ConstellationFleet &fleet) { return fleet.faction == faction.id; }));
    for (const SystemStanding &system : view.systems) {
      standing.heldBandCount += static_cast<std::uint32_t>(std::ranges::count(
          system.bandController, faction.id));
    }
    view.factions.push_back(standing);
  }

  // The player's own fleets as last reported home; rival fleets appear only
  // through perceived band control.
  if (playerIndex < ownBelief_.size()) {
    view.fleets.reserve(ownBelief_.at(playerIndex).size());
    for (const FleetBelief &known : ownBelief_.at(playerIndex)) {
      const ConstellationFleet *fleet = findFleet(known.id);
      ConstellationFleetView fleetView;
      fleetView.id = known.id;
      fleetView.faction = playerFaction_;
      fleetView.system = known.system;
      fleetView.capability = fleet != nullptr ? fleet->capability : FleetCapability::Research;
      fleetView.bandIndex = known.bandIndex;
      fleetView.lane = known.lane;
      fleetView.observer = known.observer;
      fleetView.reliability = known.reliability;
      fleetView.inTransit = known.inTransit;
      fleetView.transitArrivalTurn = known.transitArrivalTurn;
      fleetView.transitDestSystem = known.transitDestSystem;
      fleetView.reportedTurn = known.asOfTurn;
      view.fleets.push_back(fleetView);
    }
  }

  view.links = config_.links;
  return view;
}

std::vector<std::uint8_t> Constellation::serializeState() const {
  std::vector<std::uint8_t> out;
  appendU64(out, config_.seed);
  appendI64(out, clock_.turn());
  appendU8(out, decided_ ? 1U : 0U);
  appendU8(out, static_cast<std::uint8_t>(overallStatus_));
  appendU32(out, winner_);
  appendU32(out, playerFaction_);

  appendU32(out, static_cast<std::uint32_t>(systems_.size()));
  for (const OrbitalSystem &system : systems_) {
    appendF64(out, system.field.spinDeficit());
    appendU8(out, static_cast<std::uint8_t>(system.authorityObserver));
    appendF64(out, system.instability);
  }

  appendU32(out, static_cast<std::uint32_t>(factions_.size()));
  for (const FactionState &faction : factions_) {
    appendU32(out, faction.id);
    appendU8(out, static_cast<std::uint8_t>(faction.policy));
    appendU32(out, faction.homeSystem);
    appendF64(out, faction.energyUnits);
    appendF64(out, faction.stabilizationUnits);
    appendF64(out, faction.controlScore);
    appendU8(out, static_cast<std::uint8_t>(faction.status));
    appendI64(out, faction.clearedTurn);
    appendU8(out, faction.outcomeKnown ? 1U : 0U);
    appendF64(out, faction.knownStabilizationUnits);
    appendF64(out, faction.knownControlScore);
  }

  appendU32(out, static_cast<std::uint32_t>(fleets_.size()));
  for (const ConstellationFleet &fleet : fleets_) {
    appendU32(out, fleet.id);
    appendU32(out, fleet.faction);
    appendU32(out, fleet.system);
    appendU8(out, static_cast<std::uint8_t>(fleet.capability));
    appendI64(out, fleet.bandIndex);
    appendU8(out, static_cast<std::uint8_t>(fleet.lane));
    appendU8(out, static_cast<std::uint8_t>(fleet.observer));
    appendF64(out, fleet.reliability);
    appendF64(out, fleet.properTimeSec);
    appendF64(out, fleet.pendingWorkProperSec);
    appendF64(out, fleet.fuelUnits);
    appendU8(out, fleet.inTransit ? 1U : 0U);
    appendI64(out, fleet.transitArrivalTurn);
    appendU32(out, fleet.transitDestSystem);
    appendI64(out, fleet.transitDestBand);
    appendU8(out, static_cast<std::uint8_t>(fleet.transitDestLane));
    appendU8(out, static_cast<std::uint8_t>(fleet.transitDestObserver));
  }

  appendU32(out, static_cast<std::uint32_t>(commandLog_.size()));
  for (const LoggedCommand &logged : commandLog_) {
    appendU32(out, logged.command.fleet);
    appendU32(out, logged.command.targetSystem);
    appendI64(out, logged.command.targetBand);
    appendU8(out, static_cast<std::uint8_t>(logged.command.lane));
    appendU8(out, static_cast<std::uint8_t>(logged.command.station));
    appendU32(out, logged.faction);
    appendI64(out, logged.issueTurn);
    appendI64(out, logged.effectTurn);
    appendU32(out, logged.addressedSystem);
    appendI64(out, logged.addressedBand);
    appendU8(out, logged.undelivered ? 1U : 0U);
  }

  appendU32(out, static_cast<std::uint32_t>(deliveryQueue_.size()));
  for (const Delivery &delivery : deliveryQueue_) {
    appendU8(out, static_cast<std::uint8_t>(delivery.kind));
    appendI64(out, delivery.effectTurn);
    appendU32(out, delivery.sequence);
    appendU32(out, delivery.commandIndex);
    appendU32(out, delivery.faction);
    appendF64(out, delivery.yieldUnits);
    appendU32(out, delivery.system);
    appendI64(out, delivery.bandIndex);
    appendU32(out, delivery.controller);
    appendU64(out, delivery.observerIndex);
    appendFleetBelief(out, delivery.status);
    appendF64(out, delivery.stabilizationUnits);
    appendF64(out, delivery.controlPoints);
  }

  for (const std::vector<std::vector<FactionId>> &factionRow : perceived_) {
    for (const std::vector<FactionId> &systemRow : factionRow) {
      for (const FactionId controller : systemRow) {
        appendU32(out, controller);
      }
    }
  }
  for (const std::vector<FactionId> &systemRow : lastEmittedController_) {
    for (const FactionId controller : systemRow) {
      appendU32(out, controller);
    }
  }
  for (const std::vector<FleetBelief> &beliefs : ownBelief_) {
    appendU32(out, static_cast<std::uint32_t>(beliefs.size()));
    for (const FleetBelief &known : beliefs) {
      appendFleetBelief(out, known);
    }
  }

  appendU32(out, nextFleetId_);
  appendU32(out, nextFactionId_);
  appendU32(out, nextSequence_);
  return out;
}

std::uint64_t Constellation::stateDigest() const { return serial::fnv1a64(serializeState()); }

FactionId Constellation::perceivedController(std::size_t factionIndexValue, SystemId system,
                                             int bandIndex) const {
  if (factionIndexValue >= perceived_.size() ||
      system >= perceived_.at(factionIndexValue).size() || bandIndex < 0 ||
      static_cast<std::size_t>(bandIndex) >= perceived_.at(factionIndexValue).at(system).size()) {
    return K_INVALID_FACTION_ID;
  }
  return perceived_.at(factionIndexValue).at(system).at(static_cast<std::size_t>(bandIndex));
}

} // namespace game
