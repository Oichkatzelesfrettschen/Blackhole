/**
 * @file campaign.cpp
 * @brief Deterministic campaign state implementation.
 */

#include "game/campaign.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <numeric>
#include <utility>
#include <vector>

#include "game/campaign_view.h"
#include "game/command.h"
#include "game/economy.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/observer_clock.h"
#include "game/serialize_bytes.h"
#include "game/station_node.h"
#include "game/task_graph.h"
#include "game/temporal_clock.h"
#include "game/time_field.h"

namespace game {

using serial::appendF64;
using serial::appendI32;
using serial::appendI64;
using serial::appendU32;
using serial::appendU64;
using serial::appendU8;

CampaignState::CampaignState(CampaignConfig config, const TimeField &field)
    : config_(std::move(config)), field_(&field),
      // Band radii are validated at placement time (addFleet / PlaceFleet),
      // where the horizon gate belongs; the authority station and the turn
      // length are structural and gate construction itself.
      // Every node clock is exact integer arithmetic on whole-second turns.
      valid_(isClockTurnLength(config_.secondsPerTurn) &&
             field.admitsObserver(config_.authorityRadiusCm, config_.authorityObserver)),
      clock_(valid_ ? config_.secondsPerTurn : 1.0) {
  if (valid_) {
    buildNodes();
  }
  if (valid_) {
    resolveStoryParams();
  }
}

Fleet *CampaignState::findFleet(FleetId fleetId) {
  const auto fleet = std::ranges::find(fleets_, fleetId, &Fleet::id);
  return fleet == fleets_.end() ? nullptr : &*fleet;
}

double CampaignState::redeployFuelCost(int fromBand, int toBand) const {
  return config_.fuelPerBandHop * std::abs(toBand - fromBand);
}

double CampaignState::capabilityYieldMultiplier(FleetCapability capability) const {
  return config_.capabilityYieldMultiplier.at(static_cast<std::size_t>(capability));
}

double CampaignState::effectiveSignalDelaySec(double fromRadiusCm, double toRadiusCm) const {
  const double geodesicSec = field_->signalDelaySec(fromRadiusCm, toRadiusCm);
  double overhead = std::max(1.0, config_.signalOverheadFactor);
  if (config_.relayDelayFraction > 0.0 && overhead > 1.0) {
    // Relay fleets whose band radius lies between the two endpoints improve the
    // link: each removes a fraction of the coordination overhead. The overhead
    // floors at 1.0 -- the geodesic delay itself -- so a signal never beats
    // light.
    const double innerCm = std::fmin(fromRadiusCm, toRadiusCm);
    const double outerCm = std::fmax(fromRadiusCm, toRadiusCm);
    for (const Fleet &fleet : fleets_) {
      if (fleet.capability != FleetCapability::Relay) {
        continue;
      }
      const double relayCm = bandRadiusCm(fleet.bandIndex);
      if (relayCm > innerCm && relayCm < outerCm) {
        overhead *= (1.0 - config_.relayDelayFraction);
      }
    }
    overhead = std::max(1.0, overhead);
  }
  return geodesicSec * overhead;
}

bool CampaignState::placementAllowed(OrbitLane lane, StationKeeping station, int bandIndex) const {
  const double radiusCm = bandRadiusCm(bandIndex);
  if (lane == OrbitLane::Retrograde) {
    // Inside the static limit, frame dragging drags every observer forward: no
    // retrograde hold exists. A hovering ZAMO has zero angular momentum and so
    // no retrograde sense to hold anywhere.
    if (radiusCm < field_->ergosphereRadiusCm() || station == StationKeeping::Hover) {
      return false;
    }
  }
  return field_->admitsObserver(radiusCm, observerFor(lane, station));
}

double CampaignState::ergoregionDepth(const Fleet &fleet) const {
  return economy::ergoregionDepth(bandRadiusCm(fleet.bandIndex), field_->ergosphereRadiusCm(),
                                  field_->innerBoundaryRadiusCm(),
                                  fleet.lane == OrbitLane::Prograde);
}

double CampaignState::frameDragYieldFactor(const Fleet &fleet) const {
  return economy::frameDragYieldFactor(config_.frameDragYieldBonus, ergoregionDepth(fleet));
}

double CampaignState::bandRadiusCm(int bandIndex) const {
  assert(bandIndex >= 0 && static_cast<std::size_t>(bandIndex) < config_.bandRadiusCm.size());
  return config_.bandRadiusCm.at(static_cast<std::size_t>(bandIndex));
}

FleetId CampaignState::addFleet(FleetCapability capability, int bandIndex, OrbitLane lane,
                               StationKeeping station) {
  if (!valid_ || bandIndex < 0 ||
      static_cast<std::size_t>(bandIndex) >= config_.bandRadiusCm.size() ||
      !field_->isValidStationRadius(config_.bandRadiusCm.at(static_cast<std::size_t>(bandIndex))) ||
      !placementAllowed(lane, station, bandIndex)) {
    return K_INVALID_FLEET_ID;
  }
  Fleet fleet;
  fleet.id = nextFleetId_++;
  fleet.capability = capability;
  fleet.bandIndex = bandIndex;
  fleet.lane = lane;
  fleet.observer = observerFor(lane, station);
  fleet.fuelUnits = config_.fleetInitialFuelUnits;
  fleets_.push_back(std::move(fleet));
  return fleets_.back().id;
}

bool CampaignState::issueCommand(const Command &command) {
  // A decided campaign takes no further orders: the outcome is latched.
  if (!valid_ || status_ != CampaignStatus::Ongoing) {
    return false;
  }
  const Fleet *fleet = findFleet(command.fleet);
  if (fleet == nullptr) {
    return false;
  }
  // Orders leave from a live node: a dark station sends nothing.
  if (command.originNode >= nodes_.size() || nodes_.at(command.originNode).dark()) {
    return false;
  }
  switch (command.type) {
  case CommandType::PlaceFleet: {
    // Horizon gate: an at-or-inside-horizon placement is rejected HERE, before
    // the order can enter the delivery queue, so it can never advance a task.
    if (command.targetBand < 0 ||
        static_cast<std::size_t>(command.targetBand) >= config_.bandRadiusCm.size() ||
        !field_->isValidStationRadius(
            config_.bandRadiusCm.at(static_cast<std::size_t>(command.targetBand)))) {
      return false;
    }
    // Placement gate: retrograde cannot be held inside the ergosphere, and an
    // orbit needs a bound circular orbit at the band. Rejected here, at issue.
    if (!placementAllowed(command.lane, command.station, command.targetBand)) {
      return false;
    }
    // Fuel gate at issue time against the fleet's current position, for the
    // authority only: it holds the fleets' telemetry. A colony does not, so
    // its order is sent regardless and the effect-time check below decides,
    // with a fizzle notice travelling back. The charge itself always lands at
    // effect time from wherever the fleet then is.
    if (command.originNode == K_AUTHORITY_NODE &&
        redeployFuelCost(fleet->bandIndex, command.targetBand) > fleet->fuelUnits) {
      return false;
    }
    break;
  }
  case CommandType::AssignTask: {
    if (!std::isfinite(command.properTimeCostSec) || command.properTimeCostSec <= 0.0) {
      return false;
    }
    break;
  }
  }

  // Orders are in flight: the effect turn is the issue turn plus the signal
  // delay from the origin station to the fleet's CURRENT band, quantized once
  // to whole turns (ceil -- an order never lands early). An order is issued
  // between turns, after the issue turn's deliveries ran, so the earliest turn
  // it can act in is the next one: a zero delay (origin and fleet at one
  // radius) is logged as one turn, the turn it actually takes effect.
  const StationNode &origin = nodes_.at(command.originNode);
  const double delaySec = effectiveSignalDelaySec(origin.radiusCm, bandRadiusCm(fleet->bandIndex));
  LoggedCommand logged;
  logged.command = command;
  logged.issueTurn = clock_.turn();
  logged.effectTurn = clock_.turn() + std::max<std::int64_t>(1, clock_.ceilTurns(delaySec));
  commandLog_.push_back(logged);

  Delivery delivery;
  delivery.kind = DeliveryKind::Command;
  delivery.effectTurn = logged.effectTurn;
  delivery.sequence = nextSequence_++;
  delivery.commandIndex = static_cast<std::uint32_t>(commandLog_.size() - 1);
  delivery.emitTurn = logged.issueTurn;
  delivery.sender = origin.id;
  delivery.senderProperSecAtEmit = origin.clock.properSec();
  deliveryQueue_.push_back(delivery);
  return true;
}

void CampaignState::applyCommand(const LoggedCommand &logged) {
  Fleet *fleet = findFleet(logged.command.fleet);
  assert(fleet != nullptr);
  switch (logged.command.type) {
  case CommandType::PlaceFleet: {
    // Recharged against the fleet's position at EFFECT time: earlier orders
    // in flight may have moved it or spent its fuel. An unaffordable move
    // fizzles -- the fleet stays put and keeps its fuel.
    const double fuelCost = redeployFuelCost(fleet->bandIndex, logged.command.targetBand);
    // Fuel is the effect-time gate that can actually change: an earlier order
    // in flight may have spent this fleet's budget since issue. The placement
    // gate is re-checked for consistency but cannot differ -- the field is
    // fixed -- so an unaffordable move is the only way this fizzles.
    if (fuelCost <= fleet->fuelUnits &&
        placementAllowed(logged.command.lane, logged.command.station, logged.command.targetBand)) {
      fleet->fuelUnits -= fuelCost;
      fleet->bandIndex = logged.command.targetBand;
      fleet->lane = logged.command.lane;
      fleet->observer = observerFor(logged.command.lane, logged.command.station);
    } else if (logged.command.originNode != K_AUTHORITY_NODE) {
      // A station without the fleet's telemetry learns of the fizzle only
      // when the fleet's reply crosses back to it.
      emitFizzleNotice(*fleet, logged.command.originNode);
    }
    break;
  }
  case CommandType::AssignTask: {
    const TaskId taskId = taskGraph_.addTask(fleet->id, logged.command.properTimeCostSec);
    fleet->assignedTasks.push_back(taskId);
    break;
  }
  }
}

void CampaignState::deliverDue() {
  const std::int64_t now = clock_.turn();
  if (std::ranges::none_of(deliveryQueue_,
                           [now](const Delivery &delivery) { return delivery.effectTurn <= now; })) {
    return;
  }
  std::vector<Delivery> due;
  std::vector<Delivery> remaining;
  for (const Delivery &delivery : deliveryQueue_) {
    if (delivery.effectTurn <= clock_.turn()) {
      due.push_back(delivery);
    } else {
      remaining.push_back(delivery);
    }
  }
  std::ranges::stable_sort(due, [](const Delivery &a, const Delivery &b) {
    if (a.effectTurn != b.effectTurn) {
      return a.effectTurn < b.effectTurn;
    }
    return a.sequence < b.sequence;
  });
  // The queue holds what is still in flight before the due deliveries act, so
  // anything they emit (a fizzled order's notice) joins it rather than being
  // overwritten.
  deliveryQueue_ = std::move(remaining);
  for (const Delivery &delivery : due) {
    switch (delivery.kind) {
    case DeliveryKind::Command:
      applyCommand(commandLog_.at(delivery.commandIndex));
      break;
    case DeliveryKind::CompletionReport: {
      // A dark host hears nothing: the report and its yield are lost.
      if (nodes_.front().dark()) {
        energyLostToDarkness_ += delivery.yieldUnits;
        break;
      }
      IntelReport report;
      report.receivedTurn = clock_.turn();
      report.completedTurn = delivery.completedTurn;
      report.task = delivery.task;
      report.fleet = delivery.fleet;
      report.yieldUnits = delivery.yieldUnits;
      report.corrupted = delivery.corrupted;
      intelLog_.push_back(report);
      // Energy is banked HERE, on arrival: the authority cannot spend value
      // it has not yet heard about.
      energyUnits_ += delivery.yieldUnits;
      break;
    }
    case DeliveryKind::ColonyReport:
      if (nodes_.front().dark()) {
        energyLostToDarkness_ += delivery.yieldUnits;
      } else {
        energyUnits_ += delivery.yieldUnits;
        // A production report is also the host's latest word from the colony.
        noteSenderStamp(delivery);
      }
      break;
    case DeliveryKind::TechPacket:
    case DeliveryKind::EventNotice:
      receiveNodeDelivery(delivery);
      break;
    }
  }
}

void CampaignState::advanceTurn() {
  if (!valid_) {
    return;
  }
  clock_.advance();
  // Station clocks tick and colonies ship production; then everything due
  // arrives; then each node's story reads what has reached it this turn. A
  // story emission with zero delay (a node's own inference) lands this turn,
  // so every node delivery arrives exactly on its quantized effect turn.
  advanceNodeClocks();
  deliverDue();
  evaluateStory();
  deliverDue();
  taskGraph_.activateEligible();
  // Yield this turn is eroded by the instability ENTERING the turn: the
  // disturbance suppresses productive work before this turn's containment lands,
  // so containment protects the next turn's throughput. The factor saturates in
  // (0,1], never negative, so outer play slows but never dies.
  const double yieldFactor =
      economy::instabilityYieldFactor(instability_, config_.instabilityYieldPenaltyPerUnit);
  // Capability side effects are collected here and applied AFTER the fleet loop
  // so they never depend on iteration order: a fabrication refuel must hit every
  // co-band fleet identically, whether processed before or after the fabricator.
  std::vector<CapabilityCompletion> completions;
  double containmentThisTurn = 0.0;
  for (Fleet &fleet : fleets_) {
    const double rate = field_->properTimeRate(bandRadiusCm(fleet.bandIndex), fleet.observer);
    accrueProperTime(fleet, rate, clock_.secondsPerTurn());
    const double budgetSec = properDeltaSec(rate, clock_.secondsPerTurn());
    const TaskGraph::FleetAdvanceResult advanced = taskGraph_.advanceFleetTasks(fleet.id, budgetSec);
    // Wear: reliability degrades with local proper time actually worked, never
    // below the floor. Idle fleets do not wear. A prograde ergoregion fleet
    // wears faster -- deep near-horizon work carries a tidal/frame-drag hazard
    // scaled by depth -- so the deep lane spends integrity for its stabilization.
    if (advanced.properTimeSpentSec > 0.0) {
      const double wornDays = advanced.properTimeSpentSec / 86400.0;
      const double wearRate =
          config_.reliabilityWearPerProperDay +
          (config_.ergoHazardWearPerProperDay * ergoregionDepth(fleet));
      if (wearRate > 0.0) {
        fleet.reliability =
            std::max(config_.reliabilityFloor, fleet.reliability - (wearRate * wornDays));
      }
    }
    // Containment: a prograde ergoregion fleet suppresses instability in
    // proportion to the proper time it actually works, scaled by ergoregion
    // depth. This is the ergosphere mission beyond extraction. It acts at the
    // work site (physical suppression of the source), not through the report
    // queue that only carries what the authority KNOWS -- hence it lands this
    // turn while yield banks on delayed arrival.
    if (advanced.properTimeSpentSec > 0.0 && config_.ergoContainmentPerProperDay > 0.0) {
      const double depth = ergoregionDepth(fleet);
      if (depth > 0.0) {
        const double workedDays = advanced.properTimeSpentSec / 86400.0;
        containmentThisTurn += workedDays * config_.ergoContainmentPerProperDay * depth;
      }
    }
    // Corruption is judged on the post-wear reliability AT completion, before
    // any verification restore this turn: verification protects future work,
    // not a report already emitted.
    const bool corrupted = config_.reliabilityCorruptionThreshold > 0.0 &&
                           fleet.reliability < config_.reliabilityCorruptionThreshold;
    for (const TaskId taskId : advanced.completed) {
      // Telemetry rides the same causal queue as orders, outbound this time:
      // the authority learns of near-horizon completions late.
      const double reportDelaySec =
          effectiveSignalDelaySec(bandRadiusCm(fleet.bandIndex), config_.authorityRadiusCm);
      double yieldUnits =
          economy::taskYieldUnits(taskGraph_.find(taskId)->properTimeCostSec, rate,
                                  fleet.reliability) *
          frameDragYieldFactor(fleet) * capabilityYieldMultiplier(fleet.capability) * yieldFactor;
      if (corrupted) {
        yieldUnits *= config_.corruptedYieldFraction;
      }
      // Stabilization rivals extraction: a fleet whose deep prograde work is
      // taming the disturbance keeps only a fraction of its yield, so pursuing
      // stabilization genuinely costs energy rather than adding to it.
      if (config_.ergoContainmentPerProperDay > 0.0 && ergoregionDepth(fleet) > 0.0) {
        yieldUnits *= config_.containmentYieldRetention;
      }
      Delivery delivery;
      delivery.kind = DeliveryKind::CompletionReport;
      delivery.effectTurn = clock_.turn() + clock_.ceilTurns(reportDelaySec);
      delivery.sequence = nextSequence_++;
      delivery.completedTurn = clock_.turn();
      delivery.task = taskId;
      delivery.fleet = fleet.id;
      delivery.yieldUnits = yieldUnits;
      delivery.corrupted = corrupted;
      deliveryQueue_.push_back(delivery);
      completions.push_back({.capability = fleet.capability, .bandIndex = fleet.bandIndex});
    }
  }
  applyCapabilityEffects(completions);
  // Instability evolves after the work: this turn's rise, less this turn's
  // containment, floored at zero. Stabilization accumulates the containment
  // produced -- the ergosphere mission's scored output, a monotone record of
  // how much the deep lane held the singularity together.
  stabilization_ += containmentThisTurn;
  instability_ =
      std::max(0.0, instability_ + config_.instabilityPerTurn - containmentThisTurn);
  evaluateOutcome();
}

void CampaignState::applyCapabilityEffects(const std::vector<CapabilityCompletion> &completions) {
  for (const CapabilityCompletion &completion : completions) {
    if (completion.capability == FleetCapability::Fabrication &&
        config_.fabricationFuelRestore > 0.0) {
      // Band-local logistics: a fabrication run refuels every fleet sharing its
      // band, capped at the starting budget.
      for (Fleet &fleet : fleets_) {
        if (fleet.bandIndex == completion.bandIndex) {
          fleet.fuelUnits = std::min(config_.fleetInitialFuelUnits,
                                     fleet.fuelUnits + config_.fabricationFuelRestore);
        }
      }
    } else if (completion.capability == FleetCapability::Verification &&
               config_.verificationReliabilityRestore > 0.0) {
      // Band-local maintenance: verification restores reliability to co-band
      // fleets, keeping their telemetry above the corruption threshold.
      for (Fleet &fleet : fleets_) {
        if (fleet.bandIndex == completion.bandIndex) {
          fleet.reliability =
              std::min(1.0, fleet.reliability + config_.verificationReliabilityRestore);
        }
      }
    }
  }
}

void CampaignState::evaluateOutcome() {
  if (status_ != CampaignStatus::Ongoing) {
    return;
  }
  // Two ends: bank the energy target, or tame the singularity. Either latches a
  // win and records the turn it cleared. Neither dominates -- the stabilization
  // path costs energy (containmentYieldRetention), the energy path leaves the
  // disturbance to grow -- so which to pursue is a genuine choice.
  const bool energyWin =
      config_.victoryEnergyUnits > 0.0 && energyUnits_ >= config_.victoryEnergyUnits;
  const bool stabilizationWin =
      config_.victoryStabilizationUnits > 0.0 && stabilization_ >= config_.victoryStabilizationUnits;
  const bool techWin = config_.victoryTechTier > 0 && colonyTechTier() >= config_.victoryTechTier;
  if (energyWin || stabilizationWin || techWin) {
    clearedTurn_ = clock_.turn(); // turns-to-clear: the speed axis of the outcome vector.
    status_ = CampaignStatus::Won;
    return;
  }
  if (config_.deadlineTurn > 0 && clock_.turn() >= config_.deadlineTurn) {
    status_ = CampaignStatus::Lost;
  }
}

void CampaignState::advanceTurns(std::int64_t turnCount) {
  assert(turnCount >= 0);
  for (std::int64_t step = 0; step < turnCount; ++step) {
    advanceTurn();
  }
}

CampaignViewSnapshot CampaignState::renderSnapshot() const {
  CampaignViewSnapshot view;
  view.turn = clock_.turn();
  view.secondsPerTurn = clock_.secondsPerTurn();
  view.coordinateTimeSec = clock_.coordinateTimeSec();
  view.status = status_;
  view.energyUnits = energyUnits_;
  view.victoryEnergyUnits = config_.victoryEnergyUnits;
  view.deadlineTurn = config_.deadlineTurn;
  view.instability = instability_;
  view.stabilization = stabilization_;
  view.victoryStabilizationUnits = config_.victoryStabilizationUnits;
  view.clearedTurn = clearedTurn_;
  // Integrity is the weakest fleet: the deep dive's wear shows up as the axis the
  // player trades stabilization and speed against.
  view.fleetIntegrity = std::accumulate(
      fleets_.begin(), fleets_.end(), fleets_.empty() ? 1.0 : fleets_.front().reliability,
      [](double integrity, const Fleet &fleet) { return std::min(integrity, fleet.reliability); });
  view.ergosphereRadiusCm = field_->ergosphereRadiusCm();
  view.spinDimensionless = field_->spinDimensionless();
  view.spinDeficit = field_->spinDeficit();
  view.authorityObserver = config_.authorityObserver;
  view.reliabilityCorruptionThreshold = config_.reliabilityCorruptionThreshold;
  view.authorityRadiusCm = config_.authorityRadiusCm;
  view.authorityProperTimeRate =
      valid_ ? field_->properTimeRate(config_.authorityRadiusCm, config_.authorityObserver) : 0.0;
  view.innerBoundaryRadiusCm = field_->innerBoundaryRadiusCm();

  view.bands.reserve(config_.bandRadiusCm.size());
  for (std::size_t bandIndex = 0; bandIndex < config_.bandRadiusCm.size(); ++bandIndex) {
    BandView band;
    band.index = static_cast<int>(bandIndex);
    band.radiusCm = config_.bandRadiusCm.at(bandIndex);
    band.validStation = field_->isValidStationRadius(band.radiusCm);
    band.insideErgosphere = band.validStation && band.radiusCm < field_->ergosphereRadiusCm();
    if (band.validStation) {
      // The rate a fleet placed here by default carries: a prograde orbit where
      // a bound one exists, a hovering station below the marginally bound radius.
      band.admitsOrbit = field_->admitsObserver(band.radiusCm, Observer::CircularOrbitPrograde);
      band.stableOrbit = field_->admitsStableOrbit(band.radiusCm, Observer::CircularOrbitPrograde);
      band.admitsRetrogradeOrbit =
          field_->admitsObserver(band.radiusCm, Observer::CircularOrbitRetrograde);
      band.stableRetrogradeOrbit =
          field_->admitsStableOrbit(band.radiusCm, Observer::CircularOrbitRetrograde);
      band.hoverProperTimeRate = field_->properTimeRate(band.radiusCm, Observer::Hovering);
      band.progradeOrbitProperTimeRate =
          band.admitsOrbit ? field_->properTimeRate(band.radiusCm, Observer::CircularOrbitPrograde)
                           : 0.0;
      band.retrogradeOrbitProperTimeRate =
          band.admitsRetrogradeOrbit
              ? field_->properTimeRate(band.radiusCm, Observer::CircularOrbitRetrograde)
              : 0.0;
      band.properTimeRate =
          band.admitsOrbit ? band.progradeOrbitProperTimeRate : band.hoverProperTimeRate;
      band.delayToAuthoritySec = effectiveSignalDelaySec(band.radiusCm, config_.authorityRadiusCm);
      band.frameDragRateRadPerSec = field_->frameDragRateRadPerSec(band.radiusCm);
    }
    view.bands.push_back(band);
  }

  view.fleets.reserve(fleets_.size());
  for (const Fleet &fleet : fleets_) {
    FleetView fleetView;
    fleetView.id = fleet.id;
    fleetView.capability = fleet.capability;
    fleetView.bandIndex = fleet.bandIndex;
    fleetView.reliability = fleet.reliability;
    fleetView.properTimeSec = fleet.properTimeSec;
    fleetView.properTimeRate =
        field_->properTimeRate(bandRadiusCm(fleet.bandIndex), fleet.observer);
    fleetView.observer = fleet.observer;
    fleetView.unstableOrbit =
        fleet.observer != Observer::Hovering &&
        !field_->admitsStableOrbit(bandRadiusCm(fleet.bandIndex), fleet.observer);
    fleetView.fuelUnits = fleet.fuelUnits;
    fleetView.lane = fleet.lane;
    fleetView.yieldMultiplier = capabilityYieldMultiplier(fleet.capability);
    fleetView.telemetryCorrupted = config_.reliabilityCorruptionThreshold > 0.0 &&
                                   fleet.reliability < config_.reliabilityCorruptionThreshold;
    for (const TaskId taskId : fleet.assignedTasks) {
      const TaskContract *contract = taskGraph_.find(taskId);
      if (contract == nullptr) {
        continue;
      }
      switch (contract->state) {
      case TaskState::Pending:
        ++fleetView.pendingTasks;
        break;
      case TaskState::Active:
        ++fleetView.activeTasks;
        break;
      case TaskState::Complete:
        ++fleetView.completedTasks;
        break;
      }
    }
    view.fleets.push_back(fleetView);
  }

  for (const Delivery &delivery : deliveryQueue_) {
    switch (delivery.kind) {
    case DeliveryKind::Command: {
      const LoggedCommand &logged = commandLog_.at(delivery.commandIndex);
      OrderInFlightView order;
      order.type = logged.command.type;
      order.fleet = logged.command.fleet;
      order.issueTurn = logged.issueTurn;
      order.effectTurn = logged.effectTurn;
      order.origin = logged.command.originNode;
      view.ordersInFlight.push_back(order);
      break;
    }
    case DeliveryKind::CompletionReport: {
      ReportInFlightView report;
      report.task = delivery.task;
      report.fleet = delivery.fleet;
      report.completedTurn = delivery.completedTurn;
      report.effectTurn = delivery.effectTurn;
      view.reportsInFlight.push_back(report);
      break;
    }
    case DeliveryKind::ColonyReport:
    case DeliveryKind::TechPacket:
    case DeliveryKind::EventNotice: {
      ArrivalRecord signal;
      signal.kind = delivery.kind == DeliveryKind::TechPacket ? EmitKind::TechPacket
                                                              : EmitKind::Notice;
      signal.category = delivery.category;
      signal.sender = delivery.sender;
      signal.destination = delivery.destination;
      signal.emitTurn = delivery.emitTurn;
      signal.arrivalTurn = delivery.effectTurn;
      signal.senderProperSecAtEmit = delivery.senderProperSecAtEmit;
      signal.senderEnergyUnitsAtEmit = delivery.senderEnergyUnitsAtEmit;
      signal.senderTechPointsAtEmit = delivery.senderTechPointsAtEmit;
      signal.payloadIndex = delivery.payloadIndex;
      signal.fleet = delivery.sender == K_NO_NODE ? delivery.fleet : K_INVALID_FLEET_ID;
      signal.techPoints = delivery.techPoints;
      if (delivery.kind == DeliveryKind::ColonyReport) {
        ++view.colonyReportsInFlight;
      } else {
        view.nodeSignalsInFlight.push_back(signal);
      }
      break;
    }
    }
  }

  view.intel.reserve(intelLog_.size());
  for (const IntelReport &report : intelLog_) {
    IntelView intelView;
    intelView.receivedTurn = report.receivedTurn;
    intelView.completedTurn = report.completedTurn;
    intelView.task = report.task;
    intelView.fleet = report.fleet;
    intelView.yieldUnits = report.yieldUnits;
    intelView.corrupted = report.corrupted;
    view.intel.push_back(intelView);
  }

  view.nodes.reserve(nodes_.size());
  for (const StationNode &node : nodes_) {
    NodeView nodeView;
    nodeView.id = node.id;
    nodeView.isColony = node.isColony;
    nodeView.radiusCm = node.radiusCm;
    nodeView.observer = node.observer;
    nodeView.properTimeRate = node.clock.rate();
    nodeView.properTimeSec = node.clock.properSecApprox();
    nodeView.dark = node.dark();
    nodeView.techPoints = node.techPoints;
    nodeView.techTier = techTier(node.id);
    nodeView.missionProperSec = node.isColony ? node.colony.missionProperSec : 0;
    nodeView.asOfTurn = clock_.turn();
    view.nodes.push_back(nodeView);
  }
  view.arrivals = arrivals_;
  view.eventTexts.reserve(config_.story.events.size());
  for (const EventDef &event : config_.story.events) {
    view.eventTexts.push_back(
        {.id = event.id, .name = event.name, .text = event.text, .category = event.category});
  }
  view.techTiers.reserve(config_.story.techTiers.size());
  for (const TechLevel &level : config_.story.techTiers) {
    view.techTiers.push_back({.points = level.points, .name = level.name});
  }
  view.colonyTechTier = colonyTechTier();
  view.victoryTechTier = config_.victoryTechTier;
  view.energyLostToDarkness = energyLostToDarkness_;
  return view;
}

std::vector<std::uint8_t> CampaignState::serializeState() const {
  std::vector<std::uint8_t> out;
  appendU64(out, config_.seed);
  appendF64(out, config_.secondsPerTurn);
  // The field's spin enters as its deficit, the parameter that stays exact
  // near extremal spin; mass is fixed by the scenario's band radii.
  appendF64(out, field_->spinDeficit());
  appendF64(out, config_.authorityRadiusCm);
  appendU8(out, static_cast<std::uint8_t>(config_.authorityObserver));
  appendU32(out, static_cast<std::uint32_t>(config_.bandRadiusCm.size()));
  for (const double radiusCm : config_.bandRadiusCm) {
    appendF64(out, radiusCm);
  }
  appendF64(out, config_.victoryEnergyUnits);
  appendI64(out, config_.deadlineTurn);
  appendF64(out, config_.fleetInitialFuelUnits);
  appendF64(out, config_.fuelPerBandHop);
  appendF64(out, config_.reliabilityWearPerProperDay);
  appendF64(out, config_.reliabilityFloor);
  appendF64(out, config_.frameDragYieldBonus);
  for (const double multiplier : config_.capabilityYieldMultiplier) {
    appendF64(out, multiplier);
  }
  appendF64(out, config_.signalOverheadFactor);
  appendF64(out, config_.relayDelayFraction);
  appendF64(out, config_.fabricationFuelRestore);
  appendF64(out, config_.verificationReliabilityRestore);
  appendF64(out, config_.reliabilityCorruptionThreshold);
  appendF64(out, config_.corruptedYieldFraction);
  appendF64(out, config_.instabilityPerTurn);
  appendF64(out, config_.instabilityYieldPenaltyPerUnit);
  appendF64(out, config_.ergoContainmentPerProperDay);
  appendF64(out, config_.ergoHazardWearPerProperDay);
  appendF64(out, config_.containmentYieldRetention);
  appendF64(out, config_.victoryStabilizationUnits);
  appendI64(out, clock_.turn());
  appendF64(out, energyUnits_);
  appendF64(out, instability_);
  appendF64(out, stabilization_);
  appendI64(out, clearedTurn_);
  appendU8(out, static_cast<std::uint8_t>(status_));
  appendU32(out, static_cast<std::uint32_t>(fleets_.size()));
  for (const Fleet &fleet : fleets_) {
    appendU32(out, fleet.id);
    appendU8(out, static_cast<std::uint8_t>(fleet.capability));
    appendU8(out, static_cast<std::uint8_t>(fleet.lane));
    appendU8(out, static_cast<std::uint8_t>(fleet.observer));
    appendI32(out, fleet.bandIndex);
    appendF64(out, fleet.reliability);
    appendF64(out, fleet.properTimeSec);
    appendF64(out, fleet.fuelUnits);
    appendU32(out, static_cast<std::uint32_t>(fleet.assignedTasks.size()));
    for (const TaskId taskId : fleet.assignedTasks) {
      appendU32(out, taskId);
    }
  }
  appendU32(out, static_cast<std::uint32_t>(taskGraph_.tasks().size()));
  for (const TaskContract &contract : taskGraph_.tasks()) {
    appendU32(out, contract.id);
    appendU32(out, static_cast<std::uint32_t>(contract.prerequisites.size()));
    for (const TaskId prerequisiteId : contract.prerequisites) {
      appendU32(out, prerequisiteId);
    }
    appendU32(out, contract.assignedFleet);
    appendF64(out, contract.properTimeCostSec);
    appendF64(out, contract.progressSec);
    appendU8(out, static_cast<std::uint8_t>(contract.state));
  }
  appendU32(out, static_cast<std::uint32_t>(commandLog_.size()));
  for (const LoggedCommand &logged : commandLog_) {
    appendU8(out, static_cast<std::uint8_t>(logged.command.type));
    appendU32(out, logged.command.fleet);
    appendI32(out, logged.command.targetBand);
    appendU8(out, static_cast<std::uint8_t>(logged.command.lane));
    appendU8(out, static_cast<std::uint8_t>(logged.command.station));
    appendF64(out, logged.command.properTimeCostSec);
    appendI64(out, logged.issueTurn);
    appendI64(out, logged.effectTurn);
    appendU32(out, logged.command.originNode);
  }
  appendU32(out, static_cast<std::uint32_t>(deliveryQueue_.size()));
  for (const Delivery &delivery : deliveryQueue_) {
    appendU8(out, static_cast<std::uint8_t>(delivery.kind));
    appendI64(out, delivery.effectTurn);
    appendU32(out, delivery.sequence);
    appendU32(out, delivery.commandIndex);
    appendI64(out, delivery.completedTurn);
    appendU32(out, delivery.task);
    appendU32(out, delivery.fleet);
    appendF64(out, delivery.yieldUnits);
    appendU8(out, delivery.corrupted ? 1U : 0U);
    appendI64(out, delivery.emitTurn);
    appendU32(out, delivery.sender);
    appendU32(out, delivery.destination);
    appendI64(out, delivery.senderProperSecAtEmit);
    appendF64(out, delivery.senderEnergyUnitsAtEmit);
    appendI64(out, delivery.senderTechPointsAtEmit);
    appendU32(out, delivery.payloadIndex);
    appendI64(out, delivery.techPoints);
    appendU8(out, static_cast<std::uint8_t>(delivery.category));
  }
  appendU32(out, static_cast<std::uint32_t>(intelLog_.size()));
  for (const IntelReport &report : intelLog_) {
    appendI64(out, report.receivedTurn);
    appendI64(out, report.completedTurn);
    appendU32(out, report.task);
    appendU32(out, report.fleet);
    appendF64(out, report.yieldUnits);
    appendU8(out, report.corrupted ? 1U : 0U);
  }
  appendU32(out, nextFleetId_);
  appendU32(out, nextSequence_);
  appendStoryState(out);
  return out;
}

std::uint64_t CampaignState::stateDigest() const { return serial::fnv1a64(serializeState()); }

} // namespace game
