/**
 * @file campaign.cpp
 * @brief Deterministic campaign state implementation.
 */

#include "game/campaign.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstdint>
#include <cstring>
#include <utility>
#include <vector>

#include "game/campaign_view.h"
#include "game/command.h"
#include "game/fleet.h"
#include "game/task_graph.h"
#include "game/temporal_clock.h"
#include "game/time_field.h"

namespace game {

namespace {

// Field-by-field little-endian writers. Whole-struct memcpy would serialize
// padding bytes; these never do.
void appendU8(std::vector<std::uint8_t> &out, std::uint8_t value) { out.push_back(value); }

void appendU32(std::vector<std::uint8_t> &out, std::uint32_t value) {
  for (int byteIndex = 0; byteIndex < 4; ++byteIndex) {
    out.push_back(static_cast<std::uint8_t>((value >> (8 * byteIndex)) & 0xFFU));
  }
}

void appendU64(std::vector<std::uint8_t> &out, std::uint64_t value) {
  for (int byteIndex = 0; byteIndex < 8; ++byteIndex) {
    out.push_back(static_cast<std::uint8_t>((value >> (8 * byteIndex)) & 0xFFU));
  }
}

void appendI64(std::vector<std::uint8_t> &out, std::int64_t value) {
  appendU64(out, static_cast<std::uint64_t>(value));
}

void appendI32(std::vector<std::uint8_t> &out, std::int32_t value) {
  appendU32(out, static_cast<std::uint32_t>(value));
}

void appendF64(std::vector<std::uint8_t> &out, double value) {
  assert(std::isfinite(value));
  if (value == 0.0) {
    value = 0.0; // Canonicalize -0.0: equal states must hash equal.
  }
  std::uint64_t bits = 0;
  std::memcpy(&bits, &value, sizeof(bits));
  appendU64(out, bits);
}

} // namespace

CampaignState::CampaignState(CampaignConfig config, const TimeField &field)
    : config_(std::move(config)), field_(&field),
      // Band radii are validated at placement time (addFleet / PlaceFleet),
      // where the horizon gate belongs; the authority station and the turn
      // length are structural and gate construction itself.
      valid_(std::isfinite(config_.secondsPerTurn) && config_.secondsPerTurn > 0.0 &&
             field.isValidStationRadius(config_.authorityRadiusCm)),
      clock_(valid_ ? config_.secondsPerTurn : 1.0) {}

Fleet *CampaignState::findFleet(FleetId fleetId) {
  for (Fleet &fleet : fleets_) {
    if (fleet.id == fleetId) {
      return &fleet;
    }
  }
  return nullptr;
}

double CampaignState::bandRadiusCm(int bandIndex) const {
  assert(bandIndex >= 0 && static_cast<std::size_t>(bandIndex) < config_.bandRadiusCm.size());
  return config_.bandRadiusCm.at(static_cast<std::size_t>(bandIndex));
}

FleetId CampaignState::addFleet(FleetCapability capability, int bandIndex) {
  if (!valid_ || bandIndex < 0 ||
      static_cast<std::size_t>(bandIndex) >= config_.bandRadiusCm.size() ||
      !field_->isValidStationRadius(config_.bandRadiusCm.at(static_cast<std::size_t>(bandIndex)))) {
    return K_INVALID_FLEET_ID;
  }
  Fleet fleet;
  fleet.id = nextFleetId_++;
  fleet.capability = capability;
  fleet.bandIndex = bandIndex;
  fleets_.push_back(std::move(fleet));
  return fleets_.back().id;
}

bool CampaignState::issueCommand(const Command &command) {
  if (!valid_) {
    return false;
  }
  const Fleet *fleet = findFleet(command.fleet);
  if (fleet == nullptr) {
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
  // delay from the authority station to the fleet's CURRENT band, quantized
  // once to whole turns (ceil -- an order never lands early).
  const double delaySec =
      field_->signalDelaySec(config_.authorityRadiusCm, bandRadiusCm(fleet->bandIndex));
  LoggedCommand logged;
  logged.command = command;
  logged.issueTurn = clock_.turn();
  logged.effectTurn = clock_.turn() + clock_.ceilTurns(delaySec);
  commandLog_.push_back(logged);

  Delivery delivery;
  delivery.kind = DeliveryKind::Command;
  delivery.effectTurn = logged.effectTurn;
  delivery.sequence = nextSequence_++;
  delivery.commandIndex = static_cast<std::uint32_t>(commandLog_.size() - 1);
  deliveryQueue_.push_back(delivery);
  return true;
}

void CampaignState::applyCommand(const LoggedCommand &logged) {
  Fleet *fleet = findFleet(logged.command.fleet);
  assert(fleet != nullptr);
  switch (logged.command.type) {
  case CommandType::PlaceFleet:
    fleet->bandIndex = logged.command.targetBand;
    break;
  case CommandType::AssignTask: {
    const TaskId taskId = taskGraph_.addTask(fleet->id, logged.command.properTimeCostSec);
    fleet->assignedTasks.push_back(taskId);
    break;
  }
  }
}

void CampaignState::deliverDue() {
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
  for (const Delivery &delivery : due) {
    switch (delivery.kind) {
    case DeliveryKind::Command:
      applyCommand(commandLog_.at(delivery.commandIndex));
      break;
    case DeliveryKind::CompletionReport: {
      IntelReport report;
      report.receivedTurn = clock_.turn();
      report.completedTurn = delivery.completedTurn;
      report.task = delivery.task;
      report.fleet = delivery.fleet;
      intelLog_.push_back(report);
      break;
    }
    }
  }
  deliveryQueue_ = std::move(remaining);
}

void CampaignState::advanceTurn() {
  if (!valid_) {
    return;
  }
  clock_.advance();
  deliverDue();
  taskGraph_.activateEligible();
  for (Fleet &fleet : fleets_) {
    const double rate = field_->properTimeRate(bandRadiusCm(fleet.bandIndex));
    accrueProperTime(fleet, rate, clock_.secondsPerTurn());
    const double budgetSec = properDeltaSec(rate, clock_.secondsPerTurn());
    const std::vector<TaskId> completed = taskGraph_.advanceFleetTasks(fleet.id, budgetSec);
    for (const TaskId taskId : completed) {
      // Telemetry rides the same causal queue as orders, outbound this time:
      // the authority learns of near-horizon completions late.
      const double reportDelaySec =
          field_->signalDelaySec(bandRadiusCm(fleet.bandIndex), config_.authorityRadiusCm);
      Delivery delivery;
      delivery.kind = DeliveryKind::CompletionReport;
      delivery.effectTurn = clock_.turn() + clock_.ceilTurns(reportDelaySec);
      delivery.sequence = nextSequence_++;
      delivery.completedTurn = clock_.turn();
      delivery.task = taskId;
      delivery.fleet = fleet.id;
      deliveryQueue_.push_back(delivery);
    }
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
  view.authorityRadiusCm = config_.authorityRadiusCm;
  view.authorityProperTimeRate =
      valid_ ? field_->properTimeRate(config_.authorityRadiusCm) : 0.0;
  view.innerBoundaryRadiusCm = field_->innerBoundaryRadiusCm();

  view.bands.reserve(config_.bandRadiusCm.size());
  for (std::size_t bandIndex = 0; bandIndex < config_.bandRadiusCm.size(); ++bandIndex) {
    BandView band;
    band.index = static_cast<int>(bandIndex);
    band.radiusCm = config_.bandRadiusCm.at(bandIndex);
    band.validStation = field_->isValidStationRadius(band.radiusCm);
    if (band.validStation) {
      band.properTimeRate = field_->properTimeRate(band.radiusCm);
      band.delayToAuthoritySec = field_->signalDelaySec(band.radiusCm, config_.authorityRadiusCm);
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
    fleetView.properTimeRate = field_->properTimeRate(bandRadiusCm(fleet.bandIndex));
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
    }
  }

  view.intel.reserve(intelLog_.size());
  for (const IntelReport &report : intelLog_) {
    IntelView intelView;
    intelView.receivedTurn = report.receivedTurn;
    intelView.completedTurn = report.completedTurn;
    intelView.task = report.task;
    intelView.fleet = report.fleet;
    view.intel.push_back(intelView);
  }
  return view;
}

std::vector<std::uint8_t> CampaignState::serializeState() const {
  std::vector<std::uint8_t> out;
  appendU64(out, config_.seed);
  appendF64(out, config_.secondsPerTurn);
  appendF64(out, config_.authorityRadiusCm);
  appendU32(out, static_cast<std::uint32_t>(config_.bandRadiusCm.size()));
  for (const double radiusCm : config_.bandRadiusCm) {
    appendF64(out, radiusCm);
  }
  appendI64(out, clock_.turn());
  appendU32(out, static_cast<std::uint32_t>(fleets_.size()));
  for (const Fleet &fleet : fleets_) {
    appendU32(out, fleet.id);
    appendU8(out, static_cast<std::uint8_t>(fleet.capability));
    appendI32(out, fleet.bandIndex);
    appendF64(out, fleet.reliability);
    appendF64(out, fleet.properTimeSec);
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
    appendF64(out, logged.command.properTimeCostSec);
    appendI64(out, logged.issueTurn);
    appendI64(out, logged.effectTurn);
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
  }
  appendU32(out, static_cast<std::uint32_t>(intelLog_.size()));
  for (const IntelReport &report : intelLog_) {
    appendI64(out, report.receivedTurn);
    appendI64(out, report.completedTurn);
    appendU32(out, report.task);
    appendU32(out, report.fleet);
  }
  appendU32(out, nextFleetId_);
  appendU32(out, nextSequence_);
  return out;
}

std::uint64_t CampaignState::stateDigest() const {
  // FNV-1a 64-bit: a cheap comparison aid over the full serialization, not a
  // security or sole-equality mechanism.
  const std::vector<std::uint8_t> bytes = serializeState();
  std::uint64_t hash = 14695981039346656037ULL;
  for (std::uint8_t byte : bytes) {
    hash ^= byte;
    hash *= 1099511628211ULL;
  }
  return hash;
}

} // namespace game
