#include "game/desktop_game.h"

#include <cstddef>
#include <cstdint>
#include <memory>
#include <utility>
#include <vector>

#include "game/constellation.h"
#include "game/constellation_session.h"
#include "game/constellation_types.h"
#include "game/constellation_view.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/serialize_bytes.h"

namespace game {
namespace {

std::vector<std::uint8_t> scenarioBytes(std::uint64_t seed) {
  const ConstellationConfig config = defaultConstellationConfig(seed);
  std::vector<std::uint8_t> bytes;
  serial::appendU64(bytes, config.seed);
  serial::appendF64(bytes, config.secondsPerTurn);
  serial::appendU32(bytes, static_cast<std::uint32_t>(config.systems.size()));
  for (const SystemSpec &system : config.systems) {
    serial::appendF64(bytes, system.blackHoleMassG);
    serial::appendF64(bytes, system.spinDimensionless);
    serial::appendF64(bytes, system.authorityRadiusCm);
    serial::appendU8(bytes, static_cast<std::uint8_t>(system.authorityObserver));
    serial::appendU32(bytes, static_cast<std::uint32_t>(system.bandRadiusCm.size()));
    for (const double radius : system.bandRadiusCm) {
      serial::appendF64(bytes, radius);
    }
  }
  serial::appendU32(bytes, static_cast<std::uint32_t>(config.links.size()));
  for (const InterSystemLink &link : config.links) {
    serial::appendU32(bytes, link.a);
    serial::appendU32(bytes, link.b);
    serial::appendF64(bytes, link.separationCm);
  }
  serial::appendF64(bytes, config.victoryEnergyUnits);
  serial::appendF64(bytes, config.victoryStabilizationUnits);
  serial::appendF64(bytes, config.victoryControlScore);
  serial::appendI64(bytes, config.deadlineTurn);
  serial::appendF64(bytes, config.workProperHoursPerReport);
  serial::appendF64(bytes, config.fleetInitialFuelUnits);
  serial::appendF64(bytes, config.fuelPerBandHop);
  serial::appendF64(bytes, config.interSystemTravelSpeedFraction);
  serial::appendF64(bytes, config.interSystemTravelFuelUnits);
  for (const double multiplier : config.capabilityYieldMultiplier) {
    serial::appendF64(bytes, multiplier);
  }
  serial::appendF64(bytes, config.reliabilityWearPerProperDay);
  serial::appendF64(bytes, config.reliabilityFloor);
  serial::appendF64(bytes, config.frameDragYieldBonus);
  serial::appendF64(bytes, config.instabilityPerTurn);
  serial::appendF64(bytes, config.instabilityYieldPenaltyPerUnit);
  serial::appendF64(bytes, config.ergoContainmentPerProperDay);
  serial::appendF64(bytes, config.ergoHazardWearPerProperDay);
  serial::appendF64(bytes, config.containmentYieldRetention);
  serial::appendF64(bytes, config.controlPointsPerBandPerTurn);
  return bytes;
}

} // namespace

DesktopGame::DesktopGame(std::uint64_t seed, FactionPolicy rivalPolicy)
    : seed_(seed), rivalPolicy_(rivalPolicy), session_(seed, rivalPolicy),
      turnDigests_{session_.constellation().stateDigest()} {}

OrderPreview DesktopGame::preview(const ConstellationCommand &command) const {
  return state().previewCommand(session_.player(), command);
}

OrderRejection DesktopGame::issue(const ConstellationCommand &command) {
  const OrderPreview plan = preview(command);
  if (plan.rejection != OrderRejection::None) {
    return plan.rejection;
  }
  if (!session_.movePlayerFleet(command.fleet, command.targetSystem, command.targetBand,
                                command.lane, command.station)) {
    return OrderRejection::InvalidSession;
  }
  orders_.push_back(RecordedOrder{.issueTurn = state().turn(), .command = command});
  events_.push_back(GameEvent{.kind = GameEventKind::OrderIssued,
                              .receivedTurn = state().turn(),
                              .fleet = command.fleet,
                              .system = command.targetSystem,
                              .band = command.targetBand});
  turnDigests_.back() = state().stateDigest();
  return OrderRejection::None;
}

void DesktopGame::advanceTurn() {
  const ConstellationViewSnapshot before = snapshot();
  session_.constellation().advanceTurn();
  const ConstellationViewSnapshot after = snapshot();
  for (std::size_t systemIndex = 0; systemIndex < after.systems.size(); ++systemIndex) {
    const SystemStanding &current = after.systems.at(systemIndex);
    const SystemStanding &previous = before.systems.at(systemIndex);
    for (std::size_t bandIndex = 0; bandIndex < current.bandController.size(); ++bandIndex) {
      if (current.bandController.at(bandIndex) != previous.bandController.at(bandIndex)) {
        events_.push_back(
            GameEvent{.kind = current.bandController.at(bandIndex) == K_INVALID_FACTION_ID
                                  ? GameEventKind::ContestedOrUnknown
                                  : GameEventKind::ControlObservation,
                      .receivedTurn = after.turn,
                      .system = current.id,
                      .band = static_cast<int>(bandIndex)});
      }
    }
  }
  for (std::size_t index = 0; index < after.fleets.size(); ++index) {
    const ConstellationFleetView &current = after.fleets.at(index);
    const ConstellationFleetView &previous = before.fleets.at(index);
    if (current.reportedTurn != previous.reportedTurn) {
      events_.push_back(GameEvent{.kind = previous.inTransit && !current.inTransit
                                              ? GameEventKind::ArrivalReport
                                              : GameEventKind::FleetReport,
                                  .receivedTurn = after.turn,
                                  .fleet = current.id,
                                  .system = current.system,
                                  .band = current.bandIndex});
    }
  }
  if (after.player.energyUnits != before.player.energyUnits) {
    events_.push_back(GameEvent{.kind = GameEventKind::EnergyReport, .receivedTurn = after.turn});
  }
  if (after.player.stabilizationUnits != before.player.stabilizationUnits) {
    events_.push_back(
        GameEvent{.kind = GameEventKind::StabilizationReport, .receivedTurn = after.turn});
  }
  if (after.player.controlScore != before.player.controlScore) {
    events_.push_back(GameEvent{.kind = GameEventKind::ControlReport, .receivedTurn = after.turn});
  }
  if (after.overallStatus != before.overallStatus) {
    events_.push_back(GameEvent{.kind = GameEventKind::OutcomeNotice, .receivedTurn = after.turn});
  }
  turnDigests_.push_back(state().stateDigest());
}

std::vector<std::uint8_t> DesktopGame::save() const {
  std::vector<std::uint8_t> bytes;
  serial::appendU8(bytes, static_cast<std::uint8_t>('B'));
  serial::appendU8(bytes, static_cast<std::uint8_t>('H'));
  serial::appendU8(bytes, static_cast<std::uint8_t>('G'));
  serial::appendU8(bytes, static_cast<std::uint8_t>('M'));
  serial::appendU32(bytes, K_SAVE_SCHEMA);
  serial::appendU32(bytes, K_SCENARIO_SCHEMA);
  serial::appendU64(bytes, seed_);
  serial::appendU8(bytes, static_cast<std::uint8_t>(rivalPolicy_));
  const std::vector<std::uint8_t> config = scenarioBytes(seed_);
  serial::appendU32(bytes, static_cast<std::uint32_t>(config.size()));
  bytes.insert(bytes.end(), config.begin(), config.end());
  serial::appendU64(bytes, orders_.size());
  serial::appendU64(bytes, turnDigests_.size());
  for (const RecordedOrder &order : orders_) {
    serial::appendI64(bytes, order.issueTurn);
    serial::appendU32(bytes, order.command.fleet);
    serial::appendU32(bytes, order.command.targetSystem);
    serial::appendI32(bytes, order.command.targetBand);
    serial::appendU8(bytes, static_cast<std::uint8_t>(order.command.lane));
    serial::appendU8(bytes, static_cast<std::uint8_t>(order.command.station));
  }
  for (const std::uint64_t digest : turnDigests_) {
    serial::appendU64(bytes, digest);
  }
  const std::vector<std::uint8_t> stateBytes = state().serializeState();
  serial::appendU64(bytes, stateBytes.size());
  bytes.insert(bytes.end(), stateBytes.begin(), stateBytes.end());
  serial::appendU64(bytes, state().stateDigest());
  serial::appendU8(bytes, static_cast<std::uint8_t>(state().overallStatus()));
  return bytes;
}

namespace {

SaveError replayCommands(DesktopGame &game, const std::vector<RecordedOrder> &orders,
                         const std::vector<std::uint64_t> &digests) {
  std::size_t orderIndex = 0;
  for (std::size_t turnIndex = 0; turnIndex < digests.size(); ++turnIndex) {
    while (orderIndex < orders.size() &&
           std::cmp_equal(orders.at(orderIndex).issueTurn, turnIndex)) {
      if (game.issue(orders.at(orderIndex).command) != OrderRejection::None) {
        return SaveError::InvalidCommand;
      }
      ++orderIndex;
    }
    if (orderIndex < orders.size() && std::cmp_less(orders.at(orderIndex).issueTurn, turnIndex)) {
      return SaveError::InvalidCommand;
    }
    if (turnIndex > 0 && game.turnDigests().at(turnIndex - 1) != digests.at(turnIndex - 1)) {
      return SaveError::DigestMismatch;
    }
    if (turnIndex + 1 < digests.size()) {
      game.advanceTurn();
    }
  }
  return orderIndex == orders.size() ? SaveError::None : SaveError::InvalidCommand;
}

} // namespace

std::unique_ptr<DesktopGame> DesktopGame::load(const std::vector<std::uint8_t> &bytes,
                                               SaveError &error) {
  error = SaveError::Truncated;
  serial::ByteReader reader(bytes.data(), bytes.size());
  std::uint8_t magic[4]{};
  for (std::uint8_t &character : magic) {
    if (!reader.readU8(character)) {
      return nullptr;
    }
  }
  std::uint32_t saveSchema = 0;
  std::uint32_t scenarioSchema = 0;
  std::uint64_t scenarioSeed = 0;
  std::uint8_t policyValue = 0;
  std::uint32_t configSize = 0;
  std::uint64_t orderCount = 0;
  std::uint64_t digestCount = 0;
  if (!reader.readU32(saveSchema) || !reader.readU32(scenarioSchema) ||
      !reader.readU64(scenarioSeed) || !reader.readU8(policyValue) || !reader.readU32(configSize)) {
    return nullptr;
  }
  const std::vector<std::uint8_t> expectedConfig = scenarioBytes(scenarioSeed);
  if (configSize != expectedConfig.size() || configSize > reader.remaining()) {
    error = SaveError::Schema;
    return nullptr;
  }
  for (const std::uint8_t expected : expectedConfig) {
    std::uint8_t actual = 0;
    if (!reader.readU8(actual) || actual != expected) {
      error = SaveError::Schema;
      return nullptr;
    }
  }
  if (!reader.readU64(orderCount) || !reader.readU64(digestCount)) {
    return nullptr;
  }
  if (magic[0] != 'B' || magic[1] != 'H' || magic[2] != 'G' || magic[3] != 'M' ||
      saveSchema != K_SAVE_SCHEMA || scenarioSchema != K_SCENARIO_SCHEMA ||
      policyValue > static_cast<std::uint8_t>(FactionPolicy::Contester)) {
    error = SaveError::Schema;
    return nullptr;
  }
  if (digestCount == 0 || orderCount > reader.remaining() / 22U ||
      digestCount > reader.remaining() / 8U) {
    return nullptr;
  }
  std::vector<RecordedOrder> recordedOrders;
  recordedOrders.reserve(orderCount);
  for (std::uint64_t index = 0; index < orderCount; ++index) {
    RecordedOrder order;
    std::int32_t targetBand = 0;
    std::uint8_t lane = 0;
    std::uint8_t station = 0;
    if (!reader.readI64(order.issueTurn) || !reader.readU32(order.command.fleet) ||
        !reader.readU32(order.command.targetSystem) || !reader.readI32(targetBand) ||
        !reader.readU8(lane) || !reader.readU8(station)) {
      return nullptr;
    }
    order.command.targetBand = targetBand;
    if (lane > static_cast<std::uint8_t>(OrbitLane::Retrograde) ||
        station > static_cast<std::uint8_t>(StationKeeping::Hover)) {
      error = SaveError::InvalidCommand;
      return nullptr;
    }
    order.command.lane = static_cast<OrbitLane>(lane);
    order.command.station = static_cast<StationKeeping>(station);
    recordedOrders.push_back(order);
  }
  std::vector<std::uint64_t> digests;
  digests.reserve(digestCount);
  for (std::uint64_t index = 0; index < digestCount; ++index) {
    std::uint64_t digest = 0;
    if (!reader.readU64(digest)) {
      return nullptr;
    }
    digests.push_back(digest);
  }
  std::uint64_t stateSize = 0;
  if (!reader.readU64(stateSize) || stateSize > reader.remaining()) {
    return nullptr;
  }
  std::vector<std::uint8_t> stateBytes;
  stateBytes.reserve(stateSize);
  for (std::uint64_t index = 0; index < stateSize; ++index) {
    std::uint8_t value = 0;
    if (!reader.readU8(value)) {
      return nullptr;
    }
    stateBytes.push_back(value);
  }
  std::uint64_t finalDigest = 0;
  std::uint8_t outcome = 0;
  if (!reader.readU64(finalDigest) || !reader.readU8(outcome)) {
    return nullptr;
  }
  if (reader.remaining() != 0) {
    error = SaveError::TrailingData;
    return nullptr;
  }
  auto game = std::make_unique<DesktopGame>(scenarioSeed, static_cast<FactionPolicy>(policyValue));
  error = replayCommands(*game, recordedOrders, digests);
  if (error != SaveError::None) {
    return nullptr;
  }
  if (game->turnDigests_ != digests || game->state().serializeState() != stateBytes ||
      game->state().stateDigest() != finalDigest ||
      static_cast<std::uint8_t>(game->state().overallStatus()) != outcome) {
    error = SaveError::DigestMismatch;
    return nullptr;
  }
  error = SaveError::None;
  return game;
}

} // namespace game
