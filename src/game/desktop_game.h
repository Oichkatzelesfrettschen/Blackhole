#ifndef BLACKHOLE_GAME_DESKTOP_GAME_H
#define BLACKHOLE_GAME_DESKTOP_GAME_H

#include <cstdint>
#include <memory>
#include <vector>

#include "game/constellation_session.h"

namespace game {

struct RecordedOrder {
  std::int64_t issueTurn = 0;
  ConstellationCommand command;
};

enum class GameEventKind : std::uint8_t {
  OrderIssued,
  FleetReport,
  ArrivalReport,
  ControlObservation,
  ContestedOrUnknown,
  EnergyReport,
  StabilizationReport,
  ControlReport,
  OutcomeNotice
};

struct GameEvent {
  GameEventKind kind = GameEventKind::OrderIssued;
  std::int64_t receivedTurn = 0;
  FleetId fleet = K_INVALID_FLEET_ID;
  SystemId system = K_INVALID_SYSTEM_ID;
  int band = 0;
};

enum class SaveError : std::uint8_t {
  None,
  Truncated,
  Schema,
  InvalidCommand,
  DigestMismatch,
  TrailingData
};

class DesktopGame {
public:
  static constexpr std::uint32_t K_SAVE_SCHEMA = 1;
  static constexpr std::uint32_t K_SCENARIO_SCHEMA = 1;

  explicit DesktopGame(std::uint64_t seed = 1,
                       FactionPolicy rivalPolicy = FactionPolicy::Expansionist);
  [[nodiscard]] const Constellation &state() const { return session_.constellation(); }
  [[nodiscard]] ConstellationViewSnapshot snapshot() const { return state().renderSnapshot(); }
  [[nodiscard]] OrderPreview preview(const ConstellationCommand &command) const;
  [[nodiscard]] OrderRejection issue(const ConstellationCommand &command);
  void advanceTurn();
  [[nodiscard]] std::vector<std::uint8_t> save() const;
  [[nodiscard]] static std::unique_ptr<DesktopGame> load(const std::vector<std::uint8_t> &bytes,
                                                         SaveError &error);
  [[nodiscard]] const std::vector<RecordedOrder> &orders() const { return orders_; }
  [[nodiscard]] const std::vector<GameEvent> &events() const { return events_; }
  [[nodiscard]] const std::vector<std::uint64_t> &turnDigests() const { return turnDigests_; }
  [[nodiscard]] std::uint64_t seed() const { return seed_; }
  [[nodiscard]] FactionPolicy rivalPolicy() const { return rivalPolicy_; }

private:
  std::uint64_t seed_;
  FactionPolicy rivalPolicy_;
  ConstellationSession session_;
  std::vector<RecordedOrder> orders_;
  std::vector<GameEvent> events_;
  std::vector<std::uint64_t> turnDigests_;
};

} // namespace game

#endif
