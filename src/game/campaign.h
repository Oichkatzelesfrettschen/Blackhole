/**
 * @file campaign.h
 * @brief Deterministic campaign state: turn clock, fleets, tasks, causal delivery.
 *
 * CampaignState owns the strategic simulation and nothing else: no OpenGL
 * objects, no ImGui state, no wall-clock reads. All inputs arrive through
 * issueCommand and advanceTurn; all observable outputs are the public getters
 * plus serializeState/stateDigest. The same seed and ordered command log
 * replay to byte-identical serializations on the same binary and host.
 *
 * Causality is symmetric. Commands travel from the authority station INTO the
 * field (an order issued on turn T to a deep fleet takes effect turns later),
 * and completion reports travel back OUT (a task finished near the horizon is
 * learned about late). Both ride the same delivery queue, with arrival times
 * quantized once at emission to whole turns via ceil -- information never
 * arrives early -- so delivery is an integer compare, never a double compare.
 */

#ifndef BLACKHOLE_GAME_CAMPAIGN_H
#define BLACKHOLE_GAME_CAMPAIGN_H

#include <cstdint>
#include <vector>

#include "game/campaign_view.h"
#include "game/command.h"
#include "game/fleet.h"
#include "game/task_graph.h"
#include "game/temporal_clock.h"
#include "game/time_field.h"

namespace game {

struct LoggedCommand {
  Command command;
  std::int64_t issueTurn = 0;
  std::int64_t effectTurn = 0; ///< issueTurn + signal delay to the fleet, in turns.
};

/** @brief What the authority station has learned, and when it learned it. */
struct IntelReport {
  std::int64_t receivedTurn = 0;
  std::int64_t completedTurn = 0; ///< Coordinate turn the task actually finished.
  TaskId task = K_INVALID_TASK_ID;
  FleetId fleet = K_INVALID_FLEET_ID;
};

struct CampaignConfig {
  std::uint64_t seed = 0;
  double secondsPerTurn = 3600.0;
  double authorityRadiusCm = 0.0;   ///< Command origin (human authority station).
  std::vector<double> bandRadiusCm; ///< Orbital bands, any order, indexed by bandIndex.
};

class CampaignState {
public:
  /** @brief The field reference must outlive the campaign. The authority
   *         radius and every band radius must satisfy isValidStationRadius;
   *         valid() reports whether construction accepted the config. */
  CampaignState(CampaignConfig config, const TimeField &field);

  [[nodiscard]] bool valid() const { return valid_; }

  /** @brief Setup-phase fleet creation at the authority's direction; returns
   *         K_INVALID_FLEET_ID when bandIndex is out of range. */
  FleetId addFleet(FleetCapability capability, int bandIndex);

  /** @brief Validates and enqueues a command. Returns false and leaves ALL
   *         state untouched (log included) when validation fails -- an invalid
   *         order never enters the queue, so it can never advance a task.
   *         Accepted commands take effect at issue turn + ceil(signal delay
   *         from the authority station to the fleet's current band). */
  bool issueCommand(const Command &command);

  /** @brief One coordinate turn: advance clock -> deliver due commands and
   *         reports -> accrue proper time -> advance tasks -> emit completion
   *         reports with causal arrival turns. */
  void advanceTurn();

  /** @brief turnCount iterated single-turn advances (op-order invariant). */
  void advanceTurns(std::int64_t turnCount);

  [[nodiscard]] std::int64_t turn() const { return clock_.turn(); }
  [[nodiscard]] const std::vector<Fleet> &fleets() const { return fleets_; }
  [[nodiscard]] const TaskGraph &taskGraph() const { return taskGraph_; }
  [[nodiscard]] const std::vector<LoggedCommand> &commandLog() const { return commandLog_; }
  [[nodiscard]] const std::vector<IntelReport> &intelLog() const { return intelLog_; }

  /** @brief Immutable render-facing view for the UI layer: plain values, no
   *         pointers into campaign storage. The VIEW contract; grows per UI
   *         slice independently of serializeState(). */
  [[nodiscard]] CampaignViewSnapshot renderSnapshot() const;

  /** @brief Deterministic field-by-field byte serialization of the full
   *         campaign state (explicit widths, -0.0 canonicalized, every double
   *         finite). Determinism artifact, not a versioned save format. */
  [[nodiscard]] std::vector<std::uint8_t> serializeState() const;

  /** @brief FNV-1a 64 over serializeState() -- a cheap comparison aid. */
  [[nodiscard]] std::uint64_t stateDigest() const;

private:
  enum class DeliveryKind : std::uint8_t {
    Command = 0,
    CompletionReport = 1,
  };

  struct Delivery {
    DeliveryKind kind = DeliveryKind::Command;
    std::int64_t effectTurn = 0;
    std::uint32_t sequence = 0;    ///< Emission order; total tie-break within a turn.
    std::uint32_t commandIndex = 0; ///< Into commandLog_ for Command deliveries.
    std::int64_t completedTurn = 0;
    TaskId task = K_INVALID_TASK_ID;
    FleetId fleet = K_INVALID_FLEET_ID;
  };

  [[nodiscard]] Fleet *findFleet(FleetId fleetId);
  [[nodiscard]] double bandRadiusCm(int bandIndex) const;
  void deliverDue();
  void applyCommand(const LoggedCommand &logged);

  CampaignConfig config_;
  const TimeField *field_; ///< Never null; the field outlives the campaign.
  bool valid_ = false;
  TemporalClock clock_;
  std::vector<Fleet> fleets_;
  TaskGraph taskGraph_;
  std::vector<LoggedCommand> commandLog_;
  std::vector<Delivery> deliveryQueue_;
  std::vector<IntelReport> intelLog_;
  FleetId nextFleetId_ = 1;
  std::uint32_t nextSequence_ = 0;
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_H
