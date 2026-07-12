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

#include <array>
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
  double yieldUnits = 0.0; ///< Energy banked when this report arrived.
  bool corrupted = false;  ///< Yield was discounted: the source's telemetry was unreliable.
};

struct CampaignConfig {
  std::uint64_t seed = 0;
  double secondsPerTurn = 3600.0;
  double authorityRadiusCm = 0.0;   ///< Command origin (human authority station).
  std::vector<double> bandRadiusCm; ///< Orbital bands, any order, indexed by bandIndex.

  // Economy. Yield per task = properHours * (1/dtau_dt at completion band) *
  // reliability at completion: deep work is worth more per local hour exactly
  // because local hours are scarce there. Energy is banked when the report
  // ARRIVES at the authority, never at completion.
  double victoryEnergyUnits = 0.0;         ///< Win when banked energy reaches this; 0 = off.
  std::int64_t deadlineTurn = 0;           ///< Lose when the clock reaches this; 0 = off.
  double fleetInitialFuelUnits = 100.0;    ///< Starting redeployment budget per fleet.
  double fuelPerBandHop = 20.0;            ///< Redeploy cost per band of separation.
  double reliabilityWearPerProperDay = 0.0;///< Reliability lost per local day worked.
  double reliabilityFloor = 0.5;           ///< Wear never degrades a fleet below this.
  // Frame dragging (Kerr fields only). A prograde fleet working inside the
  // ergosphere taps the hole's rotational energy: yield is scaled by
  // 1 + frameDragYieldBonus * ergoregionDepth, where depth runs 0 at the
  // static limit to 1 at the horizon. Retrograde or non-rotating: no bonus.
  double frameDragYieldBonus = 0.0;        ///< Prograde ergoregion yield coefficient; 0 = off.

  // Capability effects (CAMPAIGN-5). Every fleet does the same work; its
  // capability decides what that work is WORTH and what side effect it has.
  // Defaults are no-ops so a config that leaves them unset behaves exactly like
  // the pre-capability economy. Fabrication and Verification act BAND-LOCALLY:
  // they touch only fleets sharing the completing fleet's band, so protecting a
  // deep dive fleet means co-locating support in the same band.
  std::array<double, 5> capabilityYieldMultiplier = {1.0, 1.0, 1.0, 1.0, 1.0};
  double signalOverheadFactor = 1.0;            ///< Coordination latency on base geodesic delay (>= 1).
  double relayDelayFraction = 0.0;              ///< Overhead each covering relay removes, toward the 1.0 floor.
  double fabricationFuelRestore = 0.0;          ///< Fuel a fabrication completion restores to co-band fleets.
  double verificationReliabilityRestore = 0.0;  ///< Reliability a verification completion restores to co-band fleets.
  double reliabilityCorruptionThreshold = 0.0;  ///< Below this reliability at completion, the report is corrupted.
  double corruptedYieldFraction = 1.0;          ///< Fraction of yield banked from a corrupted report.
};

class CampaignState {
public:
  /** @brief The field reference must outlive the campaign. The authority
   *         radius and every band radius must satisfy isValidStationRadius;
   *         valid() reports whether construction accepted the config. */
  CampaignState(CampaignConfig config, const TimeField &field);

  [[nodiscard]] bool valid() const { return valid_; }

  /** @brief Setup-phase fleet creation at the authority's direction; returns
   *         K_INVALID_FLEET_ID when bandIndex is out of range or the lane is
   *         retrograde inside the ergosphere. */
  FleetId addFleet(FleetCapability capability, int bandIndex,
                   OrbitLane lane = OrbitLane::Prograde);

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
  [[nodiscard]] CampaignStatus status() const { return status_; }
  [[nodiscard]] double energyUnits() const { return energyUnits_; }
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
    double yieldUnits = 0.0; ///< Fixed at completion (band + reliability then).
    bool corrupted = false;  ///< Source reliability was below the corruption threshold.
  };

  void evaluateOutcome();
  [[nodiscard]] double redeployFuelCost(int fromBand, int toBand) const;
  /** @brief Base geodesic delay scaled by coordination overhead, which relay
   *         fleets covering the path reduce toward the geodesic floor (never
   *         below it). */
  [[nodiscard]] double effectiveSignalDelaySec(double fromRadiusCm, double toRadiusCm) const;
  /** @brief Yield multiplier for a fleet's capability (1.0 by default). */
  [[nodiscard]] double capabilityYieldMultiplier(FleetCapability capability) const;
  /** @brief True when a lane can be held at a band: retrograde is refused at or
   *         inside the ergosphere, where frame dragging forbids counter-rotation. */
  [[nodiscard]] bool laneAllowedAtBand(OrbitLane lane, int bandIndex) const;
  /** @brief Prograde ergoregion yield multiplier (>= 1); 1 outside the ergosphere,
   *         for retrograde fleets, or when the bonus is disabled. */
  [[nodiscard]] double frameDragYieldFactor(const Fleet &fleet) const;

  /** @brief A capability task finished this turn: what it was and where, so its
   *         band-local side effect can be applied after the fleet loop. */
  struct CapabilityCompletion {
    FleetCapability capability = FleetCapability::Research;
    int bandIndex = 0;
  };

  [[nodiscard]] Fleet *findFleet(FleetId fleetId);
  [[nodiscard]] double bandRadiusCm(int bandIndex) const;
  void deliverDue();
  void applyCommand(const LoggedCommand &logged);
  void applyCapabilityEffects(const std::vector<CapabilityCompletion> &completions);

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
  double energyUnits_ = 0.0;
  CampaignStatus status_ = CampaignStatus::Ongoing;
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_H
