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
#include <optional>
#include <string_view>
#include <vector>

#include "game/campaign_view.h"
#include "game/command.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/station_node.h"
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
  /// The authority's clock: hovering or on an orbit.
  Observer authorityObserver = Observer::Hovering;
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

  // Capability effects. Every fleet does the same work; its
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

  // Instability and containment. The singularity destabilizes over
  // the campaign: instability rises each turn and erodes ALL yield through a
  // smooth saturating factor 1 / (1 + instability * instabilityYieldPenaltyPerUnit),
  // so pure outer-band play still functions, only more slowly as the disturbance
  // grows -- it is escalating pressure, not a death gate. A prograde fleet
  // working INSIDE the ergosphere produces containment (the ergosphere mission
  // beyond extraction), suppressing instability in proportion to the proper time
  // it works, scaled by ergoregion depth. The outcome is a vector the player
  // weights -- banked energy, stabilization achieved, fleet integrity preserved,
  // turns to clear -- so the deep dive buys a faster clear and stabilization at
  // an integrity cost rather than being mandatory. Defaults are no-ops.
  double instabilityPerTurn = 0.0;             ///< Instability rise per coordinate turn; 0 = mechanic off.
  double instabilityYieldPenaltyPerUnit = 0.0; ///< Yield erosion coefficient; factor = 1/(1+instability*this).
  double ergoContainmentPerProperDay = 0.0;    ///< Instability suppressed per proper-day of prograde ergoregion work.
  // Deep prograde near-horizon work is hazardous beyond ordinary wear: tidal and
  // frame-dragging stress degrades a fleet in proportion to ergoregion depth.
  // This is the integrity the deep lane spends -- the cost side of the stabilize/
  // clear-fast payoff, which co-located verification only partly offsets.
  double ergoHazardWearPerProperDay = 0.0;     ///< Extra reliability wear per proper-day, scaled by ergoregion depth.
  // Stabilization rivals extraction. A prograde ergoregion fleet
  // spends its proper time either taming the disturbance or harvesting energy,
  // not both: while the containment mechanic is on, such a fleet banks only this
  // fraction of its yield. Below 1.0 the deep lane sacrifices energy for
  // stabilization, so the high-stabilization line banks FEWER energy units than
  // pure outer play -- the two are genuine rival objectives the player weights,
  // not joint outputs of one dive. Default 1.0 leaves yield unpenalized.
  double containmentYieldRetention = 1.0;      ///< Yield a stabilizing (deep prograde) fleet keeps; < 1 makes it a sacrifice.
  // The payoff that makes stabilization worth its energy cost: reaching this much
  // cumulative stabilization is an ALTERNATE victory, so the campaign offers two
  // ends -- bank the energy target, or tame the singularity. Pursuing the second
  // sacrifices energy (containmentYieldRetention), so which to chase is a genuine
  // choice of objective, not a dominated afterthought. Zero disables the path.
  double victoryStabilizationUnits = 0.0;      ///< Stabilization that wins the campaign outright; 0 = off.

  // Colonies and the story. Each colony is a node (ids from
  // K_FIRST_COLONY_NODE, in this order) with its own exact clock; the host is
  // the authority node. The story's events run at those nodes. A tech tier is
  // a scored axis: reaching victoryTechTier at any colony wins outright.
  std::vector<ColonyConfig> colonies;
  EventSet story;
  std::int64_t victoryTechTier = 0; ///< Tech tier that wins the campaign; 0 = off.
};

class CampaignState {
public:
  /** @brief The field reference must outlive the campaign. The authority
   *         radius and every band radius must satisfy isValidStationRadius;
   *         valid() reports whether construction accepted the config. */
  CampaignState(CampaignConfig config, const TimeField &field);

  [[nodiscard]] bool valid() const { return valid_; }
  [[nodiscard]] const CampaignConfig &config() const { return config_; }

  /** @brief Setup-phase fleet creation at the authority's direction; returns
   *         K_INVALID_FLEET_ID when bandIndex is out of range or the placement
   *         is inadmissible (see placementAllowed). Fleets orbit by default. */
  FleetId addFleet(FleetCapability capability, int bandIndex,
                   OrbitLane lane = OrbitLane::Prograde,
                   StationKeeping station = StationKeeping::Orbit);

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
  [[nodiscard]] double instability() const { return instability_; }
  [[nodiscard]] double stabilization() const { return stabilization_; }
  /** @brief Coordinate turn the victory energy was first reached; 0 until won. */
  [[nodiscard]] std::int64_t clearedTurn() const { return clearedTurn_; }
  [[nodiscard]] const std::vector<Fleet> &fleets() const { return fleets_; }
  [[nodiscard]] const TaskGraph &taskGraph() const { return taskGraph_; }
  [[nodiscard]] const std::vector<LoggedCommand> &commandLog() const { return commandLog_; }
  [[nodiscard]] const std::vector<IntelReport> &intelLog() const { return intelLog_; }
  /** @brief The host (index 0) and every colony, indexed by NodeId. */
  [[nodiscard]] const std::vector<StationNode> &nodes() const { return nodes_; }
  /** @brief Every node-to-node delivery that has reached a live node, in
   *         arrival order. */
  [[nodiscard]] const std::vector<ArrivalRecord> &arrivals() const { return arrivals_; }
  /** @brief Tech tier of a node: the number of story tiers its points meet. */
  [[nodiscard]] std::int64_t techTier(NodeId node) const;
  /** @brief Highest tech tier any colony holds -- the tech axis of the outcome. */
  [[nodiscard]] std::int64_t colonyTechTier() const;
  /** @brief A story parameter's resolved value (seeded ones drawn from the
   *         campaign seed); nullopt when the story has no such parameter. */
  [[nodiscard]] std::optional<std::int64_t> storyParam(std::string_view name) const;
  /** @brief Signal delay between two nodes in whole turns, as quantized at
   *         emission. */
  [[nodiscard]] std::int64_t nodeDelayTurns(NodeId from, NodeId to) const;

  /** @brief Immutable render-facing view for the UI layer: plain values, no
   *         pointers into campaign storage. The VIEW contract; grows per UI
   *         slice independently of serializeState(). */
  [[nodiscard]] CampaignViewSnapshot renderSnapshot() const;

  /** @brief Deterministic field-by-field byte serialization of the full
   *         campaign state (explicit widths, -0.0 canonicalized, every double
   *         finite). Determinism artifact, not a versioned save format: it
   *         captures the config, the field's spin deficit, every station's
   *         observer, and the mutable runtime state, but not the field's mass
   *         nor the task graph's next-id counter, which are fixed by the
   *         scenario. Two runs of the same scenario on the same
   *         field compare equal; comparing across different fields is out of
   *         scope. */
  [[nodiscard]] std::vector<std::uint8_t> serializeState() const;

  /** @brief FNV-1a 64 over serializeState() -- a cheap comparison aid. */
  [[nodiscard]] std::uint64_t stateDigest() const;

private:
  enum class DeliveryKind : std::uint8_t {
    Command = 0,
    CompletionReport = 1,
    ColonyReport = 2, ///< A colony's local-tick production, banked at the host.
    TechPacket = 3,   ///< Story technology data between nodes.
    EventNotice = 4,  ///< Story message between nodes.
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
    std::int64_t emitTurn = 0;            ///< Coordinate turn the signal left its sender.
    NodeId sender = K_NO_NODE;            ///< Emitting node; K_NO_NODE for fleet reports.
    NodeId destination = K_AUTHORITY_NODE; ///< Receiving node (fleet deliveries: unused).
    std::int64_t senderProperSecAtEmit = 0; ///< Sender's whole local seconds at emission.
    double senderEnergyUnitsAtEmit = 0.0; ///< Host's banked energy at emission (host senders).
    std::uint32_t payloadIndex = 0;       ///< Tech packet ordinal, or the notice's event id.
    std::int64_t techPoints = 0;          ///< TechPacket payload.
    EventCategory category = EventCategory::Info;
  };

  /** @brief A scheduled story event: evaluated on `turn`. */
  struct ScheduledEvent {
    std::int64_t turn = 0;
    std::uint32_t eventIndex = 0; ///< Into config_.story.events.
  };

  void evaluateOutcome();
  [[nodiscard]] double redeployFuelCost(int fromBand, int toBand) const;
  /** @brief Base geodesic delay scaled by coordination overhead, which relay
   *         fleets covering the path reduce toward the geodesic floor (never
   *         below it). */
  [[nodiscard]] double effectiveSignalDelaySec(double fromRadiusCm, double toRadiusCm) const;
  /** @brief Yield multiplier for a fleet's capability (1.0 by default). */
  [[nodiscard]] double capabilityYieldMultiplier(FleetCapability capability) const;
  /** @brief True when a fleet can hold a band with this lane and station
   *         keeping: retrograde is refused inside the ergosphere, where frame
   *         dragging forbids counter-rotation; a hovering station is a ZAMO and
   *         so carries no retrograde sense; an orbit needs a bound circular
   *         orbit of its sense at the band (outside the marginally bound
   *         radius). */
  [[nodiscard]] bool placementAllowed(OrbitLane lane, StationKeeping station, int bandIndex) const;
  /** @brief Prograde ergoregion yield multiplier (>= 1); 1 outside the ergosphere,
   *         for retrograde fleets, or when the bonus is disabled. */
  [[nodiscard]] double frameDragYieldFactor(const Fleet &fleet) const;
  /** @brief Ergoregion depth in [0,1] for a prograde fleet -- 0 at the static
   *         limit, 1 at the horizon; 0 outside the ergosphere, for retrograde
   *         fleets, or a non-rotating field. Drives both the frame-drag yield
   *         bonus and containment production. */
  [[nodiscard]] double ergoregionDepth(const Fleet &fleet) const;

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
  void receiveNodeDelivery(const Delivery &delivery);
  void buildNodes();
  void resolveStoryParams();
  /** @brief Order, uniqueness, and range checks on the configured story. */
  [[nodiscard]] bool storyWellFormed() const;
  /** @brief An IntRef inside the documented range that evaluates without
   *         overflow against the resolved parameters. */
  [[nodiscard]] bool intRefValid(const IntRef &ref) const;
  [[nodiscard]] std::int64_t resolve(const IntRef &ref) const;
  /** @brief Advances every node clock one turn and ships colony production. */
  void advanceNodeClocks();
  void evaluateStory();
  [[nodiscard]] bool predicateHolds(const EventPredicate &predicate, const StationNode &node) const;
  void applyEffect(const EventEffect &effect, const EventDef &event, StationNode &node);
  void emitNodeDelivery(DeliveryKind kind, const StationNode &sender, NodeId destination,
                        EventCategory category, std::uint32_t payloadIndex,
                        std::int64_t techPoints, double yieldUnits);
  [[nodiscard]] double nodeDelaySec(NodeId from, NodeId to) const;
  void appendStoryState(std::vector<std::uint8_t> &out) const;
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
  double instability_ = 0.0;     ///< Rises each turn, suppressed by containment; erodes yield.
  double stabilization_ = 0.0;   ///< Cumulative containment produced -- the stabilization score axis.
  std::int64_t clearedTurn_ = 0; ///< Turn the victory energy was first reached; 0 until then.
  CampaignStatus status_ = CampaignStatus::Ongoing;
  std::vector<StationNode> nodes_;            ///< Host at index 0, then colonies.
  std::vector<std::int64_t> storyParams_;     ///< Resolved story parameters, by index.
  std::vector<std::uint8_t> eventFired_;      ///< Once-events that have fired, by index.
  std::vector<ScheduledEvent> scheduledEvents_;
  std::vector<ArrivalRecord> arrivals_;
  double energyLostToDarkness_ = 0.0;         ///< Production that reached a dark host.
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_H
