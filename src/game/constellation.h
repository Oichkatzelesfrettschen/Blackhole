/**
 * @file constellation.h
 * @brief Deterministic multi-system, multi-faction 4X over the campaign physics.
 *
 * A Constellation is several black-hole systems, linked by interstellar distance,
 * contested by several factions. It shares the single hole's determinism law --
 * the integer turn is the only loop variable, state serializes field-by-field to
 * a byte-identical digest on the same binary and host -- and extends its
 * causality: orders, yield reports, and now intelligence about who holds what all
 * ride a delivery queue whose arrival turns are quantized once at emission. A
 * faction in one system learns of a rival's move in another only after the light
 * between their authority stations arrives, so every faction, the AI included,
 * acts on stale information.
 *
 * Control is the competitive axis. A faction holds a band by stationing a fleet
 * there uncontested; holding many bands across many systems (breadth) accrues a
 * control score, and reaching the control target is an outright win. Because a
 * rival wins by domination on a clock, ignoring it -- whether to race energy or
 * to dive for stabilization -- loses to an unopposed expansion, so contesting is
 * forced rather than optional. That is what gives a spread, mid-commitment line a
 * reason to exist that pure concentration cannot dominate.
 */

#ifndef BLACKHOLE_GAME_CONSTELLATION_H
#define BLACKHOLE_GAME_CONSTELLATION_H

#include <array>
#include <cstdint>
#include <vector>

#include "game/campaign_view.h"
#include "game/constellation_types.h"
#include "game/constellation_view.h"
#include "game/fleet.h"
#include "game/temporal_clock.h"

namespace game {

/** @brief One system's fixed geometry: mass, spin, its authority radius, and its
 *         orbital bands (ascending radius). The constellation builds a
 *         KerrTimeField from mass and spin. */
struct SystemSpec {
  double blackHoleMassG = 0.0;
  double spinDimensionless = 0.0;
  double authorityRadiusCm = 0.0;
  Observer authorityObserver = Observer::Hovering; ///< Hovering or orbiting command station.
  std::vector<double> bandRadiusCm;
};

struct ConstellationConfig {
  std::uint64_t seed = 0;
  double secondsPerTurn = 86400.0;
  std::vector<SystemSpec> systems;
  std::vector<InterSystemLink> links;

  // Victory (evaluated per faction; any one target reached wins the campaign for
  // that faction and ends it). Zero disables a path.
  double victoryEnergyUnits = 0.0;
  double victoryStabilizationUnits = 0.0;
  double victoryControlScore = 0.0;
  std::int64_t deadlineTurn = 0;

  // Work and movement.
  double workProperHoursPerReport = 24.0; ///< Proper-hours a fleet banks before emitting one yield report.
  double fleetInitialFuelUnits = 100.0;
  double fuelPerBandHop = 20.0;
  /// Fleet transit speed as a fraction of c, in (0, 1); a coasting crew ages
  /// at sqrt(1 - beta^2) of coordinate time.
  double interSystemTravelSpeedFraction = 0.5;
  double interSystemTravelFuelUnits = 50.0;    ///< Fuel charged for one interstellar hop.

  // Economy, sharing the single hole's meaning and defaults-are-no-ops discipline.
  std::array<double, 5> capabilityYieldMultiplier = {1.0, 1.0, 1.0, 1.0, 1.0};
  double reliabilityWearPerProperDay = 0.0;
  double reliabilityFloor = 0.5;
  double frameDragYieldBonus = 0.0;
  double instabilityPerTurn = 0.0;
  double instabilityYieldPenaltyPerUnit = 0.0;
  double ergoContainmentPerProperDay = 0.0;
  double ergoHazardWearPerProperDay = 0.0;
  double containmentYieldRetention = 1.0;

  // Control.
  double controlPointsPerBandPerTurn = 1.0; ///< Score per uncontested held band per turn.
};

/** @brief The only mutation input besides advanceTurn: move a fleet. When
 *         targetSystem is the fleet's current system it is an intra-system band
 *         hop; otherwise it begins interstellar transit to targetSystem. */
struct ConstellationCommand {
  FleetId fleet = K_INVALID_FLEET_ID;
  SystemId targetSystem = K_INVALID_SYSTEM_ID;
  int targetBand = 0;
  OrbitLane lane = OrbitLane::Prograde;
  /// Orbit (geodesic) or hover (ZAMO) at the target.
  StationKeeping station = StationKeeping::Orbit;
};

class Constellation {
public:
  explicit Constellation(ConstellationConfig config);

  [[nodiscard]] bool valid() const { return valid_; }

  /** @brief Setup-phase faction registration; returns K_INVALID_FACTION_ID when
   *         homeSystem is out of range. The first faction registered is the
   *         player, whose outcome overallStatus reports. */
  FactionId addFaction(FactionPolicy policy, SystemId homeSystem);

  /** @brief Setup-phase fleet creation; returns K_INVALID_FLEET_ID when the
   *         faction, system, band, lane, or station keeping is inadmissible. */
  FleetId addFleet(FactionId faction, SystemId system, FleetCapability capability, int bandIndex,
                   OrbitLane lane = OrbitLane::Prograde,
                   StationKeeping station = StationKeeping::Orbit);

  /** @brief How a prograde fleet holds (system, bandIndex) by default: in orbit
   *         where a bound circular orbit exists, hovering below the marginally
   *         bound radius. The AI policies place fleets this way. */
  [[nodiscard]] StationKeeping defaultStation(SystemId system, int bandIndex) const;

  /** @brief Validates and enqueues one faction's order. Returns false and leaves
   *         all state untouched when the order is inadmissible or the faction
   *         has already learned that the campaign is decided. The order is
   *         judged against the faction's last report of the fleet and takes
   *         effect at issue turn + ceil of the delay from the faction's
   *         authority to where that report placed the fleet: the light path
   *         between authorities plus the radial leg. */
  bool issueCommand(FactionId faction, const ConstellationCommand &command);

  /** @brief One coordinate turn: advance the clock, deliver due orders/reports/
   *         observations, land arrivals, run each fleet's work, score control,
   *         emit control intel, step the faction AI, evaluate outcomes. */
  void advanceTurn();

  /** @brief turnCount iterated single-turn advances (op-order invariant). */
  void advanceTurns(std::int64_t turnCount);

  // Referee accessors: the true state of every system, faction, and fleet,
  // known to no authority in the game. Harnesses, tests, and the post-game
  // record read them; a player-facing surface reads renderSnapshot().
  [[nodiscard]] std::int64_t turn() const { return clock_.turn(); }
  [[nodiscard]] const std::vector<OrbitalSystem> &systems() const { return systems_; }
  [[nodiscard]] const std::vector<FactionState> &factions() const { return factions_; }
  [[nodiscard]] const std::vector<ConstellationFleet> &fleets() const { return fleets_; }

  /** @brief Referee truth for the player: Won when the player faction reaches
   *         a target first, Lost when a rival wins first or the deadline
   *         passes undecided -- decided at the crossing, before any authority
   *         can know it. */
  [[nodiscard]] CampaignStatus overallStatus() const { return overallStatus_; }
  /** @brief Referee truth: the faction that won, or K_INVALID_FACTION_ID. */
  [[nodiscard]] FactionId winner() const { return winner_; }

  /** @brief Last-known controller of (systemIndex, bandIndex) as factionIndex's
   *         authority believes it -- the delayed intel the AI reads. Returns
   *         K_INVALID_FACTION_ID for unknown/empty/contested. */
  [[nodiscard]] FactionId perceivedController(std::size_t factionIndex, SystemId system,
                                              int bandIndex) const;

  /** @brief The player's view: outcome, scores, band control, and fleets as
   *         the player's authority knows them, plus a separately named referee
   *         block (see ConstellationViewSnapshot). */
  [[nodiscard]] ConstellationViewSnapshot renderSnapshot() const;
  [[nodiscard]] std::vector<std::uint8_t> serializeState() const;
  [[nodiscard]] std::uint64_t stateDigest() const;

private:
  enum class DeliveryKind : std::uint8_t {
    Command = 0,
    YieldReport = 1,
    ControlObservation = 2,
    OutcomeNotice = 3, ///< The campaign's decision reaching observerIndex's authority.
    FleetStatus = 4,   ///< A fleet's own state travelling home to observerIndex's authority.
    OrderUndelivered = 5, ///< An order that found no fleet at its address, reported home.
    ScoreReport = 6,      ///< Stabilization and control credited at a band, reported home.
  };

  struct Delivery {
    DeliveryKind kind = DeliveryKind::Command;
    std::int64_t effectTurn = 0;
    std::uint32_t sequence = 0;
    std::uint32_t commandIndex = 0; ///< Command: index into commandLog_.
    FactionId faction = K_INVALID_FACTION_ID; ///< YieldReport: banked to this faction.
    double yieldUnits = 0.0;
    SystemId system = K_INVALID_SYSTEM_ID; ///< ControlObservation: which band.
    int bandIndex = 0;
    FactionId controller = K_INVALID_FACTION_ID; ///< ControlObservation: believed holder.
    /// ControlObservation/OutcomeNotice/FleetStatus/OrderUndelivered: who learns.
    std::size_t observerIndex = 0;
    FleetBelief status;            ///< FleetStatus: the state the fleet reported.
    double stabilizationUnits = 0.0; ///< ScoreReport: containment produced at the band.
    double controlPoints = 0.0;      ///< ScoreReport: control points the band earned.
  };

  /** @brief A place a credit happened: a band, or a system's authority when
   *         bandIndex is negative. */
  struct CreditSite {
    SystemId system = K_INVALID_SYSTEM_ID;
    int bandIndex = -1;
  };

  /** @brief One turn's stabilization and control credit for a faction at a band,
   *         gathered in canonical order and sent home as one ScoreReport. */
  struct TurnCredit {
    std::size_t factionIndex = 0;
    SystemId system = K_INVALID_SYSTEM_ID;
    int bandIndex = 0;
    double stabilizationUnits = 0.0;
    double controlPoints = 0.0;
  };

  struct LoggedCommand {
    ConstellationCommand command;
    FactionId faction = K_INVALID_FACTION_ID;
    std::int64_t issueTurn = 0;
    std::int64_t effectTurn = 0;
    /// Where the order was sent: the fleet's last-reported slot at issue. The
    /// effect turn is the light time to this address, so the order acts only
    /// on a fleet still there.
    SystemId addressedSystem = K_INVALID_SYSTEM_ID;
    int addressedBand = 0;
    bool undelivered = false; ///< Its non-delivery notice has reached the authority.
  };

  [[nodiscard]] std::size_t factionIndex(FactionId faction) const;
  [[nodiscard]] ConstellationFleet *findFleet(FleetId fleetId);
  [[nodiscard]] const ConstellationFleet *findFleet(FleetId fleetId) const;
  [[nodiscard]] double bandRadiusCm(SystemId system, int bandIndex) const;
  [[nodiscard]] bool validBand(SystemId system, int bandIndex) const;
  /** @brief Same rule as CampaignState::placementAllowed, per system. */
  [[nodiscard]] bool placementAllowed(SystemId system, OrbitLane lane, StationKeeping station,
                                      int bandIndex) const;
  [[nodiscard]] double linkSeparationCm(SystemId a, SystemId b) const; ///< -1 when not linked.
  /** @brief Shortest light time between two systems' authorities along chains
   *         of links (all-pairs, built once at construction); 0 within one
   *         system, negative when no chain of links connects them -- such a
   *         signal is never delivered. */
  [[nodiscard]] double lightPathSec(SystemId a, SystemId b) const;
  /** @brief Radial light delay between a band and its own system's authority. */
  [[nodiscard]] double intraSystemDelaySec(SystemId system, int bandIndex) const;
  /** @brief Delay from a faction's authority to a fleet at (system, band): the
   *         light path between authorities plus the radial leg inside the
   *         fleet's system. Negative when no light path exists. */
  [[nodiscard]] double orderDelaySec(FactionId faction, SystemId system, int bandIndex) const;
  /** @brief Delay from (system, band) back to a faction's authority; the
   *         reverse leg of orderDelaySec. Negative when no light path exists. */
  [[nodiscard]] double reportDelaySec(FactionId faction, SystemId system, int bandIndex) const;
  [[nodiscard]] double ergoregionDepth(const ConstellationFleet &fleet) const;

  void deliverDue();
  /** @brief Delivers order `commandIndex` at its address. A fleet still at
   *         the addressed slot acts and reports; otherwise the order fizzles
   *         and a non-delivery notice travels home from the address. */
  void applyCommand(std::uint32_t commandIndex);
  /** @brief The effect of an order the fleet has received: a band hop or an
   *         interstellar departure, each fizzling when unaffordable. */
  void applyReceivedCommand(ConstellationFleet &fleet, const ConstellationCommand &command);
  /** @brief Sends the fleet's current state home from (fromSystem, fromBand),
   *         where it stands when the report leaves; undeliverable without a
   *         light path. */
  void enqueueFleetStatus(ConstellationFleet &fleet, SystemId fromSystem, int fromBand);
  /** @brief The owner's record of a fleet; null when `faction` does not own it. */
  [[nodiscard]] const FleetBelief *knownFleet(FactionId faction, FleetId fleet) const;
  void landArrivals();
  void runFleetWork();
  void scoreControlAndObserve();
  void stepFactionAI();
  void evaluateOutcomes();
  /** @brief Records one credit at (system, band) for this turn: the referee
   *         total already holds it; the faction learns it by report. */
  void recordCredit(std::size_t factionIndex, SystemId system, int bandIndex,
                    double stabilizationUnits, double controlPoints);
  /** @brief Sends this turn's credits home, one ScoreReport per faction and band. */
  void sendScoreReports();
  /** @brief Light time from a credit site to a system's authority; negative
   *         when no light path exists. */
  [[nodiscard]] double siteDelaySec(const CreditSite &site, SystemId toSystem) const;
  void enqueueYieldReport(const ConstellationFleet &fleet, double yieldUnits);
  [[nodiscard]] FactionId bandController(SystemId system, int bandIndex) const;
  [[nodiscard]] std::vector<ConstellationCommand> policyOrders(const FactionState &faction) const;
  /** @brief Expansionist step: send one fleet redundantly stacked on a slot to
   *         the first reachable band the faction does not yet occupy. */
  [[nodiscard]] std::vector<ConstellationCommand> expansionistOrders(const FactionState &faction) const;
  /** @brief Extractor step: move one out-of-place fleet toward the home system's
   *         deepest valid prograde band. */
  [[nodiscard]] std::vector<ConstellationCommand> extractorOrders(const FactionState &faction) const;
  /** @brief Contester step: contest one band the faction's delayed intel believes
   *         the leading rival holds. */
  [[nodiscard]] std::vector<ConstellationCommand> contesterOrders(const FactionState &faction) const;
  /** @brief A fleet the faction believes can take a fresh order now: known to
   *         it, not in transit as last reported, and with no order in flight. */
  [[nodiscard]] bool fleetAvailable(std::size_t factionIndexValue, const FleetBelief &known) const;
  /** @brief True when an order to this fleet is still pending: the authority
   *         has heard neither a status report sent at or after the order's
   *         effect turn nor the order's non-delivery notice, so a policy does
   *         not stack another behind it. */
  [[nodiscard]] bool hasCommandInFlight(std::size_t factionIndexValue, FleetId fleet) const;
  /** @brief The order a faction last issued to `fleet` that is still pending,
   *         or null. */
  [[nodiscard]] const LoggedCommand *latestPendingCommand(std::size_t factionIndexValue,
                                                          FleetId fleet) const;
  /** @brief True when, as the faction last learned, one of its fleets holds
   *         (system, bandIndex) or is in transit to that slot, or an order it
   *         has not yet heard answered is sending a fleet there. */
  [[nodiscard]] bool factionOccupies(FactionId faction, SystemId system, int bandIndex) const;
  /** @brief Systems the faction can order a fleet in `fromSystem` to reach: that
   *         system itself plus every directly linked system. */
  [[nodiscard]] bool systemReachableFrom(SystemId fromSystem, SystemId toSystem) const;

  ConstellationConfig config_;
  bool valid_ = false;
  TemporalClock clock_;
  std::vector<OrbitalSystem> systems_;
  std::vector<FactionState> factions_;
  std::vector<ConstellationFleet> fleets_;
  std::vector<LoggedCommand> commandLog_;
  std::vector<Delivery> deliveryQueue_;
  // links_: the config's links normalized once -- each unordered pair of
  // systems once, with a < b, at the shortest separation any duplicate gave,
  // sorted by (a, b) -- so travel, reachability, and signal paths all use the
  // same edge whatever order the config listed duplicates in.
  std::vector<InterSystemLink> links_;
  // lightPathSec_[a * S + b]: all-pairs light time between authorities over the
  // link graph; negative marks an unreachable pair. Derived from the config.
  std::vector<double> lightPathSec_;
  // Per-turn scratch, rebuilt every turn before it is read: this turn's credits
  // and, per faction, the site of its last stabilization and control credit
  // (canonical order), which locates a victory in space. Never serialized
  // because no turn reads a previous turn's values.
  std::vector<TurnCredit> turnCredits_;
  std::vector<CreditSite> lastStabilizationSite_;
  std::vector<CreditSite> lastControlSite_;
  // pendingCommands_[factionIndex]: indices into commandLog_ of that
  // faction's orders it has not yet heard answered, ascending. An entry leaves
  // when a status report sent at or after its effect turn, or its
  // non-delivery notice, reaches the authority.
  std::vector<std::vector<std::uint32_t>> pendingCommands_;
  // ownBelief_[factionIndex]: that faction's record of its own fleets, in
  // ascending fleet id, updated only by FleetStatus deliveries.
  std::vector<std::vector<FleetBelief>> ownBelief_;
  // perceived_[factionIndex][systemIndex][bandIndex]: the controller that
  // faction's authority last learned about, delayed by the radial leg and the
  // light path between authorities.
  std::vector<std::vector<std::vector<FactionId>>> perceived_;
  // lastEmittedController_[systemIndex][bandIndex]: the actual controller when an
  // observation was last emitted, so only changes generate new intel.
  std::vector<std::vector<FactionId>> lastEmittedController_;
  FleetId nextFleetId_ = 1;
  FactionId nextFactionId_ = 1;
  std::uint32_t nextSequence_ = 0;
  FactionId playerFaction_ = K_INVALID_FACTION_ID;
  FactionId winner_ = K_INVALID_FACTION_ID;
  CampaignStatus overallStatus_ = CampaignStatus::Ongoing;
  bool decided_ = false; ///< Referee latch: a winner exists or the deadline passed.
};

} // namespace game

#endif // BLACKHOLE_GAME_CONSTELLATION_H
