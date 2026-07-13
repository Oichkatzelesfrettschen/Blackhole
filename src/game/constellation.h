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
  double interSystemTravelSpeedFraction = 0.5; ///< Fleet transit speed as a fraction of c.
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
   *         faction, system, band, or lane is inadmissible. */
  FleetId addFleet(FactionId faction, SystemId system, FleetCapability capability, int bandIndex,
                   OrbitLane lane = OrbitLane::Prograde);

  /** @brief Validates and enqueues one faction's order. Returns false and leaves
   *         all state untouched when the order is inadmissible or the campaign is
   *         already decided. Accepted orders take effect at issue turn + ceil of
   *         the delay from the faction's authority to the fleet, which for a fleet
   *         in another system includes the interstellar light time. */
  bool issueCommand(FactionId faction, const ConstellationCommand &command);

  /** @brief One coordinate turn: advance the clock, deliver due orders/reports/
   *         observations, land arrivals, run each fleet's work, score control,
   *         emit control intel, step the faction AI, evaluate outcomes. */
  void advanceTurn();

  /** @brief turnCount iterated single-turn advances (op-order invariant). */
  void advanceTurns(std::int64_t turnCount);

  [[nodiscard]] std::int64_t turn() const { return clock_.turn(); }
  [[nodiscard]] const std::vector<OrbitalSystem> &systems() const { return systems_; }
  [[nodiscard]] const std::vector<FactionState> &factions() const { return factions_; }
  [[nodiscard]] const std::vector<ConstellationFleet> &fleets() const { return fleets_; }

  /** @brief The player's outcome: Won when the player faction reaches a target
   *         first, Lost when a rival wins first or the deadline passes undecided. */
  [[nodiscard]] CampaignStatus overallStatus() const { return overallStatus_; }
  /** @brief The faction that won, or K_INVALID_FACTION_ID while undecided. */
  [[nodiscard]] FactionId winner() const { return winner_; }

  /** @brief Last-known controller of (systemIndex, bandIndex) as factionIndex's
   *         authority believes it -- the delayed intel the AI reads. Returns
   *         K_INVALID_FACTION_ID for unknown/empty/contested. */
  [[nodiscard]] FactionId perceivedController(std::size_t factionIndex, SystemId system,
                                              int bandIndex) const;

  [[nodiscard]] ConstellationViewSnapshot renderSnapshot() const;
  [[nodiscard]] std::vector<std::uint8_t> serializeState() const;
  [[nodiscard]] std::uint64_t stateDigest() const;

private:
  enum class DeliveryKind : std::uint8_t {
    Command = 0,
    YieldReport = 1,
    ControlObservation = 2,
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
    std::size_t observerIndex = 0;               ///< ControlObservation: which faction learns.
  };

  struct LoggedCommand {
    ConstellationCommand command;
    FactionId faction = K_INVALID_FACTION_ID;
    std::int64_t issueTurn = 0;
    std::int64_t effectTurn = 0;
  };

  [[nodiscard]] std::size_t factionIndex(FactionId faction) const;
  [[nodiscard]] ConstellationFleet *findFleet(FleetId fleetId);
  [[nodiscard]] const ConstellationFleet *findFleet(FleetId fleetId) const;
  [[nodiscard]] double bandRadiusCm(SystemId system, int bandIndex) const;
  [[nodiscard]] bool validBand(SystemId system, int bandIndex) const;
  [[nodiscard]] bool laneAllowedAtBand(SystemId system, OrbitLane lane, int bandIndex) const;
  [[nodiscard]] double linkSeparationCm(SystemId a, SystemId b) const; ///< -1 when not linked.
  /** @brief Flat interstellar light time between two authorities; 0 for the same
   *         system, the separation over c otherwise. */
  [[nodiscard]] double interAuthorityDelaySec(SystemId a, SystemId b) const;
  /** @brief Delay from a faction's authority to a fleet: interstellar light time
   *         plus the radial signal delay within the fleet's system. */
  [[nodiscard]] double orderDelaySec(FactionId faction, const ConstellationFleet &fleet) const;
  [[nodiscard]] double reportDelaySec(const ConstellationFleet &fleet) const;
  [[nodiscard]] double ergoregionDepth(const ConstellationFleet &fleet) const;

  void deliverDue();
  void applyCommand(const LoggedCommand &logged);
  void landArrivals();
  void runFleetWork();
  void scoreControlAndObserve();
  void stepFactionAI();
  void evaluateOutcomes();
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
  /** @brief A faction fleet that can take a fresh order now: it exists, is not in
   *         transit, and has no order already in flight. */
  [[nodiscard]] bool fleetAvailable(FleetId fleet) const;
  /** @brief True when a not-yet-delivered order already targets this fleet, so a
   *         policy does not stack duplicate orders while the first is in flight. */
  [[nodiscard]] bool hasCommandInFlight(FleetId fleet) const;
  /** @brief True when the faction stations a fleet at (system, bandIndex) or has
   *         one in transit whose destination is that slot. */
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
  // perceived_[factionIndex][systemIndex][bandIndex]: the controller that
  // faction's authority last learned about, delayed by interstellar light time.
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
  bool decided_ = false;
};

} // namespace game

#endif // BLACKHOLE_GAME_CONSTELLATION_H
