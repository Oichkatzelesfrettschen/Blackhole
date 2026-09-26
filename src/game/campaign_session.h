/**
 * @file campaign_session.h
 * @brief Owns one live campaign: the time field, the state, and the canonical
 *        default scenario the desktop client starts from.
 *
 * The session exists so the UI layer holds exactly one object. It wires the
 * field-outlives-state lifetime CampaignState requires and exposes small
 * command helpers the panels call; everything observable still flows through
 * CampaignState::renderSnapshot().
 */

#ifndef BLACKHOLE_GAME_CAMPAIGN_SESSION_H
#define BLACKHOLE_GAME_CAMPAIGN_SESSION_H

#include <cstdint>

#include "game/campaign.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/kerr_time_field.h"

namespace game {

/** @brief Named starting scenarios a session can be built from. */
enum class CampaignScenario : std::uint8_t {
  M87Default = 0,     ///< The canonical vertical slice (see the default constructor).
  GargantuaCanon = 1, ///< Interstellar's Gargantua with Miller's planet on the prograde ISCO.
  GargantuaColony = 2, ///< Gargantua with a colony node and the host's story.
};

/**
 * @brief Charter of the Gargantua colony scenario. The colony's clock is its
 *        orbit's; it ships one energy unit per local hour to the host for a
 *        mission of K_COLONY_MISSION_SEC local seconds and then falls silent.
 *
 * The mission length is the scenario parameter that decides the deep/shallow
 * split balance_sweep_test records. The host streams packets on outside time
 * until its seeded dark turn (3650..10950 turns); a colony hears packets and
 * banks production only while its mission lasts on its own clock.
 *  - On the 100M orbit (dtau/dt ~ 0.985) 365 local days is ~370 turns: the
 *    colony banks all 8760 hours, since its window closes before the earliest
 *    dark turn, but hears only the first ~370/K packets.
 *  - On Miller's orbit (dtau/dt = 1.6286e-5) 365 local days is ~22 million
 *    turns: the colony hears the whole stream before the host goes dark but
 *    lives only 1-4 local hours of it, so it banks 1-4 units.
 * Once the shallow window outlasts the dark turn -- 3650..10950 turns is
 * about 3600..10800 local days at dtau/dt = 0.98492 -- the shallow colony
 * hears the stream to its end, matches the deep tier, and still banks more:
 * the split disappears, first for late-dark seeds, then for all. A mission shorter than the deep colony's pre-dark hours would
 * shrink both colonies' banks. The value is a charter, fixed before any
 * sweep, not a knob tuned to produce the split.
 */
inline constexpr std::int64_t K_COLONY_TICK_SEC = 3600;
inline constexpr double K_COLONY_ENERGY_PER_TICK = 1.0;
inline constexpr std::int64_t K_COLONY_MISSION_SEC = 365LL * 86400LL;
/// Colony bands of the GargantuaColony scenario.
inline constexpr int K_MILLER_BAND = 0;  ///< Miller's orbit: the prograde ISCO (deep).
inline constexpr int K_SURVEY_BAND = 1;  ///< The 100M survey orbit (shallow).

class CampaignSession {
public:
  /** @brief Canonical vertical-slice scenario: M87*-scale spinning hole
   *         (a* = 0.9), one-day turns, authority at 200 r_s, four bands
   *         (an ergoregion band at index 0 plus 3/10/50 r_s), six specialist
   *         fleets, a 3150-energy objective on a 1200-turn deadline, no tasks
   *         contracted -- the player's move. The seed is recorded in the
   *         campaign state and serialization. Spin is clamped to [-1, 1]. */
  explicit CampaignSession(std::uint64_t seed = 1, double spinDimensionless = 0.9);

  /** @brief Scenario by name. GargantuaCanon is a 1e8 M_sun hole with spin
   *         deficit 1 - a = 1.33e-14 (Opatrny, Richterek & Bakala,
   *         arXiv:1601.02897), one-day turns, and Miller's band on the
   *         prograde ISCO, where a circular orbit's clock runs at
   *         dtau/dt = 1.6286e-5: one Miller hour is seven outside years. A
   *         colony fleet orbits there and a survey fleet orbits at 100M; the
   *         authority hovers at 400M. No victory, deadline, or economy knob is
   *         set, so the scenario isolates the clock. */
  CampaignSession(std::uint64_t seed, CampaignScenario scenario);

  /** @brief GargantuaColony: the GargantuaCanon field and bands (band 0 is
   *         Miller's orbit, band 1 the 100M survey orbit), the host hovering
   *         at 400M as the authority node, one survey fleet on band 1, and one
   *         colony on `colonyBand` in a prograde orbit under the colony
   *         charter above, playing `story`. No victory threshold is set: the
   *         outcome vector (colony tech tier, energy banked at the host) is
   *         read directly. */
  CampaignSession(std::uint64_t seed, const EventSet &story, int colonyBand);

  CampaignSession(const CampaignSession &) = delete;
  CampaignSession &operator=(const CampaignSession &) = delete;
  CampaignSession(CampaignSession &&) = delete;
  CampaignSession &operator=(CampaignSession &&) = delete;
  ~CampaignSession() = default;

  [[nodiscard]] std::uint64_t seed() const { return seed_; }
  [[nodiscard]] CampaignScenario scenario() const { return scenario_; }
  /** @brief Band of the scenario's colony; -1 when the scenario has none. */
  [[nodiscard]] int colonyBand() const { return colonyBand_; }

  [[nodiscard]] CampaignState &state() { return state_; }
  [[nodiscard]] const CampaignState &state() const { return state_; }
  [[nodiscard]] const KerrTimeField &field() const { return field_; }

  /** @brief Contract a task on the fleet, costed in local proper-time hours,
   *         sent from `origin` (the authority by default). */
  bool issueAssignTask(FleetId fleet, double costHours, NodeId origin = K_AUTHORITY_NODE);

  /** @brief Order the fleet to another orbital band on the given lane, in
   *         orbit by default or hovering on thrust, sent from `origin`. */
  bool issuePlaceFleet(FleetId fleet, int targetBand, OrbitLane lane = OrbitLane::Prograde,
                       StationKeeping station = StationKeeping::Orbit,
                       NodeId origin = K_AUTHORITY_NODE);

private:
  // The state holds a pointer to field_, so the session is neither copied nor
  // moved, and field_ is declared (and so constructed) first.
  KerrTimeField field_;
  CampaignState state_;
  std::uint64_t seed_ = 0;
  CampaignScenario scenario_ = CampaignScenario::M87Default;
  int colonyBand_ = -1;
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_SESSION_H
