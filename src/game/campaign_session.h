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
#include "game/fleet.h"
#include "game/kerr_time_field.h"

namespace game {

/** @brief Named starting scenarios a session can be built from. */
enum class CampaignScenario : std::uint8_t {
  M87Default = 0,     ///< The canonical vertical slice (see the default constructor).
  GargantuaCanon = 1, ///< Interstellar's Gargantua with Miller's planet on the prograde ISCO.
};

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

  [[nodiscard]] CampaignState &state() { return state_; }
  [[nodiscard]] const CampaignState &state() const { return state_; }
  [[nodiscard]] const KerrTimeField &field() const { return field_; }

  /** @brief Contract a task on the fleet, costed in local proper-time hours. */
  bool issueAssignTask(FleetId fleet, double costHours);

  /** @brief Order the fleet to another orbital band on the given lane, in
   *         orbit by default or hovering on thrust. */
  bool issuePlaceFleet(FleetId fleet, int targetBand, OrbitLane lane = OrbitLane::Prograde,
                       StationKeeping station = StationKeeping::Orbit);

private:
  KerrTimeField field_;
  CampaignState state_;
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_SESSION_H
