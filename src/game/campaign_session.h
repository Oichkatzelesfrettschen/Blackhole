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

class CampaignSession {
public:
  /** @brief Canonical vertical-slice scenario: M87*-scale spinning hole
   *         (a* = 0.9), one-day turns, authority at 200 r_s, four bands
   *         (an ergoregion band at index 0 plus 3/10/50 r_s), six specialist
   *         fleets, a 300-energy objective on a 1200-turn deadline, no tasks
   *         contracted -- the player's move. The seed and spin are recorded in
   *         the campaign state and serialization. Spin is clamped to +/-0.998. */
  explicit CampaignSession(std::uint64_t seed = 1, double spinDimensionless = 0.9);

  [[nodiscard]] CampaignState &state() { return state_; }
  [[nodiscard]] const CampaignState &state() const { return state_; }
  [[nodiscard]] const KerrTimeField &field() const { return field_; }

  /** @brief Contract a task on the fleet, costed in local proper-time hours. */
  bool issueAssignTask(FleetId fleet, double costHours);

  /** @brief Order the fleet to another orbital band on the given lane. */
  bool issuePlaceFleet(FleetId fleet, int targetBand, OrbitLane lane = OrbitLane::Prograde);

private:
  KerrTimeField field_;
  CampaignState state_;
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_SESSION_H
