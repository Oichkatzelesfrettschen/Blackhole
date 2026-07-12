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

#include "game/blackhole_time_field.h"
#include "game/campaign.h"
#include "game/fleet.h"

namespace game {

class CampaignSession {
public:
  /** @brief Canonical vertical-slice scenario: M87*-scale hole, one-day turns,
   *         authority station at 200 r_s, three orbital bands (3/10/50 r_s),
   *         six specialist fleets, a 300-energy objective on a 1200-turn
   *         deadline, no tasks contracted yet -- the player's move. The seed
   *         is recorded in the campaign state and serialization. */
  explicit CampaignSession(std::uint64_t seed = 1);

  [[nodiscard]] CampaignState &state() { return state_; }
  [[nodiscard]] const CampaignState &state() const { return state_; }
  [[nodiscard]] const BlackholeTimeField &field() const { return field_; }

  /** @brief Contract a task on the fleet, costed in local proper-time hours. */
  bool issueAssignTask(FleetId fleet, double costHours);

  /** @brief Order the fleet to another orbital band. */
  bool issuePlaceFleet(FleetId fleet, int targetBand);

private:
  BlackholeTimeField field_;
  CampaignState state_;
};

} // namespace game

#endif // BLACKHOLE_GAME_CAMPAIGN_SESSION_H
