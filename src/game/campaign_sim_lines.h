/**
 * @file campaign_sim_lines.h
 * @brief The canonical commitment lines the balance harness replays, shared by
 *        campaign_sim and the balance-invariant test.
 *
 * A commitment line is a scripted way to play the default scenario: how many
 * fleets are sent into the deep prograde ergoregion lane, from none (the outer
 * energy line) to all six (the dedicated stabilization line). Every fleet is
 * re-tasked on a fixed cadence so work -- and the deep lane's containment -- is
 * sustained across the campaign. The sim prints each line's outcome; the test
 * asserts it, so both read the identical playthrough and cannot drift apart.
 */

#ifndef BLACKHOLE_GAME_CAMPAIGN_SIM_LINES_H
#define BLACKHOLE_GAME_CAMPAIGN_SIM_LINES_H

#include <algorithm>
#include <cstdint>
#include <optional>
#include <vector>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/fleet.h"

namespace campaign_sim {

/// Largest story-derived colony horizon `campaign_sim --colony` plays without
/// --turns: 10^6 turns. The shipped story's horizon is at most about 11,500
/// (dark turn <= 10950, plus the host-colony delay, four 91-turn packet
/// periods, and 60), and a colony turn costs about a microsecond, so the
/// ceiling is roughly a second of work; a loader-valid dark turn near 2^40
/// would otherwise be a trillion turns.
inline constexpr std::int64_t K_COLONY_SIM_MAX_HORIZON = 1000000;

/** @brief Turns past which nothing in the colony story changes: the dark
 *         turn, the host-colony delay, four packet periods of silence, and a
 *         60-turn margin; never negative. Story integers lie in [-2^40, 2^40],
 *         so the sum cannot overflow. */
[[nodiscard]] inline std::int64_t colonyStoryHorizon(const game::CampaignState &state) {
  const std::int64_t derived =
      state.storyParam("dark_turn").value_or(0) +
      state.nodeDelayTurns(game::K_AUTHORITY_NODE, game::K_FIRST_COLONY_NODE) +
      (4 * state.storyParam("packet_period").value_or(0)) + 60;
  return std::max<std::int64_t>(derived, 0);
}

/** @brief Turns --colony plays: the story horizon, capped by --turns when
 *         given; nullopt when no --turns bounds a horizon past
 *         K_COLONY_SIM_MAX_HORIZON, which the sim refuses rather than run. */
[[nodiscard]] inline std::optional<std::int64_t>
colonySimTurns(std::int64_t storyHorizon, std::optional<std::int64_t> turnsCap) {
  if (turnsCap.has_value()) {
    return std::clamp<std::int64_t>(turnsCap.value(), 0, storyHorizon);
  }
  if (storyHorizon > K_COLONY_SIM_MAX_HORIZON) {
    return std::nullopt;
  }
  return storyHorizon;
}

// The canonical scenario creates six fleets with stable ids 1..6: extraction and
// research on the inner outer band, fabrication and relay on the middle,
// verification and survey research on the outer.
constexpr game::FleetId K_EXTRACTION = 1;
constexpr game::FleetId K_RESEARCH = 2;
constexpr game::FleetId K_FABRICATION = 3;
constexpr game::FleetId K_RELAY = 4;
constexpr game::FleetId K_VERIFICATION = 5;
constexpr game::FleetId K_SURVEY = 6;

constexpr int K_ERGO_BAND = 0;
constexpr double K_REISSUE_HOURS = 24.0;     ///< Uniform contract size for the sustaining cadence.
constexpr std::int64_t K_REISSUE_EVERY = 30; ///< Re-task every fleet this often to keep work flowing.

enum class Commit {
  Outer,     ///< No deep lane: every fleet stays on the outer bands (energy line).
  Solo,      ///< One survey fleet holds the deep prograde ergoregion lane.
  Pod,       ///< Survey plus co-located verification and fabrication sustain the dive.
  Stabilize, ///< Every fleet dives: the dedicated stabilization line.
};

/** @brief Fleets sent into the ergoregion band for a commitment level. The pod
 *         co-locates verification (holds telemetry above the corruption cliff)
 *         and fabrication (refuels the lane) so the deep line is sustainable. */
inline std::vector<game::FleetId> deepFleets(Commit commit) {
  switch (commit) {
    case Commit::Solo:
      return {K_SURVEY};
    case Commit::Pod:
      return {K_SURVEY, K_VERIFICATION, K_FABRICATION};
    case Commit::Stabilize:
      return {K_EXTRACTION, K_RESEARCH, K_FABRICATION, K_RELAY, K_VERIFICATION, K_SURVEY};
    case Commit::Outer:
    default:
      return {};
  }
}

/** @brief One commitment line's outcome: the render vector plus the played
 *         campaign's determinism digest. */
struct LineResult {
  game::CampaignViewSnapshot view;
  std::uint64_t digest = 0;
};

/** @brief Runs one commitment line to completion. Deep fleets redeploy prograde
 *         into the ergoregion band before work begins, hovering on thrust
 *         because no bound orbit exists there, then every fleet is re-tasked
 *         every `reissueEvery` turns (K_REISSUE_EVERY for the pinned shape)
 *         for the whole campaign. A cadence of zero or less never tasks a
 *         fleet: the no-work baseline. */
inline LineResult runLine(std::uint64_t seed, std::int64_t turns, Commit commit,
                          std::int64_t reissueEvery = K_REISSUE_EVERY) {
  game::CampaignSession session(seed);
  game::CampaignState &campaign = session.state();

  for (const game::FleetId fleet : deepFleets(commit)) {
    static_cast<void>(session.issuePlaceFleet(fleet, K_ERGO_BAND, game::OrbitLane::Prograde,
                                              game::StationKeeping::Hover));
  }

  const std::vector<game::FleetId> allFleets = {K_EXTRACTION, K_RESEARCH,     K_FABRICATION,
                                                K_RELAY,      K_VERIFICATION, K_SURVEY};
  for (std::int64_t elapsed = 0; elapsed < turns; ++elapsed) {
    if (reissueEvery > 0 && elapsed % reissueEvery == 0) {
      for (const game::FleetId fleet : allFleets) {
        static_cast<void>(session.issueAssignTask(fleet, K_REISSUE_HOURS));
      }
    }
    campaign.advanceTurn();
  }
  return LineResult{.view = campaign.renderSnapshot(), .digest = campaign.stateDigest()};
}

inline const char *commitLabel(Commit commit) {
  switch (commit) {
    case Commit::Outer:
      return "outer";
    case Commit::Pod:
      return "pod";
    case Commit::Stabilize:
      return "stab";
    case Commit::Solo:
    default:
      return "solo";
  }
}

} // namespace campaign_sim

#endif // BLACKHOLE_GAME_CAMPAIGN_SIM_LINES_H
