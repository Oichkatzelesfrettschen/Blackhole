/**
 * @file constellation_sim_lines.h
 * @brief Player commitment lines the constellation balance harness replays,
 *        shared by the sim and the balance-invariant test.
 *
 * Each line is a way the (scripted) player plays the default two-system scenario
 * against the Expansionist rival: race energy from home (Outer), dive home for
 * stabilization (AllIn), or spend fleets travelling to sit on the rival's bands
 * and deny its expansion (Contest). The rival is the same deterministic AI in
 * every line, so the lines differ only in what the player does. The sim prints
 * each line's outcome and the test asserts it, reading one identical playthrough.
 */

#ifndef BLACKHOLE_GAME_CONSTELLATION_SIM_LINES_H
#define BLACKHOLE_GAME_CONSTELLATION_SIM_LINES_H

#include <algorithm>
#include <array>
#include <cstddef>
#include <cstdint>
#include <vector>

#include "game/constellation.h"
#include "game/constellation_session.h"
#include "game/constellation_types.h"
#include "game/constellation_view.h"

namespace constellation_sim {

enum class PlayerLine {
  Outer,   ///< Hold home outer bands, ignore the rival: the energy race.
  AllIn,   ///< Dive every player fleet to the home ergoregion band: stabilization.
  Contest, ///< Travel fleets onto the rival's bands to deny its domination.
};

struct LineResult {
  game::CampaignStatus overallStatus = game::CampaignStatus::Ongoing;
  game::FactionId winner = game::K_INVALID_FACTION_ID;
  std::int64_t turn = 0;
  std::uint64_t digest = 0;
  game::ConstellationViewSnapshot view;
};

inline const char *lineName(PlayerLine line) {
  switch (line) {
  case PlayerLine::AllIn:
    return "all-in";
  case PlayerLine::Contest:
    return "contest";
  case PlayerLine::Outer:
  default:
    return "outer";
  }
}

namespace detail {

inline std::vector<game::FleetId> factionFleetIds(const game::Constellation &constellation,
                                                  game::FactionId faction) {
  std::vector<game::FleetId> ids;
  for (const game::ConstellationFleet &fleet : constellation.fleets()) {
    if (fleet.faction == faction) {
      ids.push_back(fleet.id);
    }
  }
  return ids;
}

// The player's move for one turn under a given line. Every call re-states the
// line's goal; issueCommand refuses an order that would leave a fleet where it
// is already bound (its reported slot or its pending order's target), so a
// satisfied goal adds nothing to the log.
inline void playerTurn(game::ConstellationSession &session, PlayerLine line) {
  const game::Constellation &constellation = session.constellation();
  const game::FactionId player = session.player();
  const game::FactionId rival = session.rival();
  const std::vector<game::FleetId> fleets = factionFleetIds(constellation, player);

  if (line == PlayerLine::Outer) {
    // Spread the four fleets across the home outer bands (1/2/3) and leave them:
    // a pure energy line that never answers the rival.
    static constexpr std::array<int, 4> kOuterBands = {1, 2, 3, 2};
    for (std::size_t index = 0; index < fleets.size(); ++index) {
      const int band = kOuterBands.at(index % kOuterBands.size());
      session.movePlayerFleet(fleets.at(index), 0, band, game::OrbitLane::Prograde,
                              constellation.defaultStation(0, band));
    }
    return;
  }

  if (line == PlayerLine::AllIn) {
    // Every fleet dives the home ergoregion band for stabilization.
    for (const game::FleetId fleet : fleets) {
      session.movePlayerFleet(fleet, 0, 0, game::OrbitLane::Prograde,
                              constellation.defaultStation(0, 0));
    }
    return;
  }

  // Contest: cover every home-system band (0/1/2/3), a fortress that denies the
  // rival any uncontested foothold in the player's own system and holds four
  // bands for the player's own control score.
  static_cast<void>(rival);
  for (std::size_t index = 0; index < fleets.size(); ++index) {
    const int band = static_cast<int>(index % 4);
    session.movePlayerFleet(fleets.at(index), 0, band, game::OrbitLane::Prograde,
                            constellation.defaultStation(0, band));
  }
}

} // namespace detail

/** @brief Runs one player line against a rival policy (Expansionist for the
 *         pinned shape) to a decision or the turn budget, the player acting
 *         every `playerEvery` turns, and returns the outcome and digest. */
inline LineResult runLine(std::uint64_t seed, std::int64_t turns, PlayerLine line,
                          game::FactionPolicy rivalPolicy = game::FactionPolicy::Expansionist,
                          std::int64_t playerEvery = 1) {
  game::ConstellationSession session(seed, rivalPolicy);
  game::Constellation &constellation = session.constellation();
  for (std::int64_t elapsed = 0; elapsed < turns; ++elapsed) {
    if (elapsed % playerEvery == 0) {
      detail::playerTurn(session, line);
    }
    constellation.advanceTurn();
    if (constellation.overallStatus() != game::CampaignStatus::Ongoing) {
      break;
    }
  }
  return LineResult{.overallStatus = constellation.overallStatus(),
                    .winner = constellation.winner(),
                    .turn = constellation.turn(),
                    .digest = constellation.stateDigest(),
                    .view = constellation.renderSnapshot()};
}

} // namespace constellation_sim

#endif // BLACKHOLE_GAME_CONSTELLATION_SIM_LINES_H
