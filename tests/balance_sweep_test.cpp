/**
 * @file balance_sweep_test.cpp
 * @brief Records how the campaign and constellation outcomes respond to the
 *        cadences and rival behavior the pinned invariants hold fixed.
 *
 * The campaign balance invariant pins one task cadence (every 30 turns) and
 * the constellation invariant pins one rival (Expansionist) and one player
 * cadence (every turn). This sweep replays every line over cadences 1..30 and,
 * for the constellation, against two rival policies, and prints the outcome
 * grid. It asserts only what is independent of balance: every run ends inside
 * its turn budget with a well-formed outcome, and a replay of any cell
 * reproduces its digest. It makes no claim about which line should win.
 *
 * What the grid records, stated without a balance claim: the locked
 * campaign shape (outer and stab win, solo and pod lose) holds only at
 * cadence 30, the cadence campaign_balance_invariant_test pins. At 29 solo
 * wins at t1200; from 26 to 29 pod loses and every other line wins; at 1..25
 * every line wins, and the stabilization line clears first at every cadence.
 * The constellation grid is flat along player cadence by construction: each
 * scripted line's goal is fixed from turn 0 and a re-stated goal is refused
 * as a no-op, so cadence changes nothing there.
 */

#include <gtest/gtest.h>

#include <array>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <vector>

#include "game/campaign_sim_lines.h"
#include "game/campaign_view.h"
#include "game/constellation_sim_lines.h"
#include "game/constellation_types.h"

namespace {

constexpr std::uint64_t K_SEED = 42;
constexpr std::int64_t K_CAMPAIGN_TURNS = 1200;
constexpr std::int64_t K_CONSTELLATION_TURNS = 1400;
constexpr std::int64_t K_MAX_CADENCE = 30;

char statusLetter(game::CampaignStatus status) {
  switch (status) {
  case game::CampaignStatus::Won:
    return 'W';
  case game::CampaignStatus::Lost:
    return 'L';
  case game::CampaignStatus::Ongoing:
  default:
    return '-';
  }
}

} // namespace

// Falsifier: a campaign run at any cadence 1..30 ending outside its 1200-turn
// budget, reporting a win without a cleared turn, or any cell replaying to a
// digest different from its first run. The printed grid is the record: status and cleared turn per line.
TEST(BalanceSweep, CampaignLinesAcrossTaskCadence) {
  using campaign_sim::Commit;
  constexpr std::array<Commit, 4> lines = {Commit::Outer, Commit::Solo, Commit::Pod,
                                           Commit::Stabilize};
  std::printf("campaign cadence sweep (seed %llu, %lld turns): status/clearedTurn\n",
              static_cast<unsigned long long>(K_SEED), static_cast<long long>(K_CAMPAIGN_TURNS));
  std::printf("cadence  outer        solo         pod          stab\n");
  std::vector<std::uint64_t> firstDigests;
  for (std::int64_t cadence = 1; cadence <= K_MAX_CADENCE; ++cadence) {
    std::printf("%7lld", static_cast<long long>(cadence));
    for (const Commit commit : lines) {
      const campaign_sim::LineResult result =
          campaign_sim::runLine(K_SEED, K_CAMPAIGN_TURNS, commit, cadence);
      firstDigests.push_back(result.digest);
      EXPECT_EQ(result.view.turn, K_CAMPAIGN_TURNS);
      EXPECT_EQ(result.view.status == game::CampaignStatus::Won, result.view.clearedTurn > 0);
      EXPECT_LE(result.view.clearedTurn, K_CAMPAIGN_TURNS);
      std::printf("  %c %-9lld", statusLetter(result.view.status),
                  static_cast<long long>(result.view.clearedTurn));
    }
    std::printf("\n");
  }
  // Replay every cell and compare with its first run.
  std::size_t cell = 0;
  for (std::int64_t cadence = 1; cadence <= K_MAX_CADENCE; ++cadence) {
    for (const Commit commit : lines) {
      EXPECT_EQ(campaign_sim::runLine(K_SEED, K_CAMPAIGN_TURNS, commit, cadence).digest,
                firstDigests.at(cell))
          << "cadence " << cadence << " line " << campaign_sim::commitLabel(commit);
      ++cell;
    }
  }
}

namespace {

using constellation_sim::PlayerLine;
constexpr std::array<PlayerLine, 3> K_PLAYER_LINES = {PlayerLine::Outer, PlayerLine::AllIn,
                                                      PlayerLine::Contest};

// Plays and prints one rival's grid, checking every cell's outcome is well
// formed, and returns each cell's digest in grid order.
std::vector<std::uint64_t> sweepAgainst(game::FactionPolicy rival) {
  std::printf("constellation sweep vs %s (seed %llu, %lld turns): player status/decided turn\n",
              game::factionPolicyName(rival), static_cast<unsigned long long>(K_SEED),
              static_cast<long long>(K_CONSTELLATION_TURNS));
  std::printf("cadence  outer        all-in       contest\n");
  std::vector<std::uint64_t> digests;
  for (std::int64_t cadence = 1; cadence <= K_MAX_CADENCE; ++cadence) {
    std::printf("%7lld", static_cast<long long>(cadence));
    for (const PlayerLine line : K_PLAYER_LINES) {
      const constellation_sim::LineResult result =
          constellation_sim::runLine(K_SEED, K_CONSTELLATION_TURNS, line, rival, cadence);
      digests.push_back(result.digest);
      // The scenario's deadline equals the turn budget, so every run is
      // decided: by a winner, or by the deadline with none.
      EXPECT_LE(result.turn, K_CONSTELLATION_TURNS);
      EXPECT_NE(result.overallStatus, game::CampaignStatus::Ongoing);
      if (result.winner == game::K_INVALID_FACTION_ID) {
        EXPECT_EQ(result.turn, K_CONSTELLATION_TURNS);
      }
      std::printf("  %c %-9lld", statusLetter(result.overallStatus),
                  static_cast<long long>(result.turn));
    }
    std::printf("\n");
  }
  return digests;
}

// Replays every cell of one rival's grid against its first-run digest.
void replayAgainst(game::FactionPolicy rival, const std::vector<std::uint64_t> &firstDigests) {
  std::size_t cell = 0;
  for (std::int64_t cadence = 1; cadence <= K_MAX_CADENCE; ++cadence) {
    for (const PlayerLine line : K_PLAYER_LINES) {
      EXPECT_EQ(
          constellation_sim::runLine(K_SEED, K_CONSTELLATION_TURNS, line, rival, cadence).digest,
          firstDigests.at(cell))
          << game::factionPolicyName(rival) << " cadence " << cadence << " line "
          << constellation_sim::lineName(line);
      ++cell;
    }
  }
}

} // namespace

// Falsifier: a constellation run against either rival policy at any player
// cadence 1..30 running past its 1400-turn budget, ending undecided, ending
// without a winner before the deadline, or any cell replaying to a digest
// different from its first run. The grid records the player's status and the
// deciding turn.
TEST(BalanceSweep, ConstellationLinesAcrossRivalAndCadence) {
  for (const game::FactionPolicy rival :
       {game::FactionPolicy::Expansionist, game::FactionPolicy::Contester}) {
    replayAgainst(rival, sweepAgainst(rival));
  }
}
