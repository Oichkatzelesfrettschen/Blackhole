/**
 * @file campaign_balance_invariant_test.cpp
 * @brief Pins the default scenario's intended balance shape so it cannot drift.
 *
 * The scenario is deliberately a "commit fully to one victory type" design: the
 * outer line wins the energy objective near the deadline, the all-in stabilize
 * line wins the alternate stabilization victory sooner but banks far less energy,
 * and the intermediate solo and pod lines lose both races. This test asserts
 * that shape -- which line wins, by which objective, and on which turn -- over
 * the same commitment lines the headless harness prints, so a retune that breaks
 * the invariant fails here instead of silently contradicting the harness prose.
 */

#include <gtest/gtest.h>

#include <cstdint>

#include "game/campaign_sim_lines.h"
#include "game/campaign_view.h"

namespace {

using campaign_sim::Commit;
using campaign_sim::runLine;

constexpr std::uint64_t K_SEED = 42;
constexpr std::int64_t K_DEADLINE_TURNS = 1200;

game::CampaignViewSnapshot play(Commit commit) {
  return runLine(K_SEED, K_DEADLINE_TURNS, commit).view;
}

} // namespace

// The outer line wins by banking the energy objective, and only that objective,
// near the deadline -- the tense energy race.
TEST(CampaignBalanceInvariant, OuterWinsEnergyNearDeadline) {
  const game::CampaignViewSnapshot outer = play(Commit::Outer);
  EXPECT_EQ(outer.status, game::CampaignStatus::Won);
  EXPECT_GE(outer.energyUnits, outer.victoryEnergyUnits);       // won by energy
  EXPECT_LT(outer.stabilization, outer.victoryStabilizationUnits); // not by stabilization
  EXPECT_EQ(outer.clearedTurn, 1097);
}

// The all-in stabilize line wins the alternate stabilization victory -- sooner
// than the energy line -- and does NOT reach the energy objective.
TEST(CampaignBalanceInvariant, StabilizeWinsStabilizationSooner) {
  const game::CampaignViewSnapshot stab = play(Commit::Stabilize);
  EXPECT_EQ(stab.status, game::CampaignStatus::Won);
  EXPECT_GE(stab.stabilization, stab.victoryStabilizationUnits); // won by stabilization
  EXPECT_LT(stab.energyUnits, stab.victoryEnergyUnits);          // not by energy
  EXPECT_EQ(stab.clearedTurn, 819);
  EXPECT_LT(stab.clearedTurn, 1097); // the stabilization win lands before the energy win
}

// The intermediate lines are traps: a partial dive banks neither enough energy
// nor enough stabilization, so it loses both races.
TEST(CampaignBalanceInvariant, PartialDivesLose) {
  const game::CampaignViewSnapshot solo = play(Commit::Solo);
  EXPECT_EQ(solo.status, game::CampaignStatus::Lost);
  EXPECT_LT(solo.energyUnits, solo.victoryEnergyUnits);
  EXPECT_LT(solo.stabilization, solo.victoryStabilizationUnits);

  const game::CampaignViewSnapshot pod = play(Commit::Pod);
  EXPECT_EQ(pod.status, game::CampaignStatus::Lost);
  EXPECT_LT(pod.energyUnits, pod.victoryEnergyUnits);
  EXPECT_LT(pod.stabilization, pod.victoryStabilizationUnits);
}

// The harness is deterministic: replaying a line yields an identical digest.
TEST(CampaignBalanceInvariant, LinesAreDeterministic) {
  EXPECT_EQ(runLine(K_SEED, K_DEADLINE_TURNS, Commit::Outer).digest,
            runLine(K_SEED, K_DEADLINE_TURNS, Commit::Outer).digest);
  EXPECT_EQ(runLine(K_SEED, K_DEADLINE_TURNS, Commit::Stabilize).digest,
            runLine(K_SEED, K_DEADLINE_TURNS, Commit::Stabilize).digest);
}
