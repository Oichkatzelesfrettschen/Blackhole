/**
 * @file campaign_sim_main.cpp
 * @brief Headless campaign determinism probe and balance harness.
 *
 * Replays scripted commitment lines over the canonical CampaignSession scenario
 * (the same one the desktop client plays) and prints each line's outcome vector
 * -- banked energy, the singularity's instability, the stabilization a deep
 * prograde lane achieved, the surviving fleet integrity, the turn a victory
 * cleared -- plus the determinism digest. Two runs of the same invocation on the
 * same binary and host print identical digests; the process links only the
 * campaign and physics libraries, proving the seam is GL-free.
 *
 * The default scenario has two winning lines and no viable middle. The outer
 * line wins the energy objective near the deadline; the all-in stabilize line
 * (every fleet deep) forgoes the energy race and instead reaches the alternate
 * stabilization victory, sooner but banking far less energy. The intermediate
 * solo and pod lines lose both races -- they are traps, not a gradient. This is
 * a deliberate "commit fully to one victory type" shape, pinned by
 * campaign_balance_invariant_test so the harness and the scenario cannot drift
 * apart again.
 */

#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_sim_lines.h"
#include "game/campaign_view.h"

namespace {

using campaign_sim::Commit;
using campaign_sim::commitLabel;
using campaign_sim::LineResult;
using campaign_sim::runLine;

const char *statusName(game::CampaignStatus status) {
  switch (status) {
    case game::CampaignStatus::Won:
      return "won";
    case game::CampaignStatus::Lost:
      return "lost";
    case game::CampaignStatus::Ongoing:
    default:
      return "ongoing";
  }
}

void printLine(const char *label, const LineResult &result) {
  const game::CampaignViewSnapshot &view = result.view;
  static_cast<void>(std::printf(
      "%-6s energy=%7.3f instability=%6.3f stabilization=%6.3f integrity=%5.3f "
      "cleared=%-5" PRId64 " status=%-4s digest=%016" PRIx64 "\n",
      label, view.energyUnits, view.instability, view.stabilization, view.fleetIntegrity,
      view.clearedTurn, statusName(view.status), result.digest));
}

} // namespace

int main(int argc, char **argv) {
  std::uint64_t seed = 42;
  std::int64_t turns = 1200;
  Commit commit = Commit::Solo;
  bool compareAll = false;
  for (int argIndex = 1; argIndex < argc; ++argIndex) {
    if (std::strcmp(argv[argIndex], "--no-dive") == 0) {
      commit = Commit::Outer;
    } else if (std::strcmp(argv[argIndex], "--pod") == 0) {
      commit = Commit::Pod;
    } else if (std::strcmp(argv[argIndex], "--stabilize") == 0) {
      commit = Commit::Stabilize;
    } else if (std::strcmp(argv[argIndex], "--compare") == 0) {
      compareAll = true;
    } else if (std::strcmp(argv[argIndex], "--seed") == 0 && argIndex + 1 < argc) {
      seed = std::strtoull(argv[++argIndex], nullptr, 10);
    } else if (std::strcmp(argv[argIndex], "--turns") == 0 && argIndex + 1 < argc) {
      turns = std::strtoll(argv[++argIndex], nullptr, 10);
    }
  }

  if (compareAll) {
    printLine("outer", runLine(seed, turns, Commit::Outer));
    printLine("solo", runLine(seed, turns, Commit::Solo));
    printLine("pod", runLine(seed, turns, Commit::Pod));
    printLine("stab", runLine(seed, turns, Commit::Stabilize));
    return EXIT_SUCCESS;
  }

  game::CampaignSession session(seed);
  if (!session.state().valid()) {
    static_cast<void>(std::fprintf(stderr, "campaign_sim: invalid campaign configuration\n"));
    return EXIT_FAILURE;
  }
  printLine(commitLabel(commit), runLine(seed, turns, commit));
  return EXIT_SUCCESS;
}
