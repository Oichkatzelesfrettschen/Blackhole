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
 *
 * `--colony STORY.json` instead plays the Gargantua colony story on Miller's
 * orbit and on the 100M orbit past the host's dark turn, with orders from the
 * host and the colony, and prints digest checkpoints every 2000 turns and the
 * outcome axes -- the story, node clocks, and event code under the same
 * cross-ISA digest gates as the default lines.
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
#include "game/event.h"
#include "game/event_loader.h"

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

/** @brief Plays the colony story on one band and prints its checkpoints. */
void playColony(const game::EventSet &story, std::uint64_t seed, int colonyBand) {
  game::CampaignSession session(seed, story, colonyBand);
  game::CampaignState &state = session.state();
  const std::int64_t horizon = state.storyParam("dark_turn").value_or(0) +
                               state.nodeDelayTurns(0, 1) +
                               (4 * state.storyParam("packet_period").value_or(0)) + 60;
  for (std::int64_t turn = 0; turn < horizon; ++turn) {
    if (turn % 250 == 0) {
      const game::NodeId origin =
          turn % 500 == 0 ? game::K_AUTHORITY_NODE : game::K_FIRST_COLONY_NODE;
      static_cast<void>(session.issueAssignTask(1, 6.0, origin));
    }
    state.advanceTurn();
    if (state.turn() % 2000 == 0) {
      static_cast<void>(std::printf("colony band=%d turn=%-6" PRId64 " digest=%016" PRIx64 "\n",
                                    colonyBand, state.turn(), state.stateDigest()));
    }
  }
  const game::CampaignViewSnapshot view = state.renderSnapshot();
  static_cast<void>(std::printf(
      "colony band=%d tier=%" PRId64 " energy=%.3f lost=%.3f arrivals=%zu digest=%016" PRIx64
      "\n",
      colonyBand, view.colonyTechTier, view.energyUnits, view.energyLostToDarkness,
      view.arrivals.size(), state.stateDigest()));
}

} // namespace

int main(int argc, char **argv) {
  std::uint64_t seed = 42;
  std::int64_t turns = 1200;
  Commit commit = Commit::Solo;
  bool compareAll = false;
  const char *colonyStory = nullptr;
  for (int argIndex = 1; argIndex < argc; ++argIndex) {
    if (std::strcmp(argv[argIndex], "--no-dive") == 0) {
      commit = Commit::Outer;
    } else if (std::strcmp(argv[argIndex], "--pod") == 0) {
      commit = Commit::Pod;
    } else if (std::strcmp(argv[argIndex], "--stabilize") == 0) {
      commit = Commit::Stabilize;
    } else if (std::strcmp(argv[argIndex], "--colony") == 0 && argIndex + 1 < argc) {
      colonyStory = argv[++argIndex];
    } else if (std::strcmp(argv[argIndex], "--compare") == 0) {
      compareAll = true;
    } else if (std::strcmp(argv[argIndex], "--seed") == 0 && argIndex + 1 < argc) {
      seed = std::strtoull(argv[++argIndex], nullptr, 10);
    } else if (std::strcmp(argv[argIndex], "--turns") == 0 && argIndex + 1 < argc) {
      turns = std::strtoll(argv[++argIndex], nullptr, 10);
    }
  }

  if (colonyStory != nullptr) {
    const game::EventLoadResult loaded = game::loadEventSetFile(colonyStory);
    if (!loaded.ok()) {
      static_cast<void>(std::fprintf(stderr, "campaign_sim: %s\n", loaded.error.c_str()));
      return EXIT_FAILURE;
    }
    playColony(loaded.story, seed, 0);
    playColony(loaded.story, seed, 1);
    return EXIT_SUCCESS;
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
