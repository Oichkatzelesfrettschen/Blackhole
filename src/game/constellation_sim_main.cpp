/**
 * @file constellation_sim_main.cpp
 * @brief Headless constellation determinism probe and balance harness.
 *
 * Replays the player commitment lines over the default two-system scenario -- the
 * same one the desktop client would play -- against the Expansionist rival, and
 * prints each line's outcome: the player's fate, who won, the deciding turn, the
 * player's banked energy, stabilization, and control score, and the determinism
 * digest. Two runs of the same invocation on the same binary and host print
 * identical digests; the process links only the campaign and physics libraries,
 * proving the constellation seam is GL-free.
 *
 * Left alone, the Expansionist rival fans across both systems and wins by
 * domination before a concentrated player line completes its own race, so the
 * Outer and AllIn lines lose while the Contest line, spending fleets to deny the
 * rival, survives. campaign of record: constellation_balance_invariant_test.
 */

#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include "game/campaign_view.h"
#include "game/constellation_sim_lines.h"
#include "game/constellation_view.h"

namespace {

using constellation_sim::LineResult;
using constellation_sim::lineName;
using constellation_sim::PlayerLine;
using constellation_sim::runLine;

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

void printLine(PlayerLine line, const LineResult &result) {
  static_cast<void>(std::printf("%-8s player=%-4s winner=%u decided=%" PRId64
                                " digest=%016" PRIx64 "\n",
                                lineName(line), statusName(result.overallStatus), result.winner,
                                result.turn, result.digest));
  for (const game::FactionStanding &standing : result.view.factions) {
    const char *who = standing.id == result.view.playerFaction ? "player" : "rival ";
    static_cast<void>(std::printf(
        "    %s id=%u energy=%9.2f stab=%6.3f control=%9.2f held=%u status=%s\n", who, standing.id,
        standing.energyUnits, standing.stabilizationUnits, standing.controlScore,
        standing.heldBandCount, statusName(standing.status)));
  }
}

} // namespace

int main(int argc, char **argv) {
  std::uint64_t seed = 42;
  std::int64_t turns = 1400;
  PlayerLine line = PlayerLine::Contest;
  bool compareAll = false;
  for (int argIndex = 1; argIndex < argc; ++argIndex) {
    if (std::strcmp(argv[argIndex], "--outer") == 0) {
      line = PlayerLine::Outer;
    } else if (std::strcmp(argv[argIndex], "--all-in") == 0) {
      line = PlayerLine::AllIn;
    } else if (std::strcmp(argv[argIndex], "--contest") == 0) {
      line = PlayerLine::Contest;
    } else if (std::strcmp(argv[argIndex], "--compare") == 0) {
      compareAll = true;
    } else if (std::strcmp(argv[argIndex], "--seed") == 0 && argIndex + 1 < argc) {
      seed = std::strtoull(argv[++argIndex], nullptr, 10);
    } else if (std::strcmp(argv[argIndex], "--turns") == 0 && argIndex + 1 < argc) {
      turns = std::strtoll(argv[++argIndex], nullptr, 10);
    }
  }

  if (compareAll) {
    printLine(PlayerLine::Outer, runLine(seed, turns, PlayerLine::Outer));
    printLine(PlayerLine::AllIn, runLine(seed, turns, PlayerLine::AllIn));
    printLine(PlayerLine::Contest, runLine(seed, turns, PlayerLine::Contest));
    return EXIT_SUCCESS;
  }
  printLine(line, runLine(seed, turns, line));
  return EXIT_SUCCESS;
}
