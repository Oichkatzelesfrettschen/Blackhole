/**
 * @file campaign_sim_main.cpp
 * @brief Headless campaign determinism probe and balance harness.
 *
 * Replays scripted command logs over the canonical CampaignSession scenario
 * (the same one the desktop client plays) and prints the final state digest
 * plus the CAMPAIGN-6 outcome vector -- banked energy, the singularity's
 * instability, the stabilization a deep prograde lane achieved, the surviving
 * fleet integrity, and the turn the objective cleared. Two runs of the same
 * invocation on the same binary and host print identical digests; the process
 * links only the campaign and physics libraries, proving the seam is GL-free.
 *
 * The outcome is deliberately reported as a VECTOR, not a single winner. A
 * --commit level chooses how many fleets are sent into the deep prograde
 * ergoregion lane (none / solo / a self-sustaining pod). Comparing the three
 * lines shows the Pareto structure the balance targets: the deep lane clears
 * sooner and banks more stabilization, the outer line keeps its fleets whole,
 * and neither dominates on every axis.
 */

#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <vector>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/fleet.h"

namespace {

// The canonical scenario creates six fleets with stable ids 1..6: extraction
// and research on the inner outer band, fabrication and relay on the middle,
// verification and survey research on the outer.
constexpr game::FleetId K_EXTRACTION = 1;
constexpr game::FleetId K_RESEARCH = 2;
constexpr game::FleetId K_FABRICATION = 3;
constexpr game::FleetId K_RELAY = 4;
constexpr game::FleetId K_VERIFICATION = 5;
constexpr game::FleetId K_SURVEY = 6;

constexpr int K_ERGO_BAND = 0;
constexpr double K_REISSUE_HOURS = 24.0; ///< Uniform contract size for the sustaining cadence.
constexpr std::int64_t K_REISSUE_EVERY = 30; ///< Re-task every fleet this often to keep work (and containment) flowing.

enum class Commit {
  Outer, ///< No deep lane: every fleet stays on the outer bands.
  Solo,  ///< One survey fleet holds the deep prograde ergoregion lane.
  Pod,   ///< Survey plus co-located verification and fabrication sustain the dive.
};

/** @brief Fleets sent into the ergoregion band for a commitment level. The pod
 *         co-locates verification (holds telemetry above the corruption cliff)
 *         and fabrication (refuels the lane) so the deep line is sustainable. */
std::vector<game::FleetId> deepFleets(Commit commit) {
  switch (commit) {
    case Commit::Solo:
      return {K_SURVEY};
    case Commit::Pod:
      return {K_SURVEY, K_VERIFICATION, K_FABRICATION};
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

/** @brief Runs one commitment line to completion and reports its outcome
 *         vector. Every fleet is re-tasked on a fixed cadence so work -- and
 *         the deep lane's containment -- is sustained across the campaign. */
LineResult runLine(std::uint64_t seed, std::int64_t turns, Commit commit) {
  game::CampaignSession session(seed);
  game::CampaignState &campaign = session.state();

  // Deep pod redeploys prograde into the ergoregion band before work begins, so
  // its containment covers the whole campaign.
  for (const game::FleetId fleet : deepFleets(commit)) {
    static_cast<void>(session.issuePlaceFleet(fleet, K_ERGO_BAND, game::OrbitLane::Prograde));
  }

  const std::vector<game::FleetId> allFleets = {K_EXTRACTION, K_RESEARCH,     K_FABRICATION,
                                                K_RELAY,      K_VERIFICATION, K_SURVEY};
  for (std::int64_t elapsed = 0; elapsed < turns; ++elapsed) {
    if (elapsed % K_REISSUE_EVERY == 0) {
      for (const game::FleetId fleet : allFleets) {
        static_cast<void>(session.issueAssignTask(fleet, K_REISSUE_HOURS));
      }
    }
    campaign.advanceTurn();
  }
  return LineResult{.view = campaign.renderSnapshot(), .digest = campaign.stateDigest()};
}

const char *commitLabel(Commit commit) {
  switch (commit) {
    case Commit::Outer:
      return "outer";
    case Commit::Pod:
      return "pod";
    case Commit::Solo:
    default:
      return "solo";
  }
}

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
    } else if (std::strcmp(argv[argIndex], "--compare") == 0) {
      compareAll = true;
    } else if (std::strcmp(argv[argIndex], "--seed") == 0 && argIndex + 1 < argc) {
      seed = std::strtoull(argv[++argIndex], nullptr, 10);
    } else if (std::strcmp(argv[argIndex], "--turns") == 0 && argIndex + 1 < argc) {
      turns = std::strtoll(argv[++argIndex], nullptr, 10);
    }
  }

  if (compareAll) {
    // The three-line Pareto probe: no single line dominates on every axis.
    printLine("outer", runLine(seed, turns, Commit::Outer));
    printLine("solo", runLine(seed, turns, Commit::Solo));
    printLine("pod", runLine(seed, turns, Commit::Pod));
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
