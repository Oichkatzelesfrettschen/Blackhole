/**
 * @file campaign_sim_main.cpp
 * @brief Headless campaign determinism probe.
 *
 * Replays a scripted command log over the canonical CampaignSession scenario
 * (the same one the desktop client plays) and prints the final state digest.
 * Two runs of the same invocation on the same binary and host must print
 * identical digests; the process links only the campaign and physics
 * libraries, proving the seam is GL-free.
 */

#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/fleet.h"

int main(int argc, char **argv) {
  std::uint64_t seed = 42;
  std::int64_t turns = 400;
  for (int argIndex = 1; argIndex + 1 < argc; argIndex += 2) {
    if (std::strcmp(argv[argIndex], "--seed") == 0) {
      seed = std::strtoull(argv[argIndex + 1], nullptr, 10);
    } else if (std::strcmp(argv[argIndex], "--turns") == 0) {
      turns = std::strtoll(argv[argIndex + 1], nullptr, 10);
    }
  }

  game::CampaignSession session(seed);
  game::CampaignState &campaign = session.state();
  if (!campaign.valid()) {
    static_cast<void>(std::fprintf(stderr, "campaign_sim: invalid campaign configuration\n"));
    return EXIT_FAILURE;
  }

  // The canonical scenario creates six fleets with stable ids 1..6:
  // extraction/research on the inner band, fabrication/relay on the middle,
  // verification/survey research on the outer.
  constexpr game::FleetId extractionFleet = 1;
  constexpr game::FleetId researchFleet = 2;
  constexpr game::FleetId fabricationFleet = 3;
  constexpr game::FleetId relayFleet = 4;
  constexpr game::FleetId verificationFleet = 5;
  constexpr game::FleetId surveyFleet = 6;

  // Scripted opening orders: one contract per fleet, deep work is expensive.
  const struct {
    game::FleetId fleet;
    double costHours;
  } contracts[] = {{.fleet = extractionFleet, .costHours = 40.0},
                   {.fleet = researchFleet, .costHours = 25.0},
                   {.fleet = fabricationFleet, .costHours = 60.0},
                   {.fleet = relayFleet, .costHours = 15.0},
                   {.fleet = verificationFleet, .costHours = 30.0},
                   {.fleet = surveyFleet, .costHours = 20.0}};
  for (const auto &contract : contracts) {
    if (!session.issueAssignTask(contract.fleet, contract.costHours)) {
      static_cast<void>(std::fprintf(stderr, "campaign_sim: opening order rejected\n"));
      return EXIT_FAILURE;
    }
  }

  // Mid-campaign redeployment: pull the outer survey fleet inward, then
  // contract it for a near-horizon observation run.
  const std::int64_t redeployTurn = turns / 2;
  campaign.advanceTurns(redeployTurn);
  if (session.issuePlaceFleet(surveyFleet, 0)) {
    static_cast<void>(session.issueAssignTask(surveyFleet, 10.0));
  }
  campaign.advanceTurns(turns - redeployTurn);

  const char *statusName = "ongoing";
  if (campaign.status() == game::CampaignStatus::Won) {
    statusName = "won";
  } else if (campaign.status() == game::CampaignStatus::Lost) {
    statusName = "lost";
  }
  static_cast<void>(std::printf(
      "turns=%" PRId64 " seed=%" PRIu64 " fleets=%zu tasks=%zu intel=%zu energy=%.3f status=%s "
      "digest=%016" PRIx64 "\n",
      campaign.turn(), seed, campaign.fleets().size(), campaign.taskGraph().tasks().size(),
      campaign.intelLog().size(), campaign.energyUnits(), statusName, campaign.stateDigest()));
  return EXIT_SUCCESS;
}
