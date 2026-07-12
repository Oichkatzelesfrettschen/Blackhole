/**
 * @file campaign_sim_main.cpp
 * @brief Headless campaign determinism probe.
 *
 * Builds the canonical vertical-slice scenario (one system, three orbital
 * bands, six fleets), replays a scripted command log for a given number of
 * turns, and prints the final state digest. Two runs of the same invocation on
 * the same binary and host must print identical digests; the process links
 * only the campaign and physics libraries, proving the seam is GL-free.
 */

#include <cinttypes>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <utility>

#include "game/blackhole_time_field.h"
#include "game/campaign.h"
#include "game/fleet.h"

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;

} // namespace

int main(int argc, char **argv) {
  // One-day turns: at M87* scale the authority-to-inner-band light delay is
  // ~150 days, so a 400-turn default run sees orders land, tasks complete,
  // and completion reports arrive back at the authority station.
  std::uint64_t seed = 42;
  std::int64_t turns = 400;
  for (int argIndex = 1; argIndex + 1 < argc; argIndex += 2) {
    if (std::strcmp(argv[argIndex], "--seed") == 0) {
      seed = std::strtoull(argv[argIndex + 1], nullptr, 10);
    } else if (std::strcmp(argv[argIndex], "--turns") == 0) {
      turns = std::strtoll(argv[argIndex + 1], nullptr, 10);
    }
  }

  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();

  game::CampaignConfig config;
  config.seed = seed;
  config.secondsPerTurn = 86400.0;
  config.authorityRadiusCm = 200.0 * horizonCm;
  config.bandRadiusCm = {3.0 * horizonCm, 10.0 * horizonCm, 50.0 * horizonCm};

  game::CampaignState campaign(std::move(config), field);
  if (!campaign.valid()) {
    static_cast<void>(std::fprintf(stderr, "campaign_sim: invalid campaign configuration\n"));
    return EXIT_FAILURE;
  }

  // Two fleets per band, specialist mix per the vertical-slice shape.
  const game::FleetId extraction = campaign.addFleet(game::FleetCapability::Extraction, 0);
  const game::FleetId research = campaign.addFleet(game::FleetCapability::Research, 0);
  const game::FleetId fabrication = campaign.addFleet(game::FleetCapability::Fabrication, 1);
  const game::FleetId relay = campaign.addFleet(game::FleetCapability::Relay, 1);
  const game::FleetId verification = campaign.addFleet(game::FleetCapability::Verification, 2);
  const game::FleetId survey = campaign.addFleet(game::FleetCapability::Research, 2);

  const game::FleetId allFleets[] = {extraction,  research,     fabrication,
                                     relay,       verification, survey};
  for (const game::FleetId fleetId : allFleets) {
    if (fleetId == game::K_INVALID_FLEET_ID) {
      static_cast<void>(std::fprintf(stderr, "campaign_sim: fleet setup rejected\n"));
      return EXIT_FAILURE;
    }
  }

  // Scripted opening orders: one contract per fleet, deep work is expensive.
  const double hourSec = 3600.0;
  game::Command assign;
  assign.type = game::CommandType::AssignTask;
  struct OpeningContract {
    game::FleetId fleet = game::K_INVALID_FLEET_ID;
    double costHours = 0.0;
  };
  const OpeningContract contracts[] = {
      {.fleet = extraction, .costHours = 40.0},   {.fleet = research, .costHours = 25.0},
      {.fleet = fabrication, .costHours = 60.0},  {.fleet = relay, .costHours = 15.0},
      {.fleet = verification, .costHours = 30.0}, {.fleet = survey, .costHours = 20.0}};
  for (const auto &contract : contracts) {
    assign.fleet = contract.fleet;
    assign.properTimeCostSec = contract.costHours * hourSec;
    if (!campaign.issueCommand(assign)) {
      static_cast<void>(std::fprintf(stderr, "campaign_sim: opening order rejected\n"));
      return EXIT_FAILURE;
    }
  }

  // Mid-campaign redeployment: pull the outer survey fleet inward, then
  // contract it for a near-horizon observation run.
  const std::int64_t redeployTurn = turns / 2;
  campaign.advanceTurns(redeployTurn);
  game::Command redeploy;
  redeploy.type = game::CommandType::PlaceFleet;
  redeploy.fleet = survey;
  redeploy.targetBand = 0;
  if (campaign.issueCommand(redeploy)) {
    assign.fleet = survey;
    assign.properTimeCostSec = 10.0 * hourSec;
    (void)campaign.issueCommand(assign);
  }
  campaign.advanceTurns(turns - redeployTurn);

  static_cast<void>(std::printf("turns=%" PRId64 " seed=%" PRIu64 " fleets=%zu tasks=%zu intel=%zu digest=%016" PRIx64
              "\n",
              campaign.turn(), seed, campaign.fleets().size(), campaign.taskGraph().tasks().size(),
              campaign.intelLog().size(), campaign.stateDigest()));
  return EXIT_SUCCESS;
}
