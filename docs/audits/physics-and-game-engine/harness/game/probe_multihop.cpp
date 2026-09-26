#include <cstdio>
#include "game/constellation.h"
#include "game/kerr_time_field.h"
int main() {
  constexpr double kMsun = 1.989e33;
  const game::KerrTimeField field(1.0e6 * kMsun, 0.0);
  const double rS = field.schwarzschildRadiusCm();
  const game::SystemSpec spec{.blackHoleMassG = 1.0e6 * kMsun, .spinDimensionless = 0.0,
                              .authorityRadiusCm = 200.0 * rS, .bandRadiusCm = {3.0 * rS, 10.0 * rS}};
  game::ConstellationConfig config;
  config.secondsPerTurn = 86400.0;
  config.systems = {spec, spec, spec};
  const double ld30 = 30.0 * 86400.0 * 2.99792458e10;
  config.links = {{.a = 0, .b = 1, .separationCm = ld30}, {.a = 1, .b = 2, .separationCm = ld30}};
  game::Constellation c(config);
  const game::FactionId alpha = c.addFaction(game::FactionPolicy::Scripted, 0);
  c.addFaction(game::FactionPolicy::Scripted, 1);
  c.addFaction(game::FactionPolicy::Scripted, 2);
  c.addFleet(alpha, 0, game::FleetCapability::Extraction, 0);
  c.advanceTurns(2);
  std::printf("chain 0-1-2 (30 ld per hop): after 2 turns observer@1 sees %u, observer@2 (60 ld away, unlinked) sees %u; alpha=%u\n",
              c.perceivedController(1, 0, 0), c.perceivedController(2, 0, 0), alpha);
  return 0;
}
