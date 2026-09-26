// Audit probes against HEAD game sources (scratch build only).
#include <cstdio>

#include "game/constellation.h"
#include "game/constellation_session.h"
#include "game/kerr_time_field.h"

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_G = 6.5e9 * K_SOLAR_MASS_G;

game::ConstellationConfig oneSystem(double spin) {
  const game::KerrTimeField field(K_M87_G, spin);
  const double rS = field.schwarzschildRadiusCm();
  game::ConstellationConfig config;
  config.secondsPerTurn = 86400.0;
  config.systems = {game::SystemSpec{.blackHoleMassG = K_M87_G,
                                     .spinDimensionless = spin,
                                     .authorityRadiusCm = 200.0 * rS,
                                     .bandRadiusCm = {0.85 * rS, 3.0 * rS, 10.0 * rS, 50.0 * rS}}};
  config.fleetInitialFuelUnits = 1.0e6;
  return config;
}

// Probe 1: continuous-work yield per coordinate turn versus band (no bonuses).
void yieldVersusBand() {
  std::puts("probe1: energy banked after 3000 turns, one fleet, no bonus/wear/instability");
  for (int band = 0; band < 4; ++band) {
    game::Constellation constellation(oneSystem(0.9));
    const game::FactionId faction = constellation.addFaction(game::FactionPolicy::Scripted, 0);
    constellation.addFleet(faction, 0, game::FleetCapability::Fabrication, band);
    constellation.advanceTurns(3000);
    const game::KerrTimeField &field = constellation.systems().front().field;
    const double rate = field.properTimeRate(constellation.systems().front().bandRadiusCm.at(
        static_cast<std::size_t>(band)));
    const double delayDays =
        field.signalDelaySec(constellation.systems().front().bandRadiusCm.at(
                                 static_cast<std::size_t>(band)),
                             constellation.systems().front().authorityRadiusCm) /
        86400.0;
    std::printf("  band %d dtau/dt=%.4f report delay=%.1f d energy=%.2f\n", band, rate, delayDays,
                constellation.factions().front().energyUnits);
  }
}

// Probe 2: same-system control intel delay versus the radial light delay.
void sameSystemIntel() {
  game::Constellation constellation(oneSystem(0.9));
  const game::FactionId alpha = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  const game::FactionId beta = constellation.addFaction(game::FactionPolicy::Scripted, 0);
  static_cast<void>(beta);
  constellation.addFleet(alpha, 0, game::FleetCapability::Extraction, 0);
  constellation.advanceTurns(2);
  const auto &system = constellation.systems().front();
  const double delayDays =
      system.field.signalDelaySec(system.bandRadiusCm.at(0), system.authorityRadiusCm) / 86400.0;
  std::printf("probe2: after 2 turns beta perceives band0 controller=%u (alpha=%u); radial light "
              "delay band0->authority = %.1f turns\n",
              constellation.perceivedController(1, 0, 0), alpha, delayDays);
}

// Probe 3: interstellar transit proper time versus coordinate time at 0.5c.
// Accumulates only turns where inTransit is true after the update, since the order-delay
// turns before departure and the landing turn (landArrivals runs before runFleetWork, so
// the landing turn's properTimeSec delta is already a band-rate, non-transit day) are not
// transit time.
void transitProperTime() {
  game::ConstellationSession session(42);
  game::Constellation &constellation = session.constellation();
  const game::FleetId fleet = constellation.fleets().front().id;
  static_cast<void>(session.movePlayerFleet(fleet, 1, 1));
  double transitProperSec = 0.0;
  std::int64_t transitTurns = 0;
  for (int turn = 0; turn < 400; ++turn) {
    const double beforeProperTimeSec = constellation.fleets().front().properTimeSec;
    constellation.advanceTurn();
    const game::ConstellationFleet &current = constellation.fleets().front();
    if (current.inTransit) {
      transitProperSec += current.properTimeSec - beforeProperTimeSec;
      ++transitTurns;
    } else if (transitTurns > 0) {
      std::printf("probe3: transit %lld coordinate turns, fleet aged %.2f proper days "
                  "(special relativity at 0.5c: %.2f)\n",
                  static_cast<long long>(transitTurns), transitProperSec / 86400.0,
                  static_cast<double>(transitTurns) * 0.8660254);
      return;
    }
  }
}

} // namespace

int main() {
  yieldVersusBand();
  sameSystemIntel();
  transitProperTime();
  return 0;
}
