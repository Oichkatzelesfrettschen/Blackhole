/**
 * @file kerr_time_field_test.cpp
 * @brief Falsification gates for the Kerr TimeField: exact reduction to the
 *        Schwarzschild field at zero spin, ZAMO lapse valid into the ergoregion
 *        where the static observer is not, a spin-shrunk horizon, and frame
 *        dragging that rises toward the horizon.
 */

#include <gtest/gtest.h>

#include <array>
#include <cmath>

#include "game/blackhole_time_field.h"
#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/fleet.h"
#include "game/kerr_time_field.h"
#include "game/observer.h"

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;

} // namespace

TEST(KerrTimeField, ZeroSpinReducesExactlyToSchwarzschild) {
  const game::BlackholeTimeField schwarzschild(K_M87_MASS_G);
  const game::KerrTimeField kerr(K_M87_MASS_G, 0.0);

  EXPECT_DOUBLE_EQ(kerr.innerBoundaryRadiusCm(), schwarzschild.horizonRadiusCm());
  EXPECT_DOUBLE_EQ(kerr.ergosphereRadiusCm(), schwarzschild.horizonRadiusCm());
  EXPECT_DOUBLE_EQ(kerr.spinDimensionless(), 0.0);

  const double horizonCm = schwarzschild.horizonRadiusCm();
  for (const double multiple : {1.01, 1.5, 3.0, 10.0, 100.0, 1000.0}) {
    const double radiusCm = multiple * horizonCm;
    EXPECT_NEAR(kerr.properTimeRate(radiusCm, game::Observer::Hovering),
                schwarzschild.properTimeRate(radiusCm, game::Observer::Hovering), 1e-13)
        << "rate mismatch at " << multiple;
    EXPECT_DOUBLE_EQ(kerr.frameDragRateRadPerSec(radiusCm), 0.0)
        << "no frame dragging without spin";
  }
  // The signal-delay closed form must reproduce the radial Schwarzschild delay
  // across a range of band separations.
  for (const double innerMult : {1.5, 3.0, 20.0}) {
    for (const double outerMult : {30.0, 200.0}) {
      const double innerCm = innerMult * horizonCm;
      const double outerCm = outerMult * horizonCm;
      EXPECT_NEAR(kerr.signalDelaySec(innerCm, outerCm),
                  schwarzschild.signalDelaySec(innerCm, outerCm),
                  1e-6 * schwarzschild.signalDelaySec(innerCm, outerCm))
          << "delay mismatch " << innerMult << " -> " << outerMult;
    }
  }
}

TEST(KerrTimeField, SpinShrinksTheHorizonAndOpensAnErgoregion) {
  const game::KerrTimeField kerr(K_M87_MASS_G, 0.9);
  const double gravitationalRadiusCm = kerr.gravitationalRadiusCm();
  // r_+ = M(1 + sqrt(1 - a*^2)); a* = 0.9 -> 1 + sqrt(0.19) ~ 1.4359 M.
  const double expectedHorizon = gravitationalRadiusCm * (1.0 + std::sqrt(1.0 - 0.81));
  EXPECT_NEAR(kerr.outerHorizonCm(), expectedHorizon, 1e-6 * expectedHorizon);
  // Equatorial ergosphere sits at 2M regardless of spin, strictly outside r_+.
  EXPECT_NEAR(kerr.ergosphereRadiusCm(), 2.0 * gravitationalRadiusCm,
              1e-9 * gravitationalRadiusCm);
  EXPECT_GT(kerr.ergosphereRadiusCm(), kerr.outerHorizonCm());
}

TEST(KerrTimeField, ZamoClockRunsInsideTheErgoregion) {
  const game::KerrTimeField kerr(K_M87_MASS_G, 0.9);
  const double gravitationalRadiusCm = kerr.gravitationalRadiusCm();
  // A radius between r_+ (1.436M) and the ergosphere (2M): no static observer
  // exists here, yet the ZAMO lapse is a positive, finite clock.
  const double ergoRadiusCm = 1.7 * gravitationalRadiusCm;
  ASSERT_TRUE(kerr.isValidStationRadius(ergoRadiusCm));
  ASSERT_LT(ergoRadiusCm, kerr.ergosphereRadiusCm());
  const double rate = kerr.properTimeRate(ergoRadiusCm, game::Observer::Hovering);
  EXPECT_GT(rate, 0.0);
  EXPECT_LT(rate, 1.0);
  EXPECT_TRUE(std::isfinite(rate));
  // The static-observer factor 1 - r_s/r would be negative here (imaginary
  // clock); confirm we are genuinely inside the static limit.
  EXPECT_LT(1.0 - (2.0 * gravitationalRadiusCm / ergoRadiusCm), 0.0);
}

TEST(KerrTimeField, FrameDraggingRisesTowardTheHorizon) {
  const game::KerrTimeField kerr(K_M87_MASS_G, 0.9);
  const double horizonCm = kerr.outerHorizonCm();
  double previousOmega = 0.0;
  // Sample inward: each closer radius drags faster.
  for (const double multiple : {50.0, 10.0, 4.0, 2.0, 1.2}) {
    const double omega = kerr.frameDragRateRadPerSec(multiple * horizonCm);
    EXPECT_GT(omega, previousOmega) << "omega must rise inward at " << multiple;
    EXPECT_TRUE(std::isfinite(omega));
    previousOmega = omega;
  }
}

TEST(KerrTimeField, RateMonotoneWithRadiusAndBoundedInUnitInterval) {
  const game::KerrTimeField kerr(K_M87_MASS_G, 0.9);
  const double horizonCm = kerr.outerHorizonCm();
  double previousRate = 0.0;
  for (const double multiple : {1.01, 1.1, 1.5, 3.0, 10.0, 100.0}) {
    const double rate = kerr.properTimeRate(multiple * horizonCm, game::Observer::Hovering);
    EXPECT_GT(rate, 0.0);
    EXPECT_LE(rate, 1.0);
    EXPECT_GT(rate, previousRate) << "rate must rise with radius at " << multiple;
    previousRate = rate;
  }
}

// Falsifier: the three clocks at r = 6M, a = 0.9 departing from the 50-digit
// mpmath values (ZAMO 0.817982, prograde orbit 0.743444, retrograde orbit
// 0.654512; scripts/gen_kerr_observer_reference.py) by more than 1e-12
// relative, or a zero-spin orbit clock differing from Schwarzschild's.
TEST(KerrTimeField, ObserverClocksAtSixM) {
  const game::KerrTimeField kerr(K_M87_MASS_G, 0.9);
  const double radiusCm = 6.0 * kerr.gravitationalRadiusCm();
  EXPECT_NEAR(kerr.properTimeRate(radiusCm, game::Observer::Hovering) / 8.179815713894085549e-1,
              1.0, 1e-12);
  EXPECT_NEAR(kerr.properTimeRate(radiusCm, game::Observer::CircularOrbitPrograde) /
                  7.4344405871481958781e-1,
              1.0, 1e-12);
  EXPECT_NEAR(kerr.properTimeRate(radiusCm, game::Observer::CircularOrbitRetrograde) /
                  6.5451153007973629037e-1,
              1.0, 1e-12);

  const game::KerrTimeField still(K_M87_MASS_G, 0.0);
  const game::BlackholeTimeField schwarzschild(K_M87_MASS_G);
  for (const double multiple : {4.5, 6.0, 20.0, 400.0}) {
    const double orbitCm = multiple * still.gravitationalRadiusCm();
    EXPECT_NEAR(still.properTimeRate(orbitCm, game::Observer::CircularOrbitPrograde),
                schwarzschild.properTimeRate(orbitCm, game::Observer::CircularOrbitPrograde),
                1e-13);
  }
}

// Falsifier: a prograde orbit admitted at 1.7M around a = 0.9, where the
// marginally bound radius is 1.73246M and no bound orbit exists, or a
// retrograde orbit admitted inside its own r_mb = 5.65685M.
TEST(KerrTimeField, OrbitNeedsTheMarginallyBoundRadius) {
  const game::KerrTimeField kerr(K_M87_MASS_G, 0.9);
  const double massCm = kerr.gravitationalRadiusCm();
  EXPECT_NEAR(kerr.marginallyBoundRadiusCm(game::Observer::CircularOrbitPrograde) / massCm,
              1.7324555320336759, 1e-12);
  EXPECT_FALSE(kerr.admitsObserver(1.7 * massCm, game::Observer::CircularOrbitPrograde));
  EXPECT_TRUE(kerr.admitsObserver(1.7 * massCm, game::Observer::Hovering));
  EXPECT_TRUE(kerr.admitsObserver(1.75 * massCm, game::Observer::CircularOrbitPrograde));
  EXPECT_FALSE(kerr.admitsObserver(5.6 * massCm, game::Observer::CircularOrbitRetrograde));
  EXPECT_TRUE(kerr.admitsObserver(5.7 * massCm, game::Observer::CircularOrbitRetrograde));
}

// Falsifier: the default scenario accepting an orbital placement onto the
// 1.7M ergoregion band at issue time (the order must never enter the log), or
// refusing the hovering placement there.
TEST(KerrTimeField, OrbitalPlacementBelowMarginallyBoundIsRejectedAtIssue) {
  game::CampaignSession session(5);
  const game::FleetId fleet = session.state().fleets().front().id;
  EXPECT_FALSE(
      session.issuePlaceFleet(fleet, 0, game::OrbitLane::Prograde, game::StationKeeping::Orbit));
  EXPECT_TRUE(session.state().commandLog().empty());
  EXPECT_TRUE(
      session.issuePlaceFleet(fleet, 0, game::OrbitLane::Prograde, game::StationKeeping::Hover));
  EXPECT_EQ(session.state().commandLog().size(), 1U);
  EXPECT_EQ(session.state().addFleet(game::FleetCapability::Research, 0), game::K_INVALID_FLEET_ID);
  EXPECT_NE(session.state().addFleet(game::FleetCapability::Research, 0, game::OrbitLane::Prograde,
                                     game::StationKeeping::Hover),
            game::K_INVALID_FLEET_ID);
  // Placed fleets on the outer bands orbit, and carry the orbital clock.
  EXPECT_EQ(session.state().fleets().front().observer, game::Observer::CircularOrbitPrograde);
}

// Falsifier: the canon scenario's Miller colony, orbiting the prograde ISCO at
// 1 - a = 1.33e-14, reporting dtau/dt off the mpmath value 1.6285857805e-5
// (61,403x; scripts/gen_kerr_observer_reference.py) by more than 1e-6
// relative, accruing proper time at any other rate, or its band sitting
// anywhere but r - M = 3.7611e-5 M above a bound orbit.
TEST(GargantuaScenario, MillerColonyRunsTheCanonClock) {
  const game::CampaignSession session(9, game::CampaignScenario::GargantuaCanon);
  ASSERT_TRUE(session.state().valid());
  EXPECT_DOUBLE_EQ(session.field().spinDeficit(), 1.33e-14);
  const double massCm = session.field().gravitationalRadiusCm();

  const game::CampaignViewSnapshot view = session.state().renderSnapshot();
  ASSERT_EQ(view.fleets.size(), 2U);
  const game::FleetView &miller = view.fleets.front();
  EXPECT_EQ(miller.bandIndex, 0);
  EXPECT_EQ(miller.observer, game::Observer::CircularOrbitPrograde);
  EXPECT_NEAR(miller.properTimeRate / 1.6285857804897317108e-5, 1.0, 1e-6);
  EXPECT_NEAR(1.0 / miller.properTimeRate, 61403.0, 1.0);
  EXPECT_NEAR((view.bands.at(0).radiusCm / massCm) - 1.0, 3.7611284825013188359e-5, 1e-9);
  EXPECT_TRUE(view.bands.at(0).admitsOrbit);
  EXPECT_TRUE(view.bands.at(0).insideErgosphere);
  EXPECT_GT(view.bands.at(0).delayToAuthoritySec, 0.0);

  // One Miller hour against the outside: seven Julian years to within 0.1%.
  const double outsideYearsPerMillerHour = 3600.0 / miller.properTimeRate / (365.25 * 86400.0);
  EXPECT_NEAR(outsideYearsPerMillerHour, 7.0, 0.007);

  game::CampaignSession played(9, game::CampaignScenario::GargantuaCanon);
  played.state().advanceTurns(10);
  const game::Fleet &colony = played.state().fleets().front();
  EXPECT_NEAR(colony.properTimeSec / (10.0 * 86400.0 * miller.properTimeRate), 1.0, 1e-12);
}

// Falsifier: the default M87 band at 6M reported stable for the retrograde
// lane, whose ISCO is 8.717M (the orbit there is admitted -- r_mb is 5.657M --
// but unstable), or unstable for the prograde lane (ISCO 2.321M); a band
// placed exactly on an ISCO read as unstable after the cm round trip; or a
// band measurably inside an ISCO read as stable.
TEST(KerrTimeField, StableOrbitsStartAtTheIsco) {
  const game::CampaignSession session(4);
  const game::CampaignViewSnapshot view = session.state().renderSnapshot();
  const game::BandView &sixM = view.bands.at(1);
  EXPECT_TRUE(sixM.admitsOrbit);
  EXPECT_TRUE(sixM.stableOrbit);
  EXPECT_TRUE(sixM.admitsRetrogradeOrbit);
  EXPECT_FALSE(sixM.stableRetrogradeOrbit);
  EXPECT_FALSE(view.bands.at(0).admitsOrbit); // 1.7M: below prograde r_mb

  const game::KerrTimeField &field = session.field();
  for (const game::Observer orbit :
       {game::Observer::CircularOrbitPrograde, game::Observer::CircularOrbitRetrograde}) {
    const double iscoCm = field.iscoRadiusCm(orbit);
    EXPECT_TRUE(field.admitsStableOrbit(iscoCm, orbit));
    EXPECT_FALSE(field.admitsStableOrbit(iscoCm * (1.0 - 1e-6), orbit));
  }
  EXPECT_FALSE(field.admitsStableOrbit(field.iscoRadiusCm(game::Observer::CircularOrbitPrograde), game::Observer::Hovering));

  const game::CampaignSession canon(4, game::CampaignScenario::GargantuaCanon);
  EXPECT_TRUE(canon.state().renderSnapshot().bands.at(0).stableOrbit); // Miller on the ISCO
  EXPECT_FALSE(canon.state().renderSnapshot().fleets.front().unstableOrbit);
}

// Falsifier: the band view at 6M around a = 0.9 offering the composer any
// clock but the selected observer's -- hovering 0.817982, prograde orbit
// 0.743444, retrograde orbit 0.654512 (mpmath reference) -- or a nonzero
// orbital clock on the 1.7M band, where no bound orbit exists.
TEST(KerrTimeField, BandViewCarriesEveryObserversClock) {
  const game::CampaignSession session(4);
  const game::CampaignViewSnapshot view = session.state().renderSnapshot();
  const game::BandView &sixM = view.bands.at(1);
  const auto rate = [&](game::OrbitLane lane, game::StationKeeping station) {
    return game::bandRateFor(sixM, lane, station);
  };
  EXPECT_NEAR(rate(game::OrbitLane::Prograde, game::StationKeeping::Hover) / 8.179815713894085549e-1,
              1.0, 1e-12);
  EXPECT_NEAR(rate(game::OrbitLane::Prograde, game::StationKeeping::Orbit) /
                  7.4344405871481958781e-1,
              1.0, 1e-12);
  EXPECT_NEAR(rate(game::OrbitLane::Retrograde, game::StationKeeping::Orbit) /
                  6.5451153007973629037e-1,
              1.0, 1e-12);
  EXPECT_DOUBLE_EQ(sixM.properTimeRate, sixM.progradeOrbitProperTimeRate);

  const game::BandView &ergo = view.bands.at(0);
  EXPECT_DOUBLE_EQ(ergo.progradeOrbitProperTimeRate, 0.0);
  EXPECT_DOUBLE_EQ(ergo.retrogradeOrbitProperTimeRate, 0.0);
  EXPECT_GT(ergo.hoverProperTimeRate, 0.0);
  EXPECT_DOUBLE_EQ(ergo.properTimeRate, ergo.hoverProperTimeRate);
}

// Falsifier: a deficit below what absolute cm radii resolve (1e-300, or an
// exactly extremal spin of 1) giving a field whose own ISCO is not a valid
// station, admits no stable prograde orbit there, or carries no clock -- the
// offset 1.6e-100 rounding away in 1 + x -- or a floor at which the horizon,
// marginally bound radius, and ISCO fail to sit strictly in that order.
TEST(KerrTimeField, SubResolutionDeficitsRaiseToTheFloor) {
  const double floorDeficit = game::KerrTimeField::K_MIN_SPIN_DEFICIT;
  for (const game::KerrTimeField &field :
       {game::KerrTimeField(K_M87_MASS_G, game::SpinDeficit{.epsilon = 1e-300}),
        game::KerrTimeField(K_M87_MASS_G, 1.0)}) {
    EXPECT_DOUBLE_EQ(field.spinDeficit(), floorDeficit);
    const game::Observer prograde = game::Observer::CircularOrbitPrograde;
    const double iscoCm = field.iscoRadiusCm(prograde);
    EXPECT_TRUE(field.isValidStationRadius(iscoCm));
    EXPECT_TRUE(field.admitsStableOrbit(iscoCm, prograde));
    EXPECT_GT(field.properTimeRate(iscoCm, prograde), 0.0);
    EXPECT_LT(field.outerHorizonCm(), field.marginallyBoundRadiusCm(prograde));
    EXPECT_LT(field.marginallyBoundRadiusCm(prograde), iscoCm);
  }
}

// Falsifier: the field's own published horizon radius accepted as a station
// (at spin 0.99 the cm -> offset round trip lands above the horizon offset),
// or the first representable radius the field does accept carrying a zero
// lapse -- for spins from 0.5 to the canon deficit.
TEST(KerrTimeField, HorizonRadiusIsNeverAStation) {
  const std::array<game::KerrTimeField, 5> fields = {
      game::KerrTimeField(K_M87_MASS_G, 0.5), game::KerrTimeField(K_M87_MASS_G, 0.9),
      game::KerrTimeField(K_M87_MASS_G, 0.99), game::KerrTimeField(K_M87_MASS_G, 0.998),
      game::KerrTimeField(K_M87_MASS_G, game::SpinDeficit{.epsilon = 1.33e-14})};
  for (const game::KerrTimeField &field : fields) {
    const double horizonCm = field.outerHorizonCm();
    EXPECT_FALSE(field.isValidStationRadius(horizonCm)) << "spin " << field.spinDimensionless();
    double radiusCm = horizonCm;
    for (int step = 0; step < 64 && !field.isValidStationRadius(radiusCm); ++step) {
      radiusCm = std::nextafter(radiusCm, 2.0 * radiusCm);
    }
    ASSERT_TRUE(field.isValidStationRadius(radiusCm));
    EXPECT_GT(field.properTimeRate(radiusCm, game::Observer::Hovering), 0.0);
  }
}

// Falsifier: the field's own published marginally bound radius admitted as an
// orbit of that sense (at spin 0.99 the cm -> offset round trip lands a few
// ulp above r_mb, admitting an E = 1 orbit the API defines as unbound), or
// the first radius the field does admit carrying no orbital clock.
TEST(KerrTimeField, MarginallyBoundRadiusIsNeverAnOrbit) {
  for (const double spin : {0.5, 0.9, 0.99, 0.998}) {
    const game::KerrTimeField field(K_M87_MASS_G, spin);
    for (const game::Observer orbit :
         {game::Observer::CircularOrbitPrograde, game::Observer::CircularOrbitRetrograde}) {
      const double boundaryCm = field.marginallyBoundRadiusCm(orbit);
      EXPECT_FALSE(field.admitsObserver(boundaryCm, orbit)) << "spin " << spin;
      double radiusCm = boundaryCm;
      for (int step = 0; step < 64 && !field.admitsObserver(radiusCm, orbit); ++step) {
        radiusCm = std::nextafter(radiusCm, 2.0 * radiusCm);
      }
      ASSERT_TRUE(field.admitsObserver(radiusCm, orbit));
      EXPECT_GT(field.properTimeRate(radiusCm, orbit), 0.0);
    }
  }
}
