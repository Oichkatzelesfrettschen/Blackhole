/**
 * @file tests/kerr_orbit_convention_test.cpp
 * @brief One signed-spin convention for Kerr ISCO and photon-orbit radii.
 *
 * a > 0 rotates about +z and a < 0 about -z. "Prograde" names an equatorial
 * orbit with angular momentum along +z, so at a < 0 the prograde ISCO and the
 * prograde photon orbit both counter-rotate with the hole. The table checks
 * physics::kerrIscoRadius, physics::kerrPhotonOrbit*, verified::kerrIsco*,
 * verified::photonOrbit*, blackhole::physics::NovikovThorneDisk::iscoRadius, and
 * the Blender bridge's CUDA disk edge bridge::diskIscoOverM against
 * Bardeen-Press-Teukolsky (1972) closed-form values.
 */

#include <cmath>

#include <gtest/gtest.h>

#include "blender_bridge/bridge_disk_isco.h"
#include "physics/constants.h"
#include "physics/kerr.h"
#include "physics/novikov_thorne.h"
#include "physics/verified/kerr.hpp"

namespace {

struct Row {
  double aStar;
  double iscoProgradeOverM;  // angular momentum along +z
  double photonProgradeOverM;
};

// BPT 1972 closed forms at |a*| = 0.9 and 0.5 (mpmath, 15 digits); the
// co-rotating value applies where a* > 0, the counter-rotating value where a* < 0.
constexpr Row K_TABLE[] = {
    {-0.9, 8.71735227960649, 3.91026793910304},
    {-0.5, 7.55458471451236, 3.53208888623796},
    {0.0, 6.0, 3.0},
    {0.5, 4.23300252953083, 2.34729635533386},
    {0.9, 2.32088304176189, 1.55785462742338},
};

/** @brief Every ISCO and photon-orbit function agrees with one BPT row and its reflection. */
void expectSignedSpinRow(const Row &row) {
  const double mass = physics::M_SUN;
  const double mGeom = physics::G * mass / physics::C2;
  const double a = row.aStar * mGeom;
  EXPECT_NEAR(physics::kerrIscoRadius(mass, a, true) / mGeom, row.iscoProgradeOverM, 1.0e-9)
      << "a*=" << row.aStar;
  EXPECT_NEAR(physics::kerrPhotonOrbitPrograde(mass, a) / mGeom, row.photonProgradeOverM, 1.0e-9)
      << "a*=" << row.aStar;
  EXPECT_NEAR(verified::kerrIscoPrograde(1.0, row.aStar), row.iscoProgradeOverM, 1.0e-12);
  EXPECT_NEAR(verified::photonOrbitPrograde(1.0, row.aStar), row.photonProgradeOverM, 1.0e-9);
  EXPECT_NEAR(blackhole::physics::NovikovThorneDisk::iscoRadius(row.aStar), row.iscoProgradeOverM,
              1.0e-12);

  // Both radii sit on the same side of their a = 0 values: co-rotation
  // pulls both inward, counter-rotation pushes both outward.
  const double iscoShift = row.iscoProgradeOverM - 6.0;
  const double photonShift = physics::kerrPhotonOrbitPrograde(mass, a) / mGeom - 3.0;
  EXPECT_GE(iscoShift * photonShift, 0.0) << "a*=" << row.aStar;

  // phi -> -phi reflection: retrograde at a equals prograde at -a.
  EXPECT_NEAR(physics::kerrIscoRadius(mass, a, false), physics::kerrIscoRadius(mass, -a, true),
              1.0e-9 * mGeom);
  EXPECT_NEAR(physics::kerrPhotonOrbitRetrograde(mass, a),
              physics::kerrPhotonOrbitPrograde(mass, -a), 1.0e-9 * mGeom);
  EXPECT_DOUBLE_EQ(verified::kerrIscoRetrograde(1.0, row.aStar),
                   verified::kerrIscoPrograde(1.0, -row.aStar));
}

} // namespace

TEST(KerrOrbitConvention, SignedSpinTable) {
  for (const Row &row : K_TABLE) {
    expectSignedSpinRow(row);
  }
}

/**
 * @brief The bridge's CUDA disk edge follows the same signed convention.
 *
 * bhbKerrIsco(a*, 1) returns physics::kerrIscoRadius(M, a* M, true) / M, and
 * the CUDA renderer places the +z disk's inner edge at bridge::diskIscoOverM.
 * The float helper matches the double table to 1e-5 M, far below the 6.4 M
 * that separates the two branches at |a*| = 0.9.
 */
TEST(KerrOrbitConvention, BridgeDiskIscoMatchesSignedIsco) {
  const double mass = physics::M_SUN;
  const double mGeom = physics::G * mass / physics::C2;
  for (const Row &row : K_TABLE) {
    const auto bridgeIsco =
        static_cast<double>(bridge::diskIscoOverM(static_cast<float>(row.aStar)));
    EXPECT_NEAR(bridgeIsco, row.iscoProgradeOverM, 1.0e-5) << "a*=" << row.aStar;
    EXPECT_NEAR(bridgeIsco, physics::kerrIscoRadius(mass, row.aStar * mGeom, true) / mGeom, 1.0e-5)
        << "a*=" << row.aStar;
  }
  // Extremal spins: co-rotating edge at the horizon, counter-rotating at 9 M.
  EXPECT_NEAR(static_cast<double>(bridge::diskIscoOverM(1.0f)), 1.0, 1.0e-5);
  EXPECT_NEAR(static_cast<double>(bridge::diskIscoOverM(-1.0f)), 9.0, 1.0e-5);
}
