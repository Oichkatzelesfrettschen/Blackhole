/**
 * @file tests/kerr_clock_rates_test.cpp
 * @brief Kerr clock rates (static, ZAMO, circular orbit) and the redshift built on them.
 *
 * Reference constants come from scripts/gen_kn_kds_reference.py: mpmath
 * evaluates sqrt(Sigma Delta / A), sqrt(-g_tt), and 1/u^t with u^t from the
 * metric's circularity condition, independent of the Bardeen-Press-Teukolsky
 * closed form in src/physics/kerr.h.
 */

#include <cmath>
#include <limits>
#include <optional>
#include <vector>

#include <gtest/gtest.h>

#include "physics/batch.h"
#include "physics/constants.h"
#include "physics/kerr.h"

namespace {

constexpr double K_HALF_PI = 0.5 * physics::PI;

struct Hole {
  double mass;
  double mGeom;
};

Hole solarHole() {
  const double mass = physics::M_SUN;
  return {mass, physics::G * mass / physics::C2};
}

// A missing clock rate reads as NaN, which fails every EXPECT_NEAR against it.
double orNan(std::optional<double> rate) {
  return rate.value_or(std::numeric_limits<double>::quiet_NaN());
}

} // namespace

/** @brief r = 6M, a = 0.9M: ZAMO 0.818, static 0.8165, prograde 0.743, retrograde 0.655. */
TEST(KerrClockRates, EquatorialTableAtSixM) {
  const Hole h = solarHole();
  const double r = 6.0 * h.mGeom;
  const double a = 0.9 * h.mGeom;
  EXPECT_NEAR(physics::kerrZamoLapse(r, K_HALF_PI, h.mass, a), 0.81798157138940855, 1.0e-12);
  const std::optional<double> staticRate = physics::kerrStaticTimeDilation(r, K_HALF_PI, h.mass, a);
  ASSERT_TRUE(staticRate.has_value());
  EXPECT_NEAR(orNan(staticRate), 0.81649658092772603, 1.0e-12);
  const std::optional<double> pro = physics::kerrCircularOrbitTimeDilation(r, h.mass, a, true);
  const std::optional<double> retro = physics::kerrCircularOrbitTimeDilation(r, h.mass, a, false);
  ASSERT_TRUE(pro.has_value());
  ASSERT_TRUE(retro.has_value());
  EXPECT_NEAR(orNan(pro), 0.74344405871481959, 1.0e-12);
  EXPECT_NEAR(orNan(retro), 0.65451153007973629, 1.0e-12);
}

/** @brief Inside the ergoregion (a = 0.9, r = 1.6M, 1.8M) only the ZAMO and prograde clocks exist. */
TEST(KerrClockRates, ErgoregionHasNoStaticObserver) {
  const Hole h = solarHole();
  const double a = 0.9 * h.mGeom;
  struct Row {
    double rOverM;
    double zamo;
    double prograde;
  };
  const Row rows[] = {{1.6, 0.19695340720394075, 0.083035359502440696},
                      {1.8, 0.30151134457776362, 0.20435686902226381},
                      {3.0, 0.60672559038579006, 0.50167374905743816}};
  for (const Row &row : rows) {
    const double r = row.rOverM * h.mGeom;
    EXPECT_NEAR(physics::kerrZamoLapse(r, K_HALF_PI, h.mass, a), row.zamo, 1.0e-12) << row.rOverM;
    const std::optional<double> pro = physics::kerrCircularOrbitTimeDilation(r, h.mass, a, true);
    ASSERT_TRUE(pro.has_value()) << row.rOverM;
    EXPECT_NEAR(orNan(pro), row.prograde, 1.0e-12) << row.rOverM;
    // Retrograde photon orbit at a = 0.9 is 3.91M: no retrograde circular orbit here.
    EXPECT_FALSE(physics::kerrCircularOrbitTimeDilation(r, h.mass, a, false).has_value());
  }
  EXPECT_FALSE(physics::kerrStaticTimeDilation(1.6 * h.mGeom, K_HALF_PI, h.mass, a).has_value());
  EXPECT_FALSE(physics::kerrStaticTimeDilation(1.8 * h.mGeom, K_HALF_PI, h.mass, a).has_value());
  EXPECT_NEAR(orNan(physics::kerrStaticTimeDilation(3.0 * h.mGeom, K_HALF_PI, h.mass, a)),
              0.57735026918962576, 1.0e-12);
}

/** @brief a = 0: ZAMO = static = sqrt(1 - 2M/r); circular orbit sqrt(1 - 3M/r) both ways. */
TEST(KerrClockRates, SchwarzschildLimit) {
  const Hole h = solarHole();
  for (double const x : {3.5, 6.0, 20.0}) {
    const double r = x * h.mGeom;
    const double staticRate = std::sqrt(1.0 - (2.0 / x));
    EXPECT_NEAR(physics::kerrZamoLapse(r, 0.7, h.mass, 0.0), staticRate, 1.0e-14);
    EXPECT_NEAR(orNan(physics::kerrStaticTimeDilation(r, 0.7, h.mass, 0.0)), staticRate, 1.0e-14);
    const double orbit = std::sqrt(1.0 - (3.0 / x));
    EXPECT_NEAR(orNan(physics::kerrCircularOrbitTimeDilation(r, h.mass, 0.0, true)), orbit,
                1.0e-14);
    EXPECT_NEAR(orNan(physics::kerrCircularOrbitTimeDilation(r, h.mass, 0.0, false)), orbit,
                1.0e-14);
  }
  EXPECT_NEAR(orNan(physics::kerrCircularOrbitTimeDilation(6.0 * h.mGeom, h.mass, 0.0, true)),
              0.70710678118654752, 1.0e-14);
}

/** @brief Signed spin: prograde at -a is retrograde at +a. */
TEST(KerrClockRates, SignedSpinReflection) {
  const Hole h = solarHole();
  const double r = 6.0 * h.mGeom;
  const double a = 0.9 * h.mGeom;
  EXPECT_DOUBLE_EQ(orNan(physics::kerrCircularOrbitTimeDilation(r, h.mass, -a, true)),
                   orNan(physics::kerrCircularOrbitTimeDilation(r, h.mass, a, false)));
}

/**
 * @brief kerrRedshift stays finite in the ergoregion and diverges only at the horizon.
 *
 * The batch maps the horizon's infinite redshift to the cap of 10.
 */
TEST(KerrClockRates, RedshiftThroughErgoregion) {
  const Hole h = solarHole();
  const double a = 0.9 * h.mGeom;
  const double r = 1.6 * h.mGeom;
  const double z = physics::kerrRedshift(r, K_HALF_PI, h.mass, a);
  EXPECT_NEAR(z, (1.0 / 0.19695340720394075) - 1.0, 1.0e-10);
  EXPECT_FALSE(physics::kerrStaticRedshift(r, K_HALF_PI, h.mass, a).has_value());
  const double rPlus = physics::kerrOuterHorizon(h.mass, a);
  EXPECT_TRUE(std::isinf(physics::kerrRedshift(rPlus, K_HALF_PI, h.mass, a)));
  EXPECT_EQ(physics::kerrZamoLapse(rPlus, K_HALF_PI, h.mass, a), 0.0);

  // a = 0: identical to the Schwarzschild static redshift.
  const double r10 = 10.0 * h.mGeom;
  EXPECT_NEAR(physics::kerrRedshift(r10, K_HALF_PI, h.mass, 0.0),
              (1.0 / std::sqrt(1.0 - 0.2)) - 1.0, 1.0e-14);

  std::vector<float> zBatch;
  physics::kerrRedshiftBatch({rPlus, r, 2.0 * rPlus}, K_HALF_PI, h.mass, a, zBatch);
  ASSERT_EQ(zBatch.size(), 3U);
  EXPECT_EQ(zBatch[0], 10.0F);
  EXPECT_NEAR(static_cast<double>(zBatch[1]), z, 1.0e-6);
  EXPECT_GT(zBatch[2], 0.0F);
}
