/**
 * @file tests/page_thorne_test.cpp
 * @brief Page-Thorne thin-disk flux (page_thorne.h) against direct quadrature.
 *
 * The closed form must equal the Page & Thorne (1974) integral
 *   F = -(Mdot / 4 pi r) Omega_,r / (E - Omega L)^2
 *       * integral_{r_isco}^{r} (E - Omega L) L_,r dr
 * evaluated here by composite Simpson quadrature in x = sqrt(r) with
 * analytic derivatives. The peak radii, efficiencies and 1/u^t values are the
 * 30-digit outputs of scripts/gen_page_thorne_reference.py.
 */

#include <array>
#include <cmath>
#include <numbers>

#include <gtest/gtest.h>

#include "constants.h"
#include "page_thorne.h"
#include "thin_disk.h"

namespace {

/** @brief (E - Omega L) dL/dx of the circular orbit at x = sqrt(r), M = 1. */
double integrandInX(double x, double a) {
  double const q = (x * x * x) - (3.0 * x) + (2.0 * a);
  double const sq = std::sqrt(q);
  double const num = (x * x * x * x) - (2.0 * a * x) + (a * a);
  double const den = x * std::sqrt(x) * sq;
  double const dNum = (4.0 * x * x * x) - (2.0 * a);
  double const dDen =
      (1.5 * std::sqrt(x) * sq) + (x * std::sqrt(x) * ((3.0 * x * x) - 3.0) / (2.0 * sq));
  double const dL = ((dNum * den) - (num * dDen)) / (den * den);
  physics::KerrCircularOrbit const orbit = physics::kerrCircularOrbit(x * x, a);
  return (orbit.energy - (orbit.omega * orbit.angularMomentum)) * dL;
}

/** @brief Page-Thorne flux for Mdot = 1 by quadrature of its defining integral. */
double quadratureFlux(double r, double a) {
  double const x0 = std::sqrt(physics::pageThorneIscoRadius(a));
  double const x = std::sqrt(r);
  constexpr int kPanels = 4000;
  double const h = (x - x0) / kPanels;
  double sum = integrandInX(x0, a) + integrandInX(x, a);
  for (int i = 1; i < kPanels; ++i) {
    double const weight = (i % 2 == 1) ? 4.0 : 2.0;
    sum += weight * integrandInX(x0 + (i * h), a);
  }
  double const integral = sum * h / 3.0;

  physics::KerrCircularOrbit const orbit = physics::kerrCircularOrbit(r, a);
  double const dOmegaDr = -1.5 * x / (((x * x * x) + a) * ((x * x * x) + a));
  double const eMinusOmegaL = orbit.energy - (orbit.omega * orbit.angularMomentum);
  return -(1.0 / (4.0 * std::numbers::pi * r)) * dOmegaDr / (eMinusOmegaL * eMinusOmegaL) *
         integral;
}

double closedFormFlux(double r, double a) {
  return 3.0 / (8.0 * std::numbers::pi) * physics::pageThorneFluxShape(r, a);
}

} // namespace

TEST(PageThorne, ClosedFormMatchesQuadrature) {
  constexpr std::array<double, 5> kSpins = {0.0, 0.5, 0.9, 0.998, -0.5};
  constexpr std::array<double, 5> kRatios = {1.1, 1.5, 3.0, 10.0, 40.0};
  for (double const a : kSpins) {
    double const rIsco = physics::pageThorneIscoRadius(a);
    for (double const ratio : kRatios) {
      double const r = ratio * rIsco;
      double const quad = quadratureFlux(r, a);
      double const closed = closedFormFlux(r, a);
      EXPECT_NEAR(closed / quad, 1.0, 1e-6) << "a = " << a << ", r = " << ratio << " r_isco";
    }
  }
}

TEST(PageThorne, ClosedFormMatchesMpmathReference) {
  // scripts/gen_page_thorne_reference.py, closed form at 1.5 r_isco, Mdot = 1.
  EXPECT_NEAR(closedFormFlux(1.5 * physics::pageThorneIscoRadius(0.0), 0.0) / 1.34631179132076e-5,
              1.0, 1e-12);
  EXPECT_NEAR(closedFormFlux(1.5 * physics::pageThorneIscoRadius(0.9), 0.9) / 0.000339008259230833,
              1.0, 1e-12);
  EXPECT_NEAR(
      closedFormFlux(1.5 * physics::pageThorneIscoRadius(0.998), 0.998) / 0.00408517368239317, 1.0,
      1e-11);
}

TEST(PageThorne, ContinuousPeakRadii) {
  struct Case {
    double a;
    double peakOverIsco;
  };
  constexpr std::array<Case, 4> kCases = {
      {{0.0, 1.592}, {0.5, 1.563}, {0.9, 1.483}, {0.998, 1.278}}};
  for (Case const &c : kCases) {
    double const ratio =
        physics::pageThorneFluxPeakRadius(c.a) / physics::pageThorneIscoRadius(c.a);
    EXPECT_NEAR(ratio, c.peakOverIsco, 0.002) << "a = " << c.a;
  }
  EXPECT_NEAR(physics::pageThorneFluxPeakRadius(0.0), 9.55, 0.005);
}

TEST(PageThorne, EfficiencyIsOneMinusIscoEnergy) {
  EXPECT_NEAR(physics::novikovThorneEfficiency(0.0), 1.0 - std::sqrt(8.0 / 9.0), 1e-12);
  EXPECT_NEAR(physics::novikovThorneEfficiency(0.5), 0.0821179933392243, 1e-10);
  EXPECT_NEAR(physics::novikovThorneEfficiency(0.9), 0.155752991994464, 1e-10);
  EXPECT_NEAR(physics::novikovThorneEfficiency(0.998), 0.320994165616199, 1e-10);
}

TEST(PageThorne, ZeroTorqueEdgeAndNewtonianLimit) {
  for (double const a : {0.0, 0.9, 0.998}) {
    double const rIsco = physics::pageThorneIscoRadius(a);
    EXPECT_EQ(physics::pageThorneFluxShape(rIsco, a), 0.0);
    EXPECT_EQ(physics::pageThorneFluxShape(0.9 * rIsco, a), 0.0);
    EXPECT_GT(physics::pageThorneFluxShape(1.01 * rIsco, a), 0.0);
    // f = r^3 S -> 1 from below; the deficit decays as r^{-1/2} (1.3% at
    // r = 1e5 M for a = 0.998).
    EXPECT_NEAR(physics::pageThorneRelativisticFactor(1e5, a), 1.0, 0.02);
    EXPECT_GT(physics::pageThorneRelativisticFactor(1e5, a),
              physics::pageThorneRelativisticFactor(1e4, a));
    EXPECT_LT(physics::pageThorneRelativisticFactor(1e5, a), 1.0);
  }
}

TEST(PageThorne, ThinDiskFluxUsesPageThorne) {
  // diskFlux = 3 G M Mdot / (8 pi r^3) f(r / r_g) for every spin.
  for (double const aStar : {0.0, 0.9}) {
    physics::DiskParams const disk = physics::kerrDisk(10.0, aStar, 0.1, true);
    double const rG = physics::G * disk.mass / physics::C2;
    double const r = 2.0 * disk.rIn;
    double const expected = 3.0 * physics::G * disk.mass * disk.mDot /
                            (8.0 * std::numbers::pi * r * r * r) *
                            physics::pageThorneRelativisticFactor(r / rG, aStar);
    EXPECT_NEAR(physics::diskFlux(r, disk) / expected, 1.0, 1e-12) << "a = " << aStar;
    // Mdot is 0.1 L_Edd / (eta c^2) at the Novikov-Thorne efficiency.
    double const lEdd = 1.26e38 * 10.0;
    EXPECT_NEAR(disk.mDot * physics::novikovThorneEfficiency(aStar) * physics::C2 / (0.1 * lEdd),
                1.0, 1e-12);
  }
}

namespace {

// At |aStar| = 1 the roots x1 and x2 coincide; every function evaluates at
// pageThorneSpin(aStar), |aStar| <= 0.9999, and so returns the finite values
// of that spin rather than inf (flux) or 1 (efficiency). sign selects the
// prograde (+1) or retrograde (-1) extremal disk.
void expectExtremalSpinClamped(double sign) {
  double const a = sign;
  double const aMax = sign * physics::K_PAGE_THORNE_MAX_SPIN;
  EXPECT_EQ(physics::pageThorneIscoRadius(a), physics::pageThorneIscoRadius(aMax));
  EXPECT_EQ(physics::novikovThorneEfficiency(a), physics::novikovThorneEfficiency(aMax));
  EXPECT_LT(physics::novikovThorneEfficiency(a), 0.45);
  double const peak = physics::pageThorneFluxPeak(a);
  EXPECT_TRUE(std::isfinite(peak)) << "a = " << a;
  EXPECT_GT(peak, 0.0) << "a = " << a;
  EXPECT_EQ(peak, physics::pageThorneFluxPeak(aMax));
  double const r = 2.0 * physics::pageThorneIscoRadius(a);
  EXPECT_EQ(physics::pageThorneFluxShape(r, a), physics::pageThorneFluxShape(r, aMax));

  physics::DiskParams const disk = physics::kerrDisk(10.0, 1.0, 0.1, sign > 0.0);
  double const rG = physics::G * disk.mass / physics::C2;
  EXPECT_NEAR(disk.rIn / rG, physics::pageThorneIscoRadius(aMax), 1e-9);
  EXPECT_TRUE(std::isfinite(disk.mDot));
  EXPECT_TRUE(std::isfinite(physics::diskFlux(2.0 * disk.rIn, disk)));
  EXPECT_GT(physics::diskFlux(2.0 * disk.rIn, disk), 0.0);
}

} // namespace

TEST(PageThorne, ExtremalSpinClampsToTheMaximumSpin) {
  expectExtremalSpinClamped(1.0);
  expectExtremalSpinClamped(-1.0);
}
