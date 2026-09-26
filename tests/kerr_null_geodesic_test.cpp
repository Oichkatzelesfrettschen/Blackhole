/**
 * @file kerr_null_geodesic_test.cpp
 * @brief Kerr null geodesics against analytic oracles.
 *
 * Carter consistency: the constants built from a local direction reproduce
 * the initial radial and polar velocities through R(r) and Theta(theta).
 * Capture edges: equatorial rays at 1.001 and 0.999 of Bardeen's critical
 * impact parameter escape and fall in, respectively; a stepper that stalls at
 * radial turning points fails the escape half. Ferrari: the analytic quartic
 * solver recovers known roots and the double root on the critical curve.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <cmath>
#include <complex>
#include <numbers>
#include <random>
#include <string>
#include <vector>

#include "physics/analytic_kerr_geodesic.h"
#include "physics/constants.h"
#include "physics/kerr.h"

namespace {

// Mass whose geometric length G M / c^2 is 1 cm, so r and a read in units of M.
const double K_UNIT_MASS = physics::C2 / physics::G;

// Equatorial critical impact parameter b = L/E (Bardeen 1973, M = 1):
// b(r) = -(r^3 - 3 r^2 + a^2 r + a^2) / (a (r - 1)) at the circular photon
// orbit r = 2 {1 + cos[(2/3) arccos(-+a)]}; prograde takes the minus sign.
double equatorialCriticalImpact(double a, bool prograde) {
  const double rPh =
      2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(prograde ? -a : a)));
  const double r2 = rPh * rPh;
  const double bAbs = std::abs(-((r2 * rPh) - (3.0 * r2) + (a * a * rPh) + (a * a)) /
                               (a * (rPh - 1.0)));
  return prograde ? bAbs : -bAbs;
}

enum class Fate { Captured, Escaped, Undecided };

// Integrates an inbound equatorial photon from r0 with the production stepper
// and a Mino step scaled so each step moves r by about 0.2% far out.
Fate traceEquatorial(double a, double b, double r0) {
  const physics::KerrGeodesicConsts c = physics::kerrEquatorialConsts(b, 1.0);
  physics::KerrGeodesicState s = physics::kerrEquatorialState(r0, 0.0, -1.0);
  s = physics::kerrInitMinoVelocities(s, K_UNIT_MASS, a, c);
  const double rPlus = 1.0 + std::sqrt(1.0 - (a * a));
  for (int step = 0; step < 2'000'000; ++step) {
    if (s.r <= rPlus * 1.001) {
      return Fate::Captured;
    }
    if (s.r > 2.0 * r0 && s.vr > 0.0) {
      return Fate::Escaped;
    }
    const double dlam = 2e-3 / (1.0 + (s.r * s.r));
    s = physics::kerrStepMino(s, K_UNIT_MASS, a, c, dlam);
  }
  return Fate::Undecided;
}

TEST(KerrNullGeodesic, CarterConstantsReproduceInitialVelocities) {
  // A fixed seed makes the 2000-sample Carter sweep reproducible.
  // NOLINTNEXTLINE(cert-msc32-c,cert-msc51-cpp)
  std::mt19937_64 rng(20260925);
  std::uniform_real_distribution<double> radius(2.5, 60.0);
  std::uniform_real_distribution<double> polar(0.15, std::numbers::pi - 0.15);
  std::uniform_real_distribution<double> unit(-1.0, 1.0);
  std::uniform_real_distribution<double> spin(-0.99, 0.99);

  for (int sample = 0; sample < 2000; ++sample) {
    const double a = spin(rng);
    const double r = radius(rng);
    const double theta = polar(rng);
    const physics::KerrNullGeodesic g = physics::kerrNullGeodesicFromBL(
        r, theta, 0.0, unit(rng), unit(rng) / r, unit(rng) / (r * std::sin(theta)),
        K_UNIT_MASS, a);
    const physics::KerrPotentials p =
        physics::kerrPotentials(r, theta, K_UNIT_MASS, a, g.consts);
    const double scaleR = std::max(g.state.vr * g.state.vr, r * r * r * r);
    const double scaleTheta = std::max(g.state.vtheta * g.state.vtheta, r * r);
    EXPECT_NEAR(p.rPot, g.state.vr * g.state.vr, 1e-10 * scaleR)
        << "a=" << a << " r=" << r << " theta=" << theta;
    EXPECT_NEAR(p.thetaPot, g.state.vtheta * g.state.vtheta, 1e-10 * scaleTheta)
        << "a=" << a << " r=" << r << " theta=" << theta;
  }
}

TEST(KerrNullGeodesic, AxialStartHasFiniteConstants) {
  // On the spin axis lz = 0 and the lz^2 cot^2 term must vanish rather than
  // evaluate 0 * cos^2 / 0.
  const physics::KerrNullGeodesic g =
      physics::kerrNullGeodesicFromBL(12.0, 0.0, 0.0, -0.8, 0.05, 0.0, K_UNIT_MASS, 0.9);
  EXPECT_TRUE(std::isfinite(g.consts.q));
  const physics::KerrPotentials p =
      physics::kerrPotentials(12.0, 1e-9, K_UNIT_MASS, 0.9, g.consts);
  EXPECT_NEAR(p.rPot, g.state.vr * g.state.vr, 1e-8 * g.state.vr * g.state.vr);
}

TEST(KerrNullGeodesic, AxialStartStepsLikeEquatorialTwinAtZeroSpin) {
  // A transverse ray from the axis (theta = 0, lz = 0) and its equatorial
  // twin (theta = pi/2, all angular momentum in lz) are one Schwarzschild
  // orbit in two planes: r agrees and the polar angle swept from the axis
  // equals the azimuth swept from x. The polar force at theta = 0 carries
  // lz^2 cos / sin^3, which reads 0 / 0 unless lz = 0 drops the term.
  const double r0 = 30.0;
  const double alpha = 0.4;
  const physics::KerrNullGeodesic axial = physics::kerrNullGeodesicFromBL(
      r0, 0.0, 0.0, -std::cos(alpha), std::sin(alpha) / r0, 0.0, K_UNIT_MASS, 0.0);
  const physics::KerrNullGeodesic equatorial = physics::kerrNullGeodesicFromBL(
      r0, 0.5 * std::numbers::pi, 0.0, -std::cos(alpha), 0.0, std::sin(alpha) / r0, K_UNIT_MASS,
      0.0);
  physics::KerrGeodesicState s = axial.state;
  physics::KerrGeodesicState e = equatorial.state;
  for (int step = 0; step < 20'000; ++step) {
    const double dlam = 2e-3 / (1.0 + (s.r * s.r));
    s = physics::kerrStepMino(s, K_UNIT_MASS, 0.0, axial.consts, dlam);
    e = physics::kerrStepMino(e, K_UNIT_MASS, 0.0, equatorial.consts, dlam);
  }
  ASSERT_TRUE(std::isfinite(s.r) && std::isfinite(s.theta) && std::isfinite(s.phi));
  EXPECT_NEAR(s.r, e.r, 1e-9 * e.r);
  EXPECT_NEAR(s.theta, e.phi, 1e-9);
  EXPECT_NEAR(s.phi, 0.0, 1e-12);
  EXPECT_GT(s.theta, 0.1);
}

TEST(KerrNullGeodesic, ErgoregionStartPrefersPositiveEnergyRoot) {
  // Inside the ergoregion (a = 0.9, r = 1.6, equator) d/dt is spacelike and a
  // coordinate direction has two future-directed null completions. Using
  // directions built in the zero-angular-momentum frame, the initializer
  // must return the E > 0 completion, on shell (R(r0) = vr^2).
  const double a = 0.9;
  const double r = 1.6;
  const double sigma = r * r;
  const double delta = (r * r) - (2.0 * r) + (a * a);
  const double bigA = ((r * r) + (a * a)) * ((r * r) + (a * a)) - (a * a * delta);
  const double alpha = std::sqrt(sigma * delta / bigA);
  const double omega = 2.0 * a * r / bigA;
  const double varpi = std::sqrt(bigA / sigma);
  for (int k = 0; k < 16; ++k) {
    const double psi = 2.0 * std::numbers::pi * (static_cast<double>(k) + 0.5) / 16.0;
    const double kr = std::cos(psi) * std::sqrt(delta / sigma);
    const double kphi = (omega / alpha) + (std::sin(psi) / varpi);
    const physics::KerrNullGeodesic g = physics::kerrNullGeodesicFromBL(
        r, 0.5 * std::numbers::pi, 0.0, kr, 0.0, kphi, K_UNIT_MASS, a);
    ASSERT_GT(g.state.r, 0.0) << "psi=" << psi;
    const physics::KerrPotentials p =
        physics::kerrPotentials(r, 0.5 * std::numbers::pi, K_UNIT_MASS, a, g.consts);
    EXPECT_NEAR(p.rPot, g.state.vr * g.state.vr, 1e-9 * std::max(1.0, p.rPot)) << "psi=" << psi;
  }
}

// Null direction k = (1/alpha, kr, 0, kphi) of angle psi in the equatorial
// zero-angular-momentum frame at radius r (M = 1).
struct ZamoRay {
  double kt;
  double kr;
  double kphi;
};

ZamoRay zamoEquatorialRay(double r, double a, double psi) {
  const double sigma = r * r;
  const double delta = (r * r) - (2.0 * r) + (a * a);
  const double bigA = (((r * r) + (a * a)) * ((r * r) + (a * a))) - (a * a * delta);
  const double alpha = std::sqrt(sigma * delta / bigA);
  const double omega = 2.0 * a * r / bigA;
  const double varpi = std::sqrt(bigA / sigma);
  return {.kt = 1.0 / alpha,
          .kr = std::cos(psi) * std::sqrt(delta / sigma),
          .kphi = (omega / alpha) + (std::sin(psi) / varpi)};
}

// Returns whether the frame vector has E > 0 and was checked.
bool expectStationaryLimitStart(double r, double a, double psi) {
  const ZamoRay k = zamoEquatorialRay(r, a, psi);
  const physics::KerrNullGeodesic g = physics::kerrNullGeodesicFromBL(
      r, 0.5 * std::numbers::pi, 0.0, k.kr, 0.0, k.kphi, K_UNIT_MASS, a);
  const std::string where = "r=" + std::to_string(r) + " psi=" + std::to_string(psi);
  // Equatorial Boyer-Lindquist metric (M = 1): the ZAMO vector's own E and
  // Lz. Where E > 0 it is the root the initializer must return.
  const double f = 2.0 / r;
  const double gtt = -(1.0 - f);
  const double gtphi = -f * a;
  const double gphph = (r * r) + (a * a) + (f * a * a);
  const double energy = -((gtt * k.kt) + (gtphi * k.kphi));
  const double lz = (gtphi * k.kt) + (gphph * k.kphi);
  if (energy <= 0.0) {
    return false;
  }
  EXPECT_GT(g.state.r, 0.0) << where;
  EXPECT_TRUE(std::isfinite(g.consts.lz) && std::isfinite(g.consts.q) &&
              std::isfinite(g.state.vr))
      << where;
  EXPECT_NEAR(g.consts.lz, lz / energy, 1e-9 * std::max(1.0, std::abs(lz / energy))) << where;
  const physics::KerrPotentials p =
      physics::kerrPotentials(r, 0.5 * std::numbers::pi, K_UNIT_MASS, a, g.consts);
  EXPECT_NEAR(p.rPot, g.state.vr * g.state.vr, 1e-9 * std::max(1.0, p.rPot)) << where;
  return true;
}

TEST(KerrNullGeodesic, StationaryLimitStartIsOnShell) {
  // On the equatorial stationary limit r = 2M (a = 0.6) g_tt = 0 and the null
  // condition is linear in k^t; a quadratic-formula root divides by g_tt
  // there. Zero-angular-momentum-frame directions at r = 2M and 1e-6 and
  // 1e-3 to either side must start with the E > 0 root on shell and with
  // the constants of the frame vector.
  const double a = 0.6;
  for (const double r : {2.0 * (1.0 - 1e-3), 2.0 * (1.0 - 1e-6), 2.0, 2.0 * (1.0 + 1e-6),
                         2.0 * (1.0 + 1e-3)}) {
    int checked = 0;
    for (int k = 0; k < 16; ++k) {
      const double psi = 2.0 * std::numbers::pi * (static_cast<double>(k) + 0.5) / 16.0;
      checked += expectStationaryLimitStart(r, a, psi) ? 1 : 0;
    }
    EXPECT_GE(checked, 12) << "r=" << r;
  }
}

TEST(KerrNullGeodesic, StationaryLimitCounterRotatingDirectionIsRejected) {
  // At g_tt = 0 a coordinate direction with g_tphi k^phi > 0 has no finite
  // future-directed null completion (its root runs to infinity): the
  // initializer marks it captured (r = 0) with finite constants instead of
  // returning Inf or NaN.
  const physics::KerrNullGeodesic g = physics::kerrNullGeodesicFromBL(
      2.0, 0.5 * std::numbers::pi, 0.0, 0.3, 0.0, -0.2, K_UNIT_MASS, 0.6);
  EXPECT_EQ(g.state.r, 0.0);
  EXPECT_TRUE(std::isfinite(g.consts.lz) && std::isfinite(g.consts.q));
}

TEST(KerrNullGeodesic, EquatorialRayStaysInEquatorialPlane) {
  // q = 0 at theta = pi/2 gives Theta = 0 and Theta' = 0 in Carter's form;
  // an lz^2 / sin^2 polar potential would read -lz^2 there instead.
  const double a = 0.9;
  const physics::KerrGeodesicConsts c = physics::kerrEquatorialConsts(4.0, 1.0);
  const physics::KerrPotentials p =
      physics::kerrPotentials(20.0, 0.5 * std::numbers::pi, K_UNIT_MASS, a, c);
  EXPECT_NEAR(p.thetaPot, 0.0, 1e-12);
  EXPECT_NEAR(p.dThetadtheta, 0.0, 1e-12);
}

TEST(KerrNullGeodesic, EquatorialCaptureEdgesMatchBardeen) {
  for (const double a : {0.5, 0.9, 0.99}) {
    for (const bool prograde : {true, false}) {
      const double bc = equatorialCriticalImpact(a, prograde);
      EXPECT_EQ(traceEquatorial(a, 1.001 * bc, 60.0), Fate::Escaped)
          << "a=" << a << " prograde=" << prograde << " b_c=" << bc;
      EXPECT_EQ(traceEquatorial(a, 0.999 * bc, 60.0), Fate::Captured)
          << "a=" << a << " prograde=" << prograde << " b_c=" << bc;
    }
  }
}

std::vector<double> sortedRealRoots(const physics::RadialRoots &roots) {
  std::vector<double> real;
  for (const auto &root : roots.roots) {
    if (std::abs(root.imag()) < 1e-9) {
      real.push_back(root.real());
    }
  }
  std::sort(real.begin(), real.end());
  return real;
}

TEST(KerrNullGeodesic, FerrariRecoversKnownRoots) {
  // (r^2 - 1)(r^2 - 4): c2 = -5, c1 = 0, c0 = 4.
  physics::QuarticCoeffs even{};
  even.c2 = -5.0;
  even.c1 = 0.0;
  even.c0 = 4.0;
  const auto evenRoots = sortedRealRoots(physics::findRadialRoots(even));
  ASSERT_EQ(evenRoots.size(), 4U);
  EXPECT_NEAR(evenRoots[0], -2.0, 1e-12);
  EXPECT_NEAR(evenRoots[1], -1.0, 1e-12);
  EXPECT_NEAR(evenRoots[2], 1.0, 1e-12);
  EXPECT_NEAR(evenRoots[3], 2.0, 1e-12);

  // (r - 1)(r - 2)(r - 3)(r + 6): c2 = -25, c1 = 60, c0 = -36.
  physics::QuarticCoeffs mixed{};
  mixed.c2 = -25.0;
  mixed.c1 = 60.0;
  mixed.c0 = -36.0;
  const auto mixedRoots = sortedRealRoots(physics::findRadialRoots(mixed));
  ASSERT_EQ(mixedRoots.size(), 4U);
  EXPECT_NEAR(mixedRoots[0], -6.0, 1e-10);
  EXPECT_NEAR(mixedRoots[1], 1.0, 1e-10);
  EXPECT_NEAR(mixedRoots[2], 2.0, 1e-10);
  EXPECT_NEAR(mixedRoots[3], 3.0, 1e-10);
}

TEST(KerrNullGeodesic, FerrariSolvesBiquadraticsWithZeroAlpha) {
  // With c1 = 0 and c0 < 0 the largest resolvent root is y1 = c2, so
  // alpha^2 = y1 - c2 is zero up to rounding and the quartic is a quadratic
  // in r^2. (r^2 - 1)(r^2 + 2) and (r^2 - 4)(r^2 + 1) each have one real
  // pair and one imaginary pair; every returned root must satisfy the
  // quartic and the motion is a scatter (two real roots).
  struct Case {
    double c2;
    double c0;
    double realRoot;
  };
  for (const Case &k : {Case{.c2 = 1.0, .c0 = -2.0, .realRoot = 1.0},
                        Case{.c2 = -3.0, .c0 = -4.0, .realRoot = 2.0}}) {
    physics::QuarticCoeffs coeffs{};
    coeffs.c2 = k.c2;
    coeffs.c1 = 0.0;
    coeffs.c0 = k.c0;
    const physics::RadialRoots roots = physics::findRadialRoots(coeffs);
    const auto real = sortedRealRoots(roots);
    ASSERT_EQ(real.size(), 2U) << "c2=" << k.c2 << " c0=" << k.c0;
    EXPECT_NEAR(real.front(), -k.realRoot, 1e-12) << "c2=" << k.c2;
    EXPECT_NEAR(real.back(), k.realRoot, 1e-12) << "c2=" << k.c2;
    EXPECT_EQ(roots.nReal, 2) << "c2=" << k.c2;
    EXPECT_EQ(roots.type, physics::RadialMotionType::Scatter) << "c2=" << k.c2;
    for (const std::complex<double> &r : roots.roots) {
      const std::complex<double> r2 = r * r;
      EXPECT_LT(std::abs((r2 * r2) + (k.c2 * r2) + k.c0), 1e-10) << "c2=" << k.c2 << " r=" << r;
    }
  }
}

TEST(KerrNullGeodesic, FerrariFindsDoubleRootOnCriticalCurve) {
  const double a = 0.9;
  const double rMin = physics::progradePhotonOrbit(a);
  const double rMax = physics::retrogradePhotonOrbit(a);
  for (const double frac : {0.1, 0.5, 0.9}) {
    const double rPh = rMin + (frac * (rMax - rMin));
    const auto ip = physics::criticalImpactParams(rPh, a);
    const auto coeffs = physics::radialQuarticCoeffs(a, ip.xi, ip.eta);
    const auto roots = sortedRealRoots(physics::findRadialRoots(coeffs));
    ASSERT_GE(roots.size(), 2U) << "rPh=" << rPh;
    const auto nearPh = std::count_if(roots.begin(), roots.end(), [rPh](double root) {
      return std::abs(root - rPh) < 1e-5;
    });
    EXPECT_EQ(nearPh, 2) << "rPh=" << rPh;
  }
}

} // namespace
