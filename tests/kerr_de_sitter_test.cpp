/**
 * @file tests/kerr_de_sitter_test.cpp
 * @brief Kerr-de Sitter Carter-form metric: limits, horizons, and field equations.
 *
 * Reference constants come from scripts/gen_kn_kds_reference.py (mpmath
 * polyroots of the Carter quartic Delta_r). The Einstein-Lambda check uses the
 * finite-difference Ricci oracle in tests/support/ricci_oracle.h, which shares
 * no code with src/physics/verified/kerr_de_sitter.hpp.
 */

#include <cmath>
#include <cstdio>
#include <numbers>

#include <gtest/gtest.h>

#include "physics/verified/kerr.hpp"
#include "physics/verified/kerr_de_sitter.hpp"
#include "support/ricci_oracle.h"

namespace {

using ricci_oracle::Mat4;
using ricci_oracle::Vec4;

constexpr double K_HALF_PI = std::numbers::pi / 2.0;

// Residual tolerance for R_mu_nu - Lambda g_mu_nu at |g| <= 20 (points below).
// KerrVacuumFloor measures the oracle floor on exact Kerr; this bound sits
// above that floor and far below the negative-control residuals.
constexpr double K_RICCI_TOL = 1.0e-6;

Mat4 kdsMetric(const Vec4 &x, double m, double a, double lambda) {
  const double r = x[1];
  const double theta = x[2];
  Mat4 g{};
  g[0][0] = verified::kdsGTt(r, theta, m, a, lambda);
  g[1][1] = verified::kdsGRr(r, theta, m, a, lambda);
  g[2][2] = verified::kdsGThth(r, theta, a, lambda);
  g[3][3] = verified::kdsGPhph(r, theta, m, a, lambda);
  g[0][3] = verified::kdsGTph(r, theta, m, a, lambda);
  g[3][0] = g[0][3];
  return g;
}

Mat4 kerrMetric(const Vec4 &x, double m, double a) {
  const double r = x[1];
  const double theta = x[2];
  Mat4 g{};
  g[0][0] = verified::kerrGTt(r, theta, m, a);
  g[1][1] = verified::kerrGRr(r, theta, m, a);
  g[2][2] = verified::kerrGThth(r, theta, a);
  g[3][3] = verified::kerrGPhph(r, theta, m, a);
  g[0][3] = verified::kerrGTph(r, theta, m, a);
  g[3][0] = g[0][3];
  return g;
}

/**
 * Non-Carter metric with a quadratic Delta = r^2 - 2Mr + a^2 - Lambda r^2 / 3,
 * g_tt = -(1 - 2Mr/Sigma + Lambda r^2 sin^2 / 3), and Kerr g_tph and g_thth is
 * not an Einstein space. The negative control: its Ricci residual shows the
 * tolerance discriminates.
 */
Mat4 legacyQuadraticKdsMetric(const Vec4 &x, double m, double a, double lambda) {
  const double r = x[1];
  const double theta = x[2];
  const double sigma = (r * r) + (a * a * std::cos(theta) * std::cos(theta));
  const double s2 = std::sin(theta) * std::sin(theta);
  const double delta = (r * r) - (2.0 * m * r) + (a * a) - (lambda * r * r / 3.0);
  Mat4 g{};
  g[0][0] = -(1.0 - (2.0 * m * r / sigma) + (lambda * r * r * s2 / 3.0));
  g[1][1] = sigma / delta;
  g[2][2] = sigma;
  g[3][3] = ((r * r) + (a * a) + (2.0 * m * r * a * a * s2 / sigma) - (lambda * r * r * r * r * s2 / 3.0)) * s2;
  g[0][3] = -2.0 * m * r * a * s2 / sigma;
  g[3][0] = g[0][3];
  return g;
}

double lambdaResidual(const Mat4 &ricciTensor, const Mat4 &g, double lambda) {
  return ricci_oracle::maxAbsDifference(ricciTensor, g, lambda);
}

/** @brief At a = 0 each component is Schwarzschild-de Sitter, f = 1 - 2M/r - Lambda r^2 / 3. */
void expectSchwarzschildDeSitter(double r, double theta, double m, double lambda) {
  const double f = 1.0 - (2.0 * m / r) - (lambda * r * r / 3.0);
  EXPECT_NEAR(verified::kdsGTt(r, theta, m, 0.0, lambda), -f, 1.0e-14);
  EXPECT_NEAR(verified::kdsGRr(r, theta, m, 0.0, lambda), 1.0 / f, 1.0e-12);
  EXPECT_NEAR(verified::kdsGThth(r, theta, 0.0, lambda), r * r, 1.0e-12);
  EXPECT_NEAR(verified::kdsGPhph(r, theta, m, 0.0, lambda),
              r * r * std::sin(theta) * std::sin(theta), 1.0e-12);
  EXPECT_DOUBLE_EQ(verified::kdsGTph(r, theta, m, 0.0, lambda), 0.0);
}

struct HorizonCase {
  double a;
  double lambda;
  double rMinus; // 0 at a = 0: the root is the singularity
  double rPlus;
  double rCosmo;
};

/** @brief r_-, r_+, r_c to 1e-12 relative (r_- exactly 0 at a = 0) and the ordering predicates. */
void expectHorizons(const HorizonCase &c) {
  const double rMinus = verified::kdsInnerHorizon(1.0, c.a, c.lambda);
  if (c.a == 0.0) {
    EXPECT_EQ(rMinus, 0.0) << "Lambda=" << c.lambda;
  } else {
    EXPECT_NEAR(rMinus, c.rMinus, 1.0e-12 * c.rMinus) << "a=" << c.a << " Lambda=" << c.lambda;
  }
  EXPECT_NEAR(verified::kdsEventHorizon(1.0, c.a, c.lambda), c.rPlus, 1.0e-12 * c.rPlus)
      << "a=" << c.a << " Lambda=" << c.lambda;
  EXPECT_NEAR(verified::kdsCosmologicalHorizon(1.0, c.a, c.lambda), c.rCosmo, 1.0e-12 * c.rCosmo)
      << "a=" << c.a << " Lambda=" << c.lambda;
  EXPECT_TRUE(verified::isPhysicalKdsBlackHole(1.0, c.a, c.lambda))
      << "a=" << c.a << " Lambda=" << c.lambda;
  EXPECT_TRUE(verified::verifyHorizonOrdering(1.0, c.a, c.lambda));
  EXPECT_TRUE(verified::isExteriorRegion(2.0 * c.rPlus, 1.0, c.a, c.lambda));
}

/** @brief Near the extremal spin r_- and r_+ both sit within 1e-7 of the double root. */
void expectMergedHorizons(double a, double lambda, double rDouble) {
  const double rMinus = verified::kdsInnerHorizon(1.0, a, lambda);
  const double rPlus = verified::kdsEventHorizon(1.0, a, lambda);
  // A double root moves by sqrt(|Delta_r(r_a)| / Delta_r''), ~2e-8 at one ulp of a.
  EXPECT_NEAR(rMinus, rDouble, 1.0e-7) << "a=" << a;
  EXPECT_NEAR(rPlus, rDouble, 1.0e-7) << "a=" << a;
  EXPECT_LE(rMinus, rPlus) << "a=" << a;
  EXPECT_TRUE(verified::isPhysicalKdsBlackHole(1.0, a, lambda)) << "a=" << a;
  if (verified::kdsDeltaLocalMinimum(1.0, a, lambda) == 0.0) {
    EXPECT_EQ(rMinus, rPlus) << "a=" << a;
  }
}

} // namespace

/** @brief a = 0 is Schwarzschild-de Sitter: g_tt = -(1 - 2M/r - Lambda r^2 / 3) = -1 / g_rr. */
TEST(KerrDeSitter, SchwarzschildDeSitterLimit) {
  constexpr double m = 1.0;
  for (double const lambda : {1.0e-4, 1.0e-2, 0.05}) {
    for (double const r : {3.0, 5.0, 10.0}) {
      for (double const theta : {0.4, std::numbers::pi / 3.0, K_HALF_PI}) {
        expectSchwarzschildDeSitter(r, theta, m, lambda);
      }
    }
  }
  // mpmath: r = 10, Lambda = 1e-2.
  EXPECT_NEAR(verified::kdsGTt(10.0, K_HALF_PI, m, 0.0, 1.0e-2), -0.46666666666666667, 1.0e-15);
  EXPECT_NEAR(verified::kdsGRr(10.0, K_HALF_PI, m, 0.0, 1.0e-2), 2.1428571428571429, 1.0e-14);
}

/** @brief Lambda = 0 reproduces every Kerr component. */
TEST(KerrDeSitter, KerrLimit) {
  constexpr double m = 1.0;
  for (double const a : {-0.7, 0.3, 0.9}) {
    for (double const theta : {0.5, std::numbers::pi / 3.0, K_HALF_PI}) {
      const Vec4 x{0.0, 4.0, theta, 0.0};
      const Mat4 gK = kerrMetric(x, m, a);
      const Mat4 gD = kdsMetric(x, m, a, 0.0);
      EXPECT_LT(ricci_oracle::maxAbsDifference(gK, gD, 1.0), 1.0e-13) << "a=" << a;
    }
    EXPECT_NEAR(verified::kdsEventHorizon(m, a, 0.0), m + std::sqrt(m * m - a * a), 1.0e-15);
    EXPECT_NEAR(verified::kdsInnerHorizon(m, a, 0.0), m - std::sqrt(m * m - a * a), 1.0e-15);
    EXPECT_TRUE(std::isinf(verified::kdsCosmologicalHorizon(m, a, 0.0)));
  }
}

/**
 * @brief Horizons against mpmath polyroots of Delta_r for Lambda M^2 from 1e-44 to 0.1.
 *
 * Bisection resolves each root to adjacent doubles; 1e-12 relative covers the
 * conditioning of Delta_r at the roots listed. Lambda M^2 = 1e-26 (M87*) to
 * 1e-44 (a ~10 solar-mass hole) is the astrophysical range, where the local
 * minimum of Delta_r sits at r ~ M and the cosmological root at sqrt(3 / Lambda).
 */
TEST(KerrDeSitter, HorizonsMatchQuarticRoots) {
  const HorizonCase cases[] = {
      {0.0, 1.0e-2, 0.0, 2.0277939461513023, 16.217354832407434},
      {0.0, 1.0e-4, 0.0, 2.000266773390257, 172.19628458904262},
      {0.9, 1.0e-2, 0.56274795742926431, 1.4591964724233871, 16.221118934330201},
      {0.9, 0.1, 0.55134885405674908, 1.7824862466846589, 3.9406926580723805},
      {0.5, 1.0e-10, 0.13397459621546879, 1.8660254040345312, 173204.08074822735},
      {0.0, 1.0e-26, 0.0, 2.0, 17320508075687.773},
      {0.5, 1.0e-26, 0.13397459621556135, 1.8660254037844386, 17320508075687.773},
      {0.999, 1.0e-26, 0.95528982218778369, 1.0447101778122163, 17320508075687.773},
      {0.0, 1.0e-34, 0.0, 2.0, 1.7320508075688773e+17},
      {0.5, 1.0e-34, 0.13397459621556135, 1.8660254037844386, 1.7320508075688773e+17},
      {0.999, 1.0e-34, 0.95528982218778369, 1.0447101778122163, 1.7320508075688773e+17},
      {0.0, 1.0e-44, 0.0, 2.0, 1.7320508075688773e+22},
      {0.5, 1.0e-44, 0.13397459621556135, 1.8660254037844386, 1.7320508075688773e+22},
      {0.999, 1.0e-44, 0.95528982218778369, 1.0447101778122163, 1.7320508075688773e+22},
  };
  for (const HorizonCase &c : cases) {
    expectHorizons(c);
  }
  // Beyond the Nariai bound (9 Lambda M^2 < 1 at a = 0) no black hole exists.
  EXPECT_TRUE(std::isnan(verified::kdsEventHorizon(1.0, 0.0, 0.2)));
  EXPECT_TRUE(std::isnan(verified::kdsCosmologicalHorizon(1.0, 0.0, 0.2)));
  EXPECT_FALSE(verified::isPhysicalKdsBlackHole(1.0, 0.0, 0.2));
  // Super-extremal spin has no event horizon.
  EXPECT_TRUE(std::isnan(verified::kdsEventHorizon(1.0, 1.2, 1.0e-3)));
}

/**
 * @brief The local minimum of Delta_r stays at r ~ M / (1 - Lambda a^2 / 3) as Lambda -> 0.
 *
 * dDelta_r/dr = 0 reads (1 - Lambda a^2 / 3) r - M = (2 Lambda / 3) r^3, so the
 * local minimum differs from M / b by O(Lambda M^3). Viete's r_a = A cos(phi -
 * 2 pi / 3) with A ~ sqrt(2 / Lambda) cancels to noise at Lambda M^2 = 1e-30.
 */
TEST(KerrDeSitter, StationaryRadiusSmallLambda) {
  for (double const lambda : {1.0e-26, 1.0e-30, 1.0e-34, 1.0e-44, 1.1e-52}) {
    for (double const a : {0.0, 0.5, 0.999}) {
      const double b = 1.0 - (lambda * a * a / 3.0);
      EXPECT_NEAR(verified::kdsDeltaStationaryRadius(1.0, a, lambda, false), 1.0 / b, 1.0e-15)
          << "a=" << a << " Lambda=" << lambda;
      EXPECT_NEAR(verified::kdsDeltaStationaryRadius(1.0, a, lambda, true),
                  std::sqrt(3.0 * b / (2.0 * lambda)), 1.0e-12 * std::sqrt(3.0 / (2.0 * lambda)));
    }
  }
}

/**
 * @brief At the extremal spin r_- and r_+ merge at the local minimum of Delta_r.
 *
 * mpmath (Delta_r = dDelta_r/dr = 0 at M = 1, Lambda = 1e-2) puts the extremal
 * spin at a = 1.0033903414560322118 and the double root at
 * r = 1.0102644922092494668. The nearest double below is sub-extremal; the
 * doubles above it leave Delta_r(r_a) within rounding of zero and read as
 * extremal, with r_- = r_+ = r_a. A spin 1e-9 larger is a naked singularity.
 */
TEST(KerrDeSitter, ExtremalSpinMergesHorizons) {
  constexpr double lambda = 1.0e-2;
  constexpr double rDouble = 1.0102644922092494668;
  double a = 1.0033903414560321;
  for (int ulp = 0; ulp <= 4; ++ulp) {
    expectMergedHorizons(a, lambda, rDouble);
    a = std::nextafter(a, 2.0);
  }
  EXPECT_EQ(verified::kdsDeltaLocalMinimum(1.0, std::nextafter(1.0033903414560321, 2.0), lambda),
            0.0);
  const double overSpun = 1.0033903414560321 * (1.0 + 1.0e-9);
  EXPECT_GT(verified::kdsDeltaLocalMinimum(1.0, overSpun, lambda), 0.0);
  EXPECT_TRUE(std::isnan(verified::kdsInnerHorizon(1.0, overSpun, lambda)));
  EXPECT_TRUE(std::isnan(verified::kdsEventHorizon(1.0, overSpun, lambda)));
  EXPECT_FALSE(verified::isPhysicalKdsBlackHole(1.0, overSpun, lambda));
}

/**
 * @brief A solar-mass hole under the observed cosmological constant, in meters.
 *
 * M = 1476.6 m (G M_sun / c^2) and Lambda = observedLambda() m^-2 give
 * Lambda M^2 ~ 2.4e-46; r_+ departs from the Kerr value by O(Lambda M^2),
 * far below double precision.
 */
TEST(KerrDeSitter, SolarMassObservedLambda) {
  constexpr double mMeters = 1476.6;
  const double lambda = verified::observedLambda();
  for (double const aStar : {0.0, 0.5, 0.999}) {
    const double a = aStar * mMeters;
    const double kerrRPlus = mMeters + std::sqrt((mMeters * mMeters) - (a * a));
    EXPECT_NEAR(verified::kdsEventHorizon(mMeters, a, lambda), kerrRPlus, 1.0e-12 * kerrRPlus)
        << "a*=" << aStar;
    EXPECT_NEAR(verified::kdsCosmologicalHorizon(mMeters, a, lambda), std::sqrt(3.0 / lambda),
                1.0e-12 * std::sqrt(3.0 / lambda));
    EXPECT_TRUE(verified::isPhysicalKdsBlackHole(mMeters, a, lambda)) << "a*=" << aStar;
  }
}

/**
 * @brief Carter-form components against mpmath, and a regular rotation axis.
 *
 * Xi = 1 + Lambda a^2 / 3 rescales t and phi by a constant, so R_mu_nu =
 * Lambda g_mu_nu holds with or without it and the Ricci test cannot see it.
 * Two checks can. The components at one point match the line element of
 * Carter (1973, Les Houches lectures) and Griffiths & Podolsky (2009),
 * assembled from its covectors in scripts/gen_kn_kds_reference.py. And with
 * phi of period 2 pi, the circumference-to-radius ratio of a small circle
 * about the axis is 2 pi only when Xi divides g_phph: the limit
 * sqrt(g_phph / g_thth) / sin(theta) -> 1 as theta -> 0, and -> Xi without it.
 */
TEST(KerrDeSitter, CarterComponentsAndAxisRegularity) {
  constexpr double m = 1.0;
  constexpr double a = 0.9;
  constexpr double lambda = 1.0e-2;
  const double theta = std::numbers::pi / 3.0;
  // mpmath: r = 3, theta = pi/3, M = 1, a = 0.9, Lambda = 1e-2.
  EXPECT_NEAR(verified::kdsGTt(3.0, theta, m, a, lambda), -0.3142788630304243, 1.0e-14);
  EXPECT_NEAR(verified::kdsGTph(3.0, theta, m, a, lambda), -0.45968465129291279, 1.0e-14);
  EXPECT_NEAR(verified::kdsGPhph(3.0, theta, m, a, lambda), 7.6331565734618123, 1.0e-13);

  const double xi = verified::kdsXi(a, lambda);
  for (double const r : {2.0, 5.0, 12.0}) {
    constexpr double thetaAxis = 1.0e-4;
    const double ratio = std::sqrt(verified::kdsGPhph(r, thetaAxis, m, a, lambda) /
                                   verified::kdsGThth(r, thetaAxis, a, lambda)) /
                         std::sin(thetaAxis);
    // O(theta^2) departure from 1 at theta = 1e-4, against Xi - 1 = 2.7e-3.
    EXPECT_NEAR(ratio, 1.0, 1.0e-6) << "r=" << r << " Xi=" << xi;
  }
}

/** @brief The ergosurface solves g_tt = 0 outside r_+ and reduces to Kerr at Lambda = 0. */
TEST(KerrDeSitter, ErgosurfaceSolvesGtt) {
  constexpr double m = 1.0;
  constexpr double a = 0.9;
  for (double const theta : {0.6, std::numbers::pi / 3.0, K_HALF_PI}) {
    const double cosTheta = std::cos(theta);
    EXPECT_NEAR(verified::kdsErgosphereRadius(theta, m, a, 0.0),
                m + std::sqrt((m * m) - (a * a * cosTheta * cosTheta)), 1.0e-13);
    for (double const lambda : {1.0e-2, 0.1}) {
      const double rErgo = verified::kdsErgosphereRadius(theta, m, a, lambda);
      EXPECT_GT(rErgo, verified::kdsEventHorizon(m, a, lambda));
      EXPECT_NEAR(verified::kdsGTt(rErgo, theta, m, a, lambda), 0.0, 1.0e-13);
      EXPECT_TRUE(verified::isInErgosphere(0.5 * (rErgo + verified::kdsEventHorizon(m, a, lambda)),
                                           theta, m, a, lambda));
    }
  }
  EXPECT_DOUBLE_EQ(verified::kdsErgosphereRadius(0.0, m, a, 1.0e-2),
                   verified::kdsEventHorizon(m, a, 1.0e-2));
}

/** @brief omega = -g_tph / g_phph = a (Delta_theta (r^2 + a^2) - Delta_r) / A. */
TEST(KerrDeSitter, FrameDragging) {
  constexpr double m = 1.0;
  constexpr double a = 0.9;
  constexpr double lambda = 1.0e-2;
  for (double const theta : {0.7, K_HALF_PI}) {
    for (double const r : {2.5, 8.0}) {
      const double expected = a *
                              ((verified::kdsDeltaTheta(theta, a, lambda) * ((r * r) + (a * a))) -
                               verified::kdsDelta(r, m, a, lambda)) /
                              verified::kdsA(r, theta, m, a, lambda);
      EXPECT_NEAR(verified::kdsFrameDraggingOmega(r, theta, m, a, lambda), expected, 1.0e-15);
    }
  }
  // Lambda = 0: omega = 2 M r a / A_Kerr.
  EXPECT_NEAR(verified::kdsFrameDraggingOmega(3.0, K_HALF_PI, m, a, 0.0),
              2.0 * m * 3.0 * a / verified::kdsA(3.0, K_HALF_PI, m, a, 0.0), 1.0e-15);
}

/** @brief Measured oracle floor on exact vacuum Kerr, which bounds K_RICCI_TOL from below. */
TEST(KerrDeSitter, KerrVacuumFloor) {
  double worst = 0.0;
  for (double const a : {0.0, 0.5, 0.9}) {
    for (double const r : {2.5, 6.0}) {
      const Vec4 x{0.0, r, std::numbers::pi / 3.0, 0.0};
      auto g = [a](const Vec4 &y) { return kerrMetric(y, 1.0, a); };
      worst = std::fmax(worst, lambdaResidual(ricci_oracle::ricci(g, x), g(x), 0.0));
    }
  }
  std::printf("Ricci oracle floor on vacuum Kerr: %.3e (tolerance %.1e)\n", worst, K_RICCI_TOL);
  EXPECT_LT(worst, K_RICCI_TOL);
}

/**
 * @brief R_mu_nu = Lambda g_mu_nu off the equator, with negative controls.
 *
 * theta = pi/3 keeps the theta-odd terms that vanish on the equator and would
 * hide a Delta_theta error.
 */
TEST(KerrDeSitter, EinsteinLambdaFieldEquation) {
  struct Case {
    double a;
    double lambda;
    double r;
  };
  const Case cases[] = {{0.9, 1.0e-2, 6.0}, {0.9, 0.1, 2.5}, {0.5, 0.05, 3.5}, {0.0, 0.1, 3.0}};
  double worst = 0.0;
  for (const Case &c : cases) {
    const Vec4 x{0.0, c.r, std::numbers::pi / 3.0, 0.0};
    auto g = [&c](const Vec4 &y) { return kdsMetric(y, 1.0, c.a, c.lambda); };
    const Mat4 ricciTensor = ricci_oracle::ricci(g, x);
    const double residual = lambdaResidual(ricciTensor, g(x), c.lambda);
    EXPECT_LT(residual, K_RICCI_TOL) << "a=" << c.a << " Lambda=" << c.lambda;
    worst = std::fmax(worst, residual);
    // R = 4 Lambda for an Einstein space.
    EXPECT_NEAR(ricci_oracle::scalar(ricci_oracle::inverse(g(x)), ricciTensor), 4.0 * c.lambda,
                K_RICCI_TOL);
    // Negative control: the same metric is not Ricci-flat.
    EXPECT_GT(lambdaResidual(ricciTensor, g(x), 0.0), 1.0e3 * K_RICCI_TOL);
  }
  // Negative control: the quadratic-Delta metric fails the field equation.
  const Vec4 x{0.0, 6.0, std::numbers::pi / 3.0, 0.0};
  auto legacy = [](const Vec4 &y) { return legacyQuadraticKdsMetric(y, 1.0, 0.9, 1.0e-2); };
  const double legacyResidual = lambdaResidual(ricci_oracle::ricci(legacy, x), legacy(x), 1.0e-2);
  std::printf("KdS Einstein-Lambda residual %.3e; quadratic-Delta metric %.3e\n", worst,
              legacyResidual);
  EXPECT_GT(legacyResidual, 1.0e3 * K_RICCI_TOL);
}
