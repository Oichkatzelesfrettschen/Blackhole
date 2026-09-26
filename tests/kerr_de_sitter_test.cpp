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
#include <limits>
#include <numbers>

#include <gtest/gtest.h>

#include "physics/verified/kerr.hpp"
#include "physics/verified/kerr_de_sitter.hpp"
#include "support/ricci_oracle.h"

namespace {

using ricci_oracle::Mat4;
using ricci_oracle::Vec4;

constexpr double kHalfPi = std::numbers::pi / 2.0;

// Residual tolerance for R_mu_nu - Lambda g_mu_nu at |g| <= 20 (points below).
// KerrVacuumFloor measures the oracle floor on exact Kerr; this bound sits
// above that floor and far below the negative-control residuals.
constexpr double kRicciTol = 1.0e-6;

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
 * g_tt = -(1 - 2Mr/Sigma + Lambda r^2 sin^2 / 3), and Kerr g_tph and g_thth
 * (audit 02-open-gororoba-crossref F5). The negative control: its Ricci
 * residual shows the tolerance discriminates.
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

} // namespace

/** @brief a = 0 is Schwarzschild-de Sitter: g_tt = -(1 - 2M/r - Lambda r^2 / 3) = -1 / g_rr. */
TEST(KerrDeSitter, SchwarzschildDeSitterLimit) {
  constexpr double m = 1.0;
  for (double const lambda : {1.0e-4, 1.0e-2, 0.05}) {
    for (double const r : {3.0, 5.0, 10.0}) {
      for (double const theta : {0.4, std::numbers::pi / 3.0, kHalfPi}) {
        const double f = 1.0 - (2.0 * m / r) - (lambda * r * r / 3.0);
        EXPECT_NEAR(verified::kdsGTt(r, theta, m, 0.0, lambda), -f, 1.0e-14);
        EXPECT_NEAR(verified::kdsGRr(r, theta, m, 0.0, lambda), 1.0 / f, 1.0e-12);
        EXPECT_NEAR(verified::kdsGThth(r, theta, 0.0, lambda), r * r, 1.0e-12);
        EXPECT_NEAR(verified::kdsGPhph(r, theta, m, 0.0, lambda),
                    r * r * std::sin(theta) * std::sin(theta), 1.0e-12);
        EXPECT_DOUBLE_EQ(verified::kdsGTph(r, theta, m, 0.0, lambda), 0.0);
      }
    }
  }
  // mpmath: r = 10, Lambda = 1e-2.
  EXPECT_NEAR(verified::kdsGTt(10.0, kHalfPi, m, 0.0, 1.0e-2), -0.46666666666666667, 1.0e-15);
  EXPECT_NEAR(verified::kdsGRr(10.0, kHalfPi, m, 0.0, 1.0e-2), 2.1428571428571429, 1.0e-14);
}

/** @brief Lambda = 0 reproduces every Kerr component. */
TEST(KerrDeSitter, KerrLimit) {
  constexpr double m = 1.0;
  for (double const a : {-0.7, 0.3, 0.9}) {
    for (double const theta : {0.5, std::numbers::pi / 3.0, kHalfPi}) {
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
 * @brief Horizons against mpmath polyroots of Delta_r, including Lambda = 1e-10.
 *
 * Bisection resolves each root to adjacent doubles; 1e-12 relative covers the
 * conditioning of Delta_r at the roots listed.
 */
TEST(KerrDeSitter, HorizonsMatchQuarticRoots) {
  struct Case {
    double a;
    double lambda;
    double rMinus; // 0 at a = 0: the root is the singularity
    double rPlus;
    double rCosmo;
  };
  const Case cases[] = {
      {0.0, 1.0e-2, 0.0, 2.0277939461513023, 16.217354832407434},
      {0.0, 1.0e-4, 0.0, 2.000266773390257, 172.19628458904262},
      {0.9, 1.0e-2, 0.56274795742926431, 1.4591964724233871, 16.221118934330201},
      {0.9, 0.1, 0.55134885405674908, 1.7824862466846589, 3.9406926580723805},
      {0.5, 1.0e-10, 0.13397459621546879, 1.8660254040345312, 173204.08074822735},
  };
  for (const Case &c : cases) {
    EXPECT_NEAR(verified::kdsInnerHorizon(1.0, c.a, c.lambda), c.rMinus, 1.0e-12 * (1.0 + c.rMinus))
        << "a=" << c.a << " Lambda=" << c.lambda;
    EXPECT_NEAR(verified::kdsEventHorizon(1.0, c.a, c.lambda), c.rPlus, 1.0e-12 * c.rPlus)
        << "a=" << c.a << " Lambda=" << c.lambda;
    EXPECT_NEAR(verified::kdsCosmologicalHorizon(1.0, c.a, c.lambda), c.rCosmo, 1.0e-12 * c.rCosmo)
        << "a=" << c.a << " Lambda=" << c.lambda;
    EXPECT_TRUE(verified::isPhysicalKdsBlackHole(1.0, c.a, c.lambda));
    EXPECT_TRUE(verified::verifyHorizonOrdering(1.0, c.a, c.lambda));
  }
  // Beyond the Nariai bound (9 Lambda M^2 < 1 at a = 0) no black hole exists.
  EXPECT_TRUE(std::isnan(verified::kdsEventHorizon(1.0, 0.0, 0.2)));
  EXPECT_TRUE(std::isnan(verified::kdsCosmologicalHorizon(1.0, 0.0, 0.2)));
  EXPECT_FALSE(verified::isPhysicalKdsBlackHole(1.0, 0.0, 0.2));
  // Super-extremal spin has no event horizon.
  EXPECT_TRUE(std::isnan(verified::kdsEventHorizon(1.0, 1.2, 1.0e-3)));
}

/** @brief The ergosurface solves g_tt = 0 outside r_+ and reduces to Kerr at Lambda = 0. */
TEST(KerrDeSitter, ErgosurfaceSolvesGtt) {
  constexpr double m = 1.0;
  constexpr double a = 0.9;
  for (double const theta : {0.6, std::numbers::pi / 3.0, kHalfPi}) {
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
  for (double const theta : {0.7, kHalfPi}) {
    for (double const r : {2.5, 8.0}) {
      const double expected = a *
                              ((verified::kdsDeltaTheta(theta, a, lambda) * ((r * r) + (a * a))) -
                               verified::kdsDelta(r, m, a, lambda)) /
                              verified::kdsA(r, theta, m, a, lambda);
      EXPECT_NEAR(verified::kdsFrameDraggingOmega(r, theta, m, a, lambda), expected, 1.0e-15);
    }
  }
  // Lambda = 0: omega = 2 M r a / A_Kerr.
  EXPECT_NEAR(verified::kdsFrameDraggingOmega(3.0, kHalfPi, m, a, 0.0),
              2.0 * m * 3.0 * a / verified::kdsA(3.0, kHalfPi, m, a, 0.0), 1.0e-15);
}

/** @brief Measured oracle floor on exact vacuum Kerr, which bounds kRicciTol from below. */
TEST(KerrDeSitter, KerrVacuumFloor) {
  double worst = 0.0;
  for (double const a : {0.0, 0.5, 0.9}) {
    for (double const r : {2.5, 6.0}) {
      const Vec4 x{0.0, r, std::numbers::pi / 3.0, 0.0};
      auto g = [a](const Vec4 &y) { return kerrMetric(y, 1.0, a); };
      worst = std::fmax(worst, lambdaResidual(ricci_oracle::ricci(g, x), g(x), 0.0));
    }
  }
  std::printf("Ricci oracle floor on vacuum Kerr: %.3e (tolerance %.1e)\n", worst, kRicciTol);
  EXPECT_LT(worst, kRicciTol);
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
    EXPECT_LT(residual, kRicciTol) << "a=" << c.a << " Lambda=" << c.lambda;
    worst = std::fmax(worst, residual);
    // R = 4 Lambda for an Einstein space.
    EXPECT_NEAR(ricci_oracle::scalar(ricci_oracle::inverse(g(x)), ricciTensor), 4.0 * c.lambda,
                kRicciTol);
    // Negative control: the same metric is not Ricci-flat.
    EXPECT_GT(lambdaResidual(ricciTensor, g(x), 0.0), 1.0e3 * kRicciTol);
  }
  // Negative control: the quadratic-Delta metric fails the field equation.
  const Vec4 x{0.0, 6.0, std::numbers::pi / 3.0, 0.0};
  auto legacy = [](const Vec4 &y) { return legacyQuadraticKdsMetric(y, 1.0, 0.9, 1.0e-2); };
  const double legacyResidual = lambdaResidual(ricci_oracle::ricci(legacy, x), legacy(x), 1.0e-2);
  std::printf("KdS Einstein-Lambda residual %.3e; quadratic-Delta metric %.3e\n", worst,
              legacyResidual);
  EXPECT_GT(legacyResidual, 1.0e3 * kRicciTol);
}
