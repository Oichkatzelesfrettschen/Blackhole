/**
 * @file tests/kerr_newman_test.cpp
 * @brief G5 -- Kerr-Newman metric limit and parity tests.
 *
 * WHY: `kerr_newman.h` implements the most general stationary axisymmetric
 * electrovacuum metric.  It must reduce exactly to Kerr when Q = 0 and to
 * Reissner-Nordstrom when a = 0.  Verifying these algebraic limits catches
 * sign errors, wrong coefficient insertions, and incorrect Q^2 placement
 * before the metric is used in geodesic integration.
 *
 * WHAT:
 *   - ReducesToKerr: all five metric components, both horizons, ergosphere,
 *     and frame dragging match Kerr formulas at Q = 0 across four spin values.
 *   - ReducesToReissnerNordstrom: g_tph = 0, Delta_RN and g_tt/g_rr/g_thth/
 *     g_phph match Reissner-Nordstrom at a = 0 across four charge values.
 *   - ChargeSplitsHorizons: r_+ decreases and r_- > 0 as Q grows.
 *   - SubExtremalCondition: validity predicate matches M^2 >= a^2 + Q^2.
 *   - ElectricPotentialVanishesAtQZero: A_t = 0 exactly when Q = 0.
 *   - ExtremeLimit: at M^2 = a^2 + Q^2 both horizons coincide at r = M.
 *
 * HOW: Pure analytical reference values are computed inline from the textbook
 * formulas (MTW; Wald 1984) and compared to the library at tolerance 1e-14.
 * No external data or GPU required.
 */

#include <cmath>
#include <numbers>

#include <gtest/gtest.h>

#include "physics/kerr_newman.h"

// ============================================================================
// Utility: Kerr reference formulas (geometric units, G=c=1)
// ============================================================================

namespace {

/** @brief Kerr Sigma = r^2 + a^2 cos^2(theta). */
double kerrSigmaRef(double r, double a, double theta) {
  const double c = std::cos(theta);
  return r * r + a * a * c * c;
}

/** @brief Kerr Delta = r^2 - 2 M r + a^2 (no charge). */
double kerrDeltaRef(double r, double m, double a) {
  return r * r - 2.0 * m * r + a * a;
}

/** @brief Kerr g_tt = -(Delta - a^2 sin^2 theta) / Sigma. */
double kerrGttRef(double r, double theta, double m, double a) {
  const double sigma = kerrSigmaRef(r, a, theta);
  const double delta = kerrDeltaRef(r, m, a);
  const double s = std::sin(theta);
  return -(delta - a * a * s * s) / sigma;
}

/** @brief Kerr g_rr = Sigma / Delta. */
double kerrGrrRef(double r, double theta, double m, double a) {
  return kerrSigmaRef(r, a, theta) / kerrDeltaRef(r, m, a);
}

/** @brief Kerr g_phph = A sin^2 theta / Sigma,  A = (r^2+a^2)^2 - a^2 Delta sin^2 theta. */
double kerrGphphRef(double r, double theta, double m, double a) {
  const double r2a2 = r * r + a * a;
  const double s = std::sin(theta);
  const double delta = kerrDeltaRef(r, m, a);
  const double metricFactor = r2a2 * r2a2 - a * a * delta * s * s;
  return metricFactor * s * s / kerrSigmaRef(r, a, theta);
}

/** @brief Kerr g_tph = -2 M r a sin^2 theta / Sigma. */
double kerrGtphRef(double r, double theta, double m, double a) {
  const double s = std::sin(theta);
  return -2.0 * m * r * a * s * s / kerrSigmaRef(r, a, theta);
}

/** @brief Kerr outer horizon r+ = M + sqrt(M^2 - a^2). */
double kerrRplusRef(double m, double a) {
  return m + std::sqrt(m * m - a * a);
}

/** @brief Kerr ergosphere r_ergo = M + sqrt(M^2 - a^2 cos^2 theta). */
double kerrErgoRef(double theta, double m, double a) {
  const double c = std::cos(theta);
  return m + std::sqrt(m * m - a * a * c * c);
}

void checkKerrMetricComponents(double r, double theta, double m, double a, double q, double tol) {
  // g_tt
  EXPECT_NEAR(physics::knGtt(r, theta, m, a, q), kerrGttRef(r, theta, m, a), tol)
      << "g_tt mismatch at a=" << a << " r=" << r;

  // g_rr
  EXPECT_NEAR(physics::knGrr(r, theta, m, a, q), kerrGrrRef(r, theta, m, a), tol)
      << "g_rr mismatch at a=" << a << " r=" << r;

  // g_thth = Sigma
  EXPECT_NEAR(physics::knGthth(r, a, theta), kerrSigmaRef(r, a, theta), tol)
      << "g_thth mismatch at a=" << a << " r=" << r;

  // g_phph
  EXPECT_NEAR(physics::knGphph(r, theta, m, a, q), kerrGphphRef(r, theta, m, a), tol)
      << "g_phph mismatch at a=" << a << " r=" << r;

  // g_tph
  EXPECT_NEAR(physics::knGtph(r, theta, m, a), kerrGtphRef(r, theta, m, a), tol)
      << "g_tph mismatch at a=" << a << " r=" << r;

  // Frame dragging
  EXPECT_NEAR(physics::knFrameDragging(r, theta, m, a, q),
              2.0 * m * r * a / physics::knA(r, theta, m, a, q), tol)
      << "frame dragging mismatch at a=" << a << " r=" << r;
}

void checkReissnerNordstromMetric(double r, double theta, double m, double a, double q,
                                  double deltaRn, double tol) {
  const double s = std::sin(theta);

  // g_tph must vanish: no spin means no frame dragging
  EXPECT_NEAR(physics::knGtph(r, theta, m, a), 0.0, tol) << "g_tph != 0 at Q=" << q << " r=" << r;

  // g_tt = -Delta_RN / r^2  (Sigma = r^2 when a = 0)
  EXPECT_NEAR(physics::knGtt(r, theta, m, a, q), -deltaRn / (r * r), tol)
      << "g_tt RN mismatch at Q=" << q << " r=" << r;

  // g_rr = r^2 / Delta_RN
  if (std::abs(deltaRn) > 1.0e-10) {
    EXPECT_NEAR(physics::knGrr(r, theta, m, a, q), r * r / deltaRn, tol)
        << "g_rr RN mismatch at Q=" << q << " r=" << r;
  }

  // g_thth = r^2  (Sigma = r^2 when a = 0)
  EXPECT_NEAR(physics::knGthth(r, a, theta), r * r, tol)
      << "g_thth RN mismatch at Q=" << q << " r=" << r;

  // g_phph = r^2 sin^2 theta.
  // WHY 1e-12 not 1e-14: at r=50, the magnitude is ~1875;
  // machine epsilon for doubles at that scale is ~2e-13.
  EXPECT_NEAR(physics::knGphph(r, theta, m, a, q), r * r * s * s, 1.0e-12)
      << "g_phph RN mismatch at Q=" << q << " r=" << r;
}

} // namespace

// ============================================================================
// Test 1: Q = 0 reduces KN to Kerr
// ============================================================================

/**
 * @brief All KN metric components match Kerr exactly when Q = 0.
 *
 * Tests g_tt, g_rr, g_thth, g_phph, g_tph, r_+, r_-, ergosphere, and
 * frame dragging at four spin values and two radii.
 */
TEST(KerrNewman, ReducesToKerr) {
  constexpr double m = 1.0;
  constexpr double q = 0.0;
  constexpr double theta = std::numbers::pi / 4.0;
  constexpr double tol = 1.0e-14;

  const double spins[] = {0.0, 0.3, 0.7, 0.95};
  const double radii[] = {6.0, 20.0};

  for (double const a : spins) {
    for (double const r : radii) {
      checkKerrMetricComponents(r, theta, m, a, q, tol);
    }

    // Horizon
    EXPECT_NEAR(physics::knOuterHorizon(m, a, q), kerrRplusRef(m, a), tol)
        << "r_+ mismatch at a=" << a;

    // Inner horizon (a > 0 gives distinct r-)
    if (a > 0.0) {
      const double rMinus = physics::knInnerHorizon(m, a, q);
      const double rPlus = physics::knOuterHorizon(m, a, q);
      EXPECT_GT(rPlus, rMinus) << "r_+ > r_- violated at a=" << a;
    }

    // Ergosphere at equator and pole
    for (double const th : {std::numbers::pi / 2.0, std::numbers::pi / 6.0}) {
      EXPECT_NEAR(physics::knErgosphereRadius(th, m, a, q), kerrErgoRef(th, m, a), tol)
          << "ergosphere mismatch at a=" << a << " theta=" << th;
    }
  }
}

// ============================================================================
// Test 2: a = 0 reduces KN to Reissner-Nordstrom
// ============================================================================

/**
 * @brief When a = 0 the metric reduces to Reissner-Nordstrom.
 *
 * Checks:
 *   - g_tph = 0 (no frame dragging without spin)
 *   - Delta_RN = r^2 - 2 M r + Q^2
 *   - g_tt = -(r^2 - 2 M r + Q^2) / r^2
 *   - g_rr = r^2 / (r^2 - 2 M r + Q^2)
 *   - g_thth = r^2
 *   - g_phph = r^2 sin^2(theta)
 *   - r_+_RN = M + sqrt(M^2 - Q^2)
 */
TEST(KerrNewman, ReducesToReissnerNordstrom) {
  constexpr double m = 1.0;
  constexpr double a = 0.0;
  constexpr double tol = 1.0e-14;

  const double charges[] = {0.0, 0.3, 0.6, 0.8};
  const double radii[] = {5.0, 15.0, 50.0};
  const double thetas[] = {std::numbers::pi / 6.0, std::numbers::pi / 2.0,
                           2.0 * std::numbers::pi / 3.0};

  for (double const q : charges) {
    for (double const r : radii) {
      const double deltaRn = r * r - 2.0 * m * r + q * q;

      for (double const theta : thetas) {
        checkReissnerNordstromMetric(r, theta, m, a, q, deltaRn, tol);
      }

      // Outer horizon: r_+ = M + sqrt(M^2 - Q^2)
      if (q < m) {
        const double rPlusRN = m + std::sqrt(m * m - q * q);
        EXPECT_NEAR(physics::knOuterHorizon(m, a, q), rPlusRN, tol) << "r_+ RN mismatch at Q=" << q;
      }
    }
  }
}

// ============================================================================
// Test 3: Charge progressively lowers the outer horizon
// ============================================================================

/**
 * @brief r_+ strictly decreases as Q increases from 0 to M (a fixed).
 *
 * Physical interpretation: charge contributes a repulsive component to the
 * effective potential, bringing the horizons closer together until they merge
 * at the extremal limit M^2 = a^2 + Q^2.
 */
TEST(KerrNewman, ChargeSplitsHorizons) {
  constexpr double m = 1.0;
  constexpr double a = 0.3;

  double prevRplus = physics::knOuterHorizon(m, a, 0.0);

  const double charges[] = {0.1, 0.3, 0.5, 0.7, 0.9};
  for (double const q : charges) {
    if (!physics::knSubExtremal(m, a, q)) {
      break;
    }

    const double rPlus = physics::knOuterHorizon(m, a, q);
    const double rMinus = physics::knInnerHorizon(m, a, q);

    EXPECT_LT(rPlus, prevRplus) << "r_+ should decrease as Q grows; Q=" << q;
    EXPECT_GT(rPlus, rMinus) << "r_+ > r_- required; Q=" << q;
    EXPECT_GT(rMinus, 0.0) << "r_- > 0 for sub-extremal KN; Q=" << q;

    prevRplus = rPlus;
  }
}

// ============================================================================
// Test 4: Sub-extremal validity predicate
// ============================================================================

/**
 * @brief knSubExtremal correctly partitions physical and unphysical parameters.
 */
TEST(KerrNewman, SubExtremalCondition) {
  constexpr double m = 1.0;

  // Physical cases: a^2 + Q^2 < M^2
  EXPECT_TRUE(physics::knSubExtremal(m, 0.0, 0.0)); // Schwarzschild
  EXPECT_TRUE(physics::knSubExtremal(m, 0.5, 0.0)); // Kerr, a < M
  EXPECT_TRUE(physics::knSubExtremal(m, 0.0, 0.5)); // RN, Q < M
  EXPECT_TRUE(physics::knSubExtremal(m, 0.6, 0.6)); // a^2+Q^2 = 0.72 < 1

  // Extremal (boundary, should be allowed)
  EXPECT_TRUE(physics::knSubExtremal(m, m, 0.0)); // extremal Kerr
  EXPECT_TRUE(physics::knSubExtremal(m, 0.0, m)); // extremal RN

  // Super-extremal: naked singularity
  EXPECT_FALSE(physics::knSubExtremal(m, 0.8, 0.8)); // a^2+Q^2 = 1.28 > 1
  EXPECT_FALSE(physics::knSubExtremal(m, m + 0.1, 0.0));
  EXPECT_FALSE(physics::knSubExtremal(m, 0.0, m + 0.1));
}

// ============================================================================
// Test 5: Electric potential vanishes when Q = 0
// ============================================================================

/**
 * @brief A_t = -Q r / Sigma is identically 0 when Q = 0.
 *
 * Ensures the electromagnetic potential does not introduce spurious
 * contributions to the geodesic equation in the uncharged limit.
 */
TEST(KerrNewman, ElectricPotentialVanishesAtQZero) {
  constexpr double tol = 1.0e-30;
  const double radii[] = {2.0, 5.0, 10.0, 100.0};
  const double thetas[] = {0.1, std::numbers::pi / 4.0, std::numbers::pi / 2.0};
  const double spins[] = {0.0, 0.5, 0.9};

  for (double const a : spins) {
    for (double const r : radii) {
      for (double const theta : thetas) {
        EXPECT_NEAR(physics::knElectricPotentialAt(r, theta, a, 0.0), 0.0, tol)
            << "A_t != 0 at Q=0, a=" << a << " r=" << r;
        EXPECT_NEAR(physics::knMagneticPotentialPhi(r, theta, a, 0.0), 0.0, tol)
            << "A_phi != 0 at Q=0, a=" << a << " r=" << r;
      }
    }
  }
}

// ============================================================================
// Test 6: Extremal limit -- horizons coincide at r = M
// ============================================================================

/**
 * @brief At M^2 = a^2 + Q^2, the outer and inner horizons coincide at r = M.
 *
 * The extremal KN black hole has vanishing surface gravity; the two horizons
 * merge into a single degenerate horizon at r = M.
 */
TEST(KerrNewman, ExtremeLimit) {
  constexpr double m = 1.0;
  constexpr double tol = 1.0e-14;

  // Case A: extremal Kerr (Q = 0, a = M)
  {
    const double rPlus = physics::knOuterHorizon(m, m, 0.0);
    const double rMinus = physics::knInnerHorizon(m, m, 0.0);
    EXPECT_NEAR(rPlus, m, tol) << "extremal Kerr r_+ != M";
    EXPECT_NEAR(rMinus, m, tol) << "extremal Kerr r_- != M";
  }

  // Case B: extremal RN (a = 0, Q = M)
  {
    const double rPlus = physics::knOuterHorizon(m, 0.0, m);
    const double rMinus = physics::knInnerHorizon(m, 0.0, m);
    EXPECT_NEAR(rPlus, m, tol) << "extremal RN r_+ != M";
    EXPECT_NEAR(rMinus, m, tol) << "extremal RN r_- != M";
  }

  // Case C: mixed extremal a^2 + Q^2 = M^2, a = Q = M/sqrt(2).
  // WHY looser tolerance: M/sqrt(2) is irrational; its IEEE 754 square
  // differs from M^2/2 by ~7e-17, so sqrt(disc) ~ 1.4e-8 rather than 0.
  // We check that both horizons coincide (r_+ == r_-) rather than
  // pinning them to M exactly.
  {
    const double aq = m / std::numbers::sqrt2;
    const double rPlus = physics::knOuterHorizon(m, aq, aq);
    const double rMinus = physics::knInnerHorizon(m, aq, aq);
    EXPECT_NEAR(rPlus, m, 2.0e-7) << "mixed extremal r_+ ~ M";
    EXPECT_NEAR(rMinus, m, 2.0e-7) << "mixed extremal r_- ~ M";
    EXPECT_NEAR(rPlus, rMinus, 3.0e-8) << "mixed extremal horizons coincide";
  }
}
