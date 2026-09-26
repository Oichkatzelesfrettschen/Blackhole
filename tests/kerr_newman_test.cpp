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
 *   - FrameDraggingChargeTerm: g_tph and omega carry the a Q^2 cross term in
 *     both namespaces.
 *   - IscoReissnerNordstromCubic / IscoMixedSpinCharge / IscoKerrLimit /
 *     IscoSignAndScaling: verified:: ISCO against mpmath dE/dr = 0 roots,
 *     Bardeen-Press-Teukolsky at Q = 0, the phi -> -phi reflection, and M scaling.
 *   - PhotonOrbitEquator: circular photon orbit against mpmath null limits of
 *     circular geodesics, 3M at a = Q = 0, and the BPT Kerr orbit at Q = 0.
 *   - EmPotentialNamespacesAgree: A_t and A_phi agree across physics:: and
 *     verified::, with A_phi / A_t = -a sin^2 theta.
 *   - EinsteinMaxwellFieldEquation: the verified:: metric and the physics::
 *     potential satisfy R_mu_nu = 2 (F_ma F_n^a - g_mn F^2 / 4) and R = 0
 *     through tests/support/ricci_oracle.h, with negative controls for the
 *     Kerr-only g_tph and for a flipped A_phi.
 *
 * HOW: Pure analytical reference values are computed inline from the textbook
 * formulas (MTW; Wald 1984) and compared to the library at tolerance 1e-14.
 * No external data or GPU required.
 */

#include <cmath>
#include <cstdio>
#include <numbers>

#include <gtest/gtest.h>

#include "physics/kerr_newman.h"
#include "physics/verified/kerr_newman.hpp"
#include "support/ricci_oracle.h"

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
  EXPECT_NEAR(physics::knGtph(r, theta, m, a, q), kerrGtphRef(r, theta, m, a), tol)
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
  EXPECT_NEAR(physics::knGtph(r, theta, m, a, q), 0.0, tol) << "g_tph != 0 at Q=" << q << " r=" << r;

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

// ============================================================================
// Reference constants: scripts/gen_kn_kds_reference.py (mpmath, 60 digits).
// The ISCO values are roots of dE/dr = 0 for the equatorial circular-orbit
// energy of the Carter-form metric, independent of the closed form under test.
// ============================================================================

namespace {

constexpr double K_ISCO_A0_Q05 = 5.6066434276477041;
constexpr double K_ISCO_A0_Q09 = 4.5137450467151034;
constexpr double K_ISCO_A05_Q05_PRO = 3.7320508075688773;
constexpr double K_ISCO_A05_Q05_RET = 7.2051154235083894;
constexpr double K_ISCO_A09_Q03_PRO = 1.980407461799196;
constexpr double K_ISCO_A09_Q03_RET = 8.6013892403446616;
constexpr double K_OMEGA_R3_A05_Q05 = 0.033948339483394834;
constexpr double K_PHOTON_A0_Q05 = 2.8228756555322953;
constexpr double K_PHOTON_A05_Q05_PRO = 2.118828664898468;
constexpr double K_PHOTON_A05_Q05_RET = 3.3756176710888185;
constexpr double K_PHOTON_A09_Q03_PRO = 1.3996686888099221;
constexpr double K_PHOTON_A09_Q03_RET = 3.8589114446045108;

// Bisection stops at a 1e-15 M bracket; the closed-form root is
// well-conditioned there, so 1e-12 bounds the double-precision error.
constexpr double K_ISCO_TOL = 1.0e-12;

/** @brief Bardeen-Press-Teukolsky co-rotating (sign = -1) or counter-rotating (+1) ISCO. */
double bptIsco(double m, double spinMagnitude, double sign) {
  const double s = spinMagnitude / m;
  const double z1 =
      1.0 + (std::cbrt(1.0 - (s * s)) * (std::cbrt(1.0 + s) + std::cbrt(1.0 - s)));
  const double z2 = std::sqrt((3.0 * s * s) + (z1 * z1));
  return m * (3.0 + z2 + (sign * std::sqrt((3.0 - z1) * (3.0 + z1 + (2.0 * z2)))));
}

} // namespace

/**
 * @brief g_tph = -a (2Mr - Q^2) sin^2 / Sigma and omega = a (2Mr - Q^2) / A.
 *
 * The Q = 0 and a = 0 limits both hide the a Q^2 cross term, so this test
 * evaluates a = Q = 0.5 on and off the equator in both namespaces.
 */
TEST(KerrNewman, FrameDraggingChargeTerm) {
  constexpr double m = 1.0;
  constexpr double a = 0.5;
  constexpr double q = 0.5;
  constexpr double r = 3.0;
  constexpr double halfPi = std::numbers::pi / 2.0;

  EXPECT_NEAR(verified::knFrameDraggingOmega(r, halfPi, m, a, q), K_OMEGA_R3_A05_Q05, 1.0e-15);
  EXPECT_NEAR(physics::knFrameDragging(r, halfPi, m, a, q), K_OMEGA_R3_A05_Q05, 1.0e-15);

  for (double const theta : {std::numbers::pi / 5.0, std::numbers::pi / 3.0, halfPi}) {
    const double s2 = std::sin(theta) * std::sin(theta);
    const double sigma = kerrSigmaRef(r, a, theta);
    const double delta = (r * r) - (2.0 * m * r) + (a * a) + (q * q);
    // Carter-form expansion: g_tph = a sin^2 (Delta - r^2 - a^2) / Sigma.
    const double gTphCarter = a * s2 * (delta - (r * r) - (a * a)) / sigma;
    EXPECT_NEAR(physics::knGtph(r, theta, m, a, q), gTphCarter, 1.0e-15) << "theta=" << theta;
    EXPECT_NEAR(verified::knGTph(r, theta, m, a, q), gTphCarter, 1.0e-15) << "theta=" << theta;
    const double omega = -gTphCarter / physics::knGphph(r, theta, m, a, q);
    EXPECT_NEAR(physics::knFrameDragging(r, theta, m, a, q), omega, 1.0e-15);
    EXPECT_NEAR(verified::knFrameDraggingOmega(r, theta, m, a, q), omega, 1.0e-15);
  }
}

/** @brief a = 0 ISCO is the root of r^3 - 6Mr^2 + 9Q^2 r - 4Q^4/M = 0. */
TEST(KerrNewman, IscoReissnerNordstromCubic) {
  EXPECT_NEAR(verified::knIscoRadiusPrograde(1.0, 0.0, 0.5), K_ISCO_A0_Q05, K_ISCO_TOL);
  EXPECT_NEAR(verified::knIscoRadiusRetrograde(1.0, 0.0, 0.5), K_ISCO_A0_Q05, K_ISCO_TOL);
  EXPECT_NEAR(verified::knIscoRadiusPrograde(1.0, 0.0, 0.9), K_ISCO_A0_Q09, K_ISCO_TOL);
  // Extremal Reissner-Nordstrom: the cubic factors as -(r - M)^2 (r - 4M).
  EXPECT_NEAR(verified::knIscoRadiusPrograde(1.0, 0.0, 1.0), 4.0, K_ISCO_TOL);
  // Charge moves the ISCO inward from 6M.
  EXPECT_LT(verified::knIscoRadiusPrograde(1.0, 0.0, 0.5), 6.0);
}

/** @brief Spin and charge together, where the a Q^2 cross terms act. */
TEST(KerrNewman, IscoMixedSpinCharge) {
  EXPECT_NEAR(verified::knIscoRadiusPrograde(1.0, 0.5, 0.5), K_ISCO_A05_Q05_PRO, K_ISCO_TOL);
  EXPECT_NEAR(verified::knIscoRadiusRetrograde(1.0, 0.5, 0.5), K_ISCO_A05_Q05_RET, K_ISCO_TOL);
  EXPECT_NEAR(verified::knIscoRadiusPrograde(1.0, 0.9, 0.3), K_ISCO_A09_Q03_PRO, K_ISCO_TOL);
  EXPECT_NEAR(verified::knIscoRadiusRetrograde(1.0, 0.9, 0.3), K_ISCO_A09_Q03_RET, K_ISCO_TOL);
}

/** @brief Q = 0 reproduces Bardeen-Press-Teukolsky for signed spin up to a = 0.9999. */
TEST(KerrNewman, IscoKerrLimit) {
  for (double const a : {-0.9999, -0.9, -0.5, 0.0, 0.3, 0.7, 0.9, 0.998, 0.9999}) {
    const double coRotating = (a >= 0.0) ? -1.0 : 1.0;
    EXPECT_NEAR(verified::knIscoRadiusPrograde(1.0, a, 0.0), bptIsco(1.0, std::abs(a), coRotating),
                1.0e-10)
        << "prograde a=" << a;
    EXPECT_NEAR(verified::knIscoRadiusRetrograde(1.0, a, 0.0),
                bptIsco(1.0, std::abs(a), -coRotating), 1.0e-10)
        << "retrograde a=" << a;
  }
  EXPECT_NEAR(verified::knIscoRadiusPrograde(1.0, 0.998, 0.0), 1.2369706, 1.0e-7);
}

/** @brief phi -> -phi reflection, M scaling, and the super-extremal guard. */
TEST(KerrNewman, IscoSignAndScaling) {
  for (double const a : {0.2, 0.6, 0.9}) {
    for (double const q : {0.0, 0.3}) {
      EXPECT_DOUBLE_EQ(verified::knIscoRadiusPrograde(1.0, -a, q),
                       verified::knIscoRadiusRetrograde(1.0, a, q));
      EXPECT_NEAR(verified::knIscoRadiusPrograde(2.5, 2.5 * a, 2.5 * q),
                  2.5 * verified::knIscoRadiusPrograde(1.0, a, q), 1.0e-11)
          << "a=" << a << " q=" << q;
    }
  }
  EXPECT_TRUE(std::isnan(verified::knIscoRadiusPrograde(1.0, 0.8, 0.8)));
  EXPECT_TRUE(std::isnan(verified::knIscoRadiusPrograde(0.0, 0.0, 0.0)));
}

/**
 * @brief Equatorial photon orbit: null limit of circular geodesics, signed spin.
 *
 * References are mpmath roots of g_tt + 2 g_tphi Omega + g_phph Omega^2 = 0
 * with Omega from the geodesic circularity condition.
 */
TEST(KerrNewman, PhotonOrbitEquator) {
  EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, 0.0, 0.0), 3.0, K_ISCO_TOL);
  EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, 0.0, 0.5), K_PHOTON_A0_Q05, K_ISCO_TOL);
  // Extremal Reissner-Nordstrom: (3M + sqrt(9M^2 - 8Q^2)) / 2 = 2M.
  EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, 0.0, 1.0), 2.0, K_ISCO_TOL);
  EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, 0.5, 0.5), K_PHOTON_A05_Q05_PRO, K_ISCO_TOL);
  EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, -0.5, 0.5), K_PHOTON_A05_Q05_RET, K_ISCO_TOL);
  EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, 0.9, 0.3), K_PHOTON_A09_Q03_PRO, K_ISCO_TOL);
  EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, -0.9, 0.3), K_PHOTON_A09_Q03_RET, K_ISCO_TOL);
  // Q = 0: Bardeen-Press-Teukolsky 2M(1 + cos((2/3) acos(-a/M))).
  for (double const a : {-0.99, -0.5, 0.3, 0.9, 0.99}) {
    const double bpt = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(-a)));
    EXPECT_NEAR(verified::knPhotonSphereEquator(1.0, a, 0.0), bpt, 1.0e-10) << "a=" << a;
  }
  EXPECT_NEAR(verified::knPhotonSphereEquator(2.5, 1.25, 1.25),
              2.5 * verified::knPhotonSphereEquator(1.0, 0.5, 0.5), 1.0e-11);
  EXPECT_TRUE(std::isnan(verified::knPhotonSphereEquator(1.0, 0.8, 0.8)));
}

/**
 * @brief The EM potential is -(Qr/Sigma)(dt - a sin^2 dphi) in both namespaces.
 *
 * The overall sign of A_mu is a convention; the ratio A_phi / A_t = -a sin^2
 * is fixed by the metric's (dt - a sin^2 dphi) one-form.
 */
TEST(KerrNewman, EmPotentialNamespacesAgree) {
  for (double const a : {-0.6, 0.3, 0.9}) {
    for (double const theta : {0.3, std::numbers::pi / 3.0, std::numbers::pi / 2.0}) {
      for (double const r : {2.5, 7.0}) {
        constexpr double q = 0.4;
        const double at = physics::knElectricPotentialAt(r, theta, a, q);
        const double aphi = physics::knMagneticPotentialPhi(r, theta, a, q);
        EXPECT_NEAR(verified::knPotentialT(r, theta, a, q), at, 1.0e-15);
        EXPECT_NEAR(verified::knPotentialPhi(r, theta, a, q), aphi, 1.0e-15);
        const double s2 = std::sin(theta) * std::sin(theta);
        EXPECT_NEAR(aphi, -a * s2 * at, 1.0e-15) << "a=" << a << " theta=" << theta;
      }
    }
  }
}

// ============================================================================
// Einstein-Maxwell field equation through the finite-difference Ricci oracle
// ============================================================================

namespace {

using ricci_oracle::Mat4;
using ricci_oracle::Vec4;

// Residual tolerance for R_mu_nu - 2 (F F - g F^2 / 4). The oracle floor on
// vacuum Kerr is ~2e-9 (kerr_de_sitter_test KerrVacuumFloor); the Maxwell
// source adds a fourth-order difference of A at h = 1e-4.
constexpr double K_FIELD_TOL = 1.0e-7;

Mat4 knMetric(const Vec4 &x, double m, double a, double q, bool kerrCrossTerm) {
  const double r = x[1];
  const double theta = x[2];
  Mat4 g{};
  g[0][0] = verified::knGTt(r, theta, m, a, q);
  g[1][1] = verified::knGRr(r, theta, m, a, q);
  g[2][2] = verified::knGThth(r, theta, a);
  g[3][3] = verified::knGPhph(r, theta, m, a, q);
  g[0][3] = kerrCrossTerm ? kerrGtphRef(r, theta, m, a) : verified::knGTph(r, theta, m, a, q);
  g[3][0] = g[0][3];
  return g;
}

Vec4 knPotential(const Vec4 &x, double a, double q, double phiSign) {
  return {physics::knElectricPotentialAt(x[1], x[2], a, q), 0.0, 0.0,
          phiSign * physics::knMagneticPotentialPhi(x[1], x[2], a, q)};
}

struct FieldResidual {
  double tensor;   // max |R_mn - S_mn|
  double scalar;   // |g^mn R_mn|
  double tPhi;     // |R_tphi - S_tphi|
};

FieldResidual einsteinMaxwellResidual(double a, double q, double r, bool kerrCrossTerm,
                                      double phiSign) {
  constexpr double m = 1.0;
  const Vec4 x{0.0, r, std::numbers::pi / 3.0, 0.0};
  auto g = [&](const Vec4 &y) { return knMetric(y, m, a, q, kerrCrossTerm); };
  auto potential = [&](const Vec4 &y) { return knPotential(y, a, q, phiSign); };
  const Mat4 metric = g(x);
  const Mat4 ricciTensor = ricci_oracle::ricci(g, x);
  const Mat4 source = ricci_oracle::maxwellSource(potential, metric, x);
  return {ricci_oracle::maxAbsDifference(ricciTensor, source, 1.0),
          std::abs(ricci_oracle::scalar(ricci_oracle::inverse(metric), ricciTensor)),
          std::abs(ricciTensor[0][3] - source[0][3])};
}

} // namespace

/**
 * @brief R_mu_nu equals the traceless Maxwell source, and R = 0, off the equator.
 *
 * Electrovac KN has R = 0 (the Maxwell stress is traceless) but R_mu_nu != 0,
 * so the full tensor equation is the check; the scalar condition alone cannot
 * see the g_tph charge term or the sign of A_phi.
 */
TEST(KerrNewman, EinsteinMaxwellFieldEquation) {
  struct Case {
    double a;
    double q;
    double r;
  };
  const Case cases[] = {{0.5, 0.5, 3.0}, {0.9, 0.3, 4.0}, {0.0, 0.8, 3.0}, {-0.6, 0.5, 3.5}};
  double worst = 0.0;
  for (const Case &c : cases) {
    const FieldResidual residual = einsteinMaxwellResidual(c.a, c.q, c.r, false, 1.0);
    EXPECT_LT(residual.tensor, K_FIELD_TOL) << "a=" << c.a << " Q=" << c.q;
    EXPECT_LT(residual.scalar, K_FIELD_TOL) << "a=" << c.a << " Q=" << c.q;
    worst = std::fmax(worst, residual.tensor);
  }
  const FieldResidual kerrCross = einsteinMaxwellResidual(0.5, 0.5, 3.0, true, 1.0);
  const FieldResidual flippedPhi = einsteinMaxwellResidual(0.5, 0.5, 3.0, false, -1.0);
  std::printf("KN Einstein-Maxwell residual %.3e; Kerr-only g_tph %.3e; flipped A_phi R_tphi %.3e\n",
              worst, kerrCross.tensor, flippedPhi.tPhi);
  // Negative controls: the Kerr cross term -2Mra sin^2 / Sigma and the
  // -Qra sin^2 / Sigma potential both violate the field equation.
  EXPECT_GT(kerrCross.tensor, 1.0e3 * K_FIELD_TOL);
  EXPECT_GT(flippedPhi.tPhi, 1.0e3 * K_FIELD_TOL);
}
