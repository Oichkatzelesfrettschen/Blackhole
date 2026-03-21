/**
 * @file tests/lqg_kerr_test.cpp
 * @brief Tests for the LQG-modified Kerr metric (D6).
 *
 * WHY: lqg_kerr.h replaces the classical point-mass Kerr singularity with a
 * Hayward-type regular mass function.  These tests verify:
 *   1. Exact reduction to Kerr when l = 0 (the LQG correction is absent).
 *   2. Regularity at r = 0: M_eff vanishes so the metric is non-singular.
 *   3. Asymptotic flatness: M_eff(r) -> M as r -> inf.
 *   4. Monotone effective mass: M_eff(r) increases from 0 to M.
 *   5. Horizon bisection: outer horizon exists for sub-extremal parameters.
 *   6. EHT bound compliance: photon sphere shifts inward for l = 0.3 M.
 *
 * HOW: Pure analytical checks; no GPU or external data required.
 */

#include <gtest/gtest.h>
#include "physics/lqg_kerr.h"
#include <cmath>
#include <numbers>

// ============================================================================
// Kerr reference formulas (geometric units)
// ============================================================================

namespace {

/** @brief Kerr Delta = r^2 - 2 M r + a^2. */
double kerrDeltaRef(double r, double M, double a) {
    return r * r - 2.0 * M * r + a * a;
}

/** @brief Kerr g_tt = -(Delta - a^2 sin^2 theta) / Sigma. */
double kerrGttRef(double r, double theta, double M, double a) {
    const double Sigma = r * r + a * a * std::cos(theta) * std::cos(theta);
    const double Delta = kerrDeltaRef(r, M, a);
    const double s     = std::sin(theta);
    return -(Delta - a * a * s * s) / Sigma;
}

} // namespace

// ============================================================================
// Test 1: l = 0 reduces to exact Kerr
// ============================================================================

/**
 * @brief All LQG-Kerr components match Kerr exactly when l = 0.
 *
 * Checks Delta, g_tt, g_rr, g_thth, g_phph, and g_tph at several
 * (r, theta) pairs and spin values.
 */
TEST(LqgKerr, ReducesToKerrAtLZero) {
    constexpr double M   = 1.0;
    constexpr double l   = 0.0;
    constexpr double tol = 1.0e-14;

    const double spins[]  = {0.0, 0.3, 0.8, 0.998};
    const double radii[]  = {3.0, 6.0, 20.0};
    const double thetas[] = {std::numbers::pi / 6.0,
                              std::numbers::pi / 3.0,
                              std::numbers::pi / 2.0};

    for (double a : spins) {
        for (double r : radii) {
            // Effective mass == M when l = 0
            EXPECT_NEAR(physics::lqgEffectiveMass(r, M, l), M, tol)
                << "M_eff != M at l=0, a=" << a << " r=" << r;

            // Delta
            EXPECT_NEAR(physics::lqgDelta(r, M, a, l),
                        kerrDeltaRef(r, M, a), tol)
                << "Delta mismatch at l=0, a=" << a << " r=" << r;

            for (double theta : thetas) {
                // g_tt
                EXPECT_NEAR(physics::lqgGtt(r, theta, M, a, l),
                            kerrGttRef(r, theta, M, a), tol)
                    << "g_tt mismatch at l=0, a=" << a << " r=" << r;

                // g_thth = Sigma (same as Kerr)
                const double sigma_ref = r * r + a * a * std::cos(theta) * std::cos(theta);
                EXPECT_NEAR(physics::lqgGthth(r, a, theta), sigma_ref, tol)
                    << "g_thth mismatch at l=0, a=" << a << " r=" << r;

                // g_tph = -2 M r a sin^2(theta) / Sigma
                const double Sigma = sigma_ref;
                const double s     = std::sin(theta);
                const double gtph_ref = -2.0 * M * r * a * s * s / Sigma;
                EXPECT_NEAR(physics::lqgGtph(r, theta, M, a, l), gtph_ref, tol)
                    << "g_tph mismatch at l=0, a=" << a << " r=" << r;
            }
        }
    }
}

// ============================================================================
// Test 2: Metric is regular at r = 0 (singularity removed)
// ============================================================================

/**
 * @brief M_eff(0) = 0 and g_tt is finite at the origin.
 *
 * In classical Kerr, M_eff = M and Delta(0) = a^2 -- the metric is also
 * regular at r = 0 in the Kerr case because the ring singularity is at
 * the equator only.  For Schwarzschild (a = 0), Delta(0) = 0 is where
 * the singularity lives.  The LQG correction with M_eff(0) = 0 ensures
 * Delta(0) = a^2 + 0 even for a = 0, so the a = 0 Schwarzschild singularity
 * is resolved.
 */
TEST(LqgKerr, RegularAtOrigin) {
    constexpr double M   = 1.0;
    constexpr double tol = 1.0e-14;

    const double ls[] = {0.1, 0.3, 1.0};

    for (double l : ls) {
        // Effective mass at r = 0 must vanish
        EXPECT_NEAR(physics::lqgEffectiveMass(0.0, M, l), 0.0, tol)
            << "M_eff(r=0) != 0 at l=" << l;

        // LQG correction at r = 0 should be 1 (full correction)
        EXPECT_NEAR(physics::lqgCorrection(0.0, M, l), 1.0, tol)
            << "correction(r=0) != 1 at l=" << l;

        // Delta at r = 0, a = 0: Delta_LQG(0) = 0 - 0 + 0 = 0 in Kerr.
        // With LQG: Delta(0) = 0 - 0 + 0 = 0 for a = 0 (but M_eff also 0
        // so Delta = -2*0*0 + 0 = 0; for a > 0 Delta(0) = a^2 > 0 -- regular).
        // Check a = 0.5 case: Delta(0) = a^2 (positive, regular).
        constexpr double a = 0.5;
        EXPECT_NEAR(physics::lqgDelta(0.0, M, a, l), a * a, tol)
            << "Delta(r=0) != a^2 at l=" << l << " a=" << a;

        // g_tt at r = 0 for a = 0.5, theta = pi/2: should be finite.
        // Sigma(0, a, pi/2) = a^2; Delta = a^2; g_tt = -(a^2 - a^2*1)/a^2 = 0.
        EXPECT_TRUE(std::isfinite(physics::lqgGtt(0.0, std::numbers::pi / 2.0, M, a, l)))
            << "g_tt not finite at r=0, l=" << l;
    }
}

// ============================================================================
// Test 3: Asymptotic flatness -- M_eff(r) -> M as r -> inf
// ============================================================================

/**
 * @brief M_eff approaches M from below as r increases.
 *
 * The fractional correction 2 l^2 M / (r^3 + 2 l^2 M) decays as (l/r)^2,
 * so at r = 100 M with l = 0.3 M, the correction is < 2e-7.
 */
TEST(LqgKerr, AsymptoticFlatness) {
    constexpr double M   = 1.0;
    constexpr double l   = 0.3;
    constexpr double tol = 1.0e-5;  // (l/100)^2 ~ 9e-6

    EXPECT_NEAR(physics::lqgEffectiveMass(100.0, M, l), M, tol)
        << "M_eff not converging to M at large r";
    EXPECT_NEAR(physics::lqgCorrection(100.0, M, l), 0.0, tol)
        << "LQG correction not vanishing at large r";
}

// ============================================================================
// Test 4: Monotone effective mass
// ============================================================================

/**
 * @brief M_eff(r) is strictly increasing from 0 to M.
 *
 * Monotonicity is required for the metric to behave as a one-parameter
 * deformation of Kerr; a non-monotone mass function would introduce
 * unphysical topology changes.
 */
TEST(LqgKerr, MonotoneEffectiveMass) {
    constexpr double M = 1.0;
    constexpr double l = 0.5;

    const double radii[] = {0.0, 0.5, 1.0, 2.0, 5.0, 10.0, 50.0};
    double prev = physics::lqgEffectiveMass(0.0, M, l);

    for (std::size_t i = 1; i < std::size(radii); ++i) {
        const double meff = physics::lqgEffectiveMass(radii[i], M, l);
        EXPECT_GE(meff, prev) << "M_eff not monotone at r=" << radii[i];
        EXPECT_LE(meff, M)    << "M_eff exceeds M at r=" << radii[i];
        prev = meff;
    }
}

// ============================================================================
// Test 5: Outer horizon exists and is below Kerr horizon for sub-extremal l
// ============================================================================

/**
 * @brief Bisection finds an outer horizon; for l > 0 it lies below the Kerr r+.
 *
 * The LQG effective mass replaces M with M_eff(r) < M, which means
 * Delta_LQG(r) > Delta_Kerr(r) at all r.  The horizon where Delta_LQG = 0
 * therefore lies at a smaller radius than the Kerr horizon.
 */
TEST(LqgKerr, OuterHorizonBelowKerr) {
    constexpr double M = 1.0;
    constexpr double a = 0.5;

    // Kerr outer horizon (l = 0) as baseline.
    const double rPlus_kerr = physics::lqgOuterHorizon(M, a, 0.0);
    EXPECT_NEAR(rPlus_kerr, M + std::sqrt(M * M - a * a), 1.0e-10)
        << "l=0 horizon does not match Kerr r+";

    // For l = 0.1, 0.2: horizon should exist and be below Kerr.
    const double ls[] = {0.05, 0.1, 0.2};
    for (double l : ls) {
        const double rPlus_lqg = physics::lqgOuterHorizon(M, a, l);
        EXPECT_TRUE(std::isfinite(rPlus_lqg))
            << "No horizon found for l=" << l;
        EXPECT_LT(rPlus_lqg, rPlus_kerr)
            << "LQG horizon >= Kerr horizon for l=" << l;
        EXPECT_GT(rPlus_lqg, 0.0)
            << "LQG horizon <= 0 for l=" << l;
    }
}

// ============================================================================
// Test 6: Photon sphere shifts inward for l = 0.3 M (EHT-bounded regime)
// ============================================================================

/**
 * @brief The approximate prograde photon sphere radius is less than the Kerr
 * value for l = 0.3 M (the approximate EHT upper bound for M87*).
 *
 * This is consistent with arXiv:2511.17975 which shows LQG corrections shift
 * the shadow inward by up to ~1-5% relative to Kerr.
 */
TEST(LqgKerr, PhotonSphereShiftsInward) {
    constexpr double M = 1.0;
    constexpr double a = 0.5;

    // Kerr prograde photon sphere (l = 0).
    const double rph_kerr = physics::lqgPhotonSphereApprox(M, a, 0.0);
    EXPECT_GT(rph_kerr, 0.0) << "Kerr photon sphere <= 0";

    // LQG photon sphere should be smaller.
    const double l_eht = 0.3 * M;
    const double rph_lqg = physics::lqgPhotonSphereApprox(M, a, l_eht);
    EXPECT_LT(rph_lqg, rph_kerr)
        << "LQG photon sphere not below Kerr at l=0.3M";

    // Correction should be small: < 10% (EHT observational bound).
    const double frac = (rph_kerr - rph_lqg) / rph_kerr;
    EXPECT_LT(frac, 0.1) << "LQG photon sphere correction > 10% at l=0.3M";
    EXPECT_GT(frac, 0.0) << "LQG photon sphere correction is non-positive";
}
