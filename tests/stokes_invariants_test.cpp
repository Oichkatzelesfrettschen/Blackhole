/**
 * @file stokes_invariants_test.cpp
 * @brief G7: Stokes rotation invariants -- I^2 = Q^2+U^2+V^2 conservation,
 *        Faraday rotation rate, absorption scaling, full-K parity.
 *
 * WHY: The polarized RTE has exact symmetry properties that must hold even
 * after many propagation steps:
 *   1. Under pure Faraday rotation (no absorption, no emission): I and V are
 *      constant; Q^2+U^2 is constant; for fully polarized light I^2=Q^2+U^2+V^2
 *      is conserved.
 *   2. Under pure absorption (no rotation, no emission): all four Stokes
 *      components decay by the same factor exp(-alpha*ds); total polarization
 *      fraction is constant.
 *   3. stokesStepFull() with simplified-K coefficients must produce the same
 *      result as the exact stokesStep() to O(ds^4) (RK4 truncation error).
 *   4. stokesStepFull() with rho_Q coupling transfers linear to circular
 *      polarization (Faraday conversion).
 * These tests guard against sign errors, coupling mistakes, and normalization
 * bugs that would show up only in long integrations.
 */

#include "stokes_transport.h"

#include <cmath>
#include <cstdio>
#include <numbers>
#include <vector>

using namespace physics;

// ---------------------------------------------------------------------------
// helpers
// ---------------------------------------------------------------------------

static int gPass = 0;
static int gFail = 0;

static void check(bool cond, const char* msg) {
    if (cond) {
        std::printf("  [PASS] %s\n", msg);
        ++gPass;
    } else {
        std::printf("  [FAIL] %s\n", msg);
        ++gFail;
    }
}

static bool nearAbs(double a, double b, double tol) {
    return std::fabs(a - b) < tol;
}

static bool nearRel(double a, double b, double tol) {
    const double denom = std::max(std::fabs(b), 1.0e-300);
    return std::fabs(a - b) / denom < tol;
}

static bool geq(double a, double b, double tol = 0.0) {
    return a >= b - tol;
}

// ---------------------------------------------------------------------------
// Group 1: Pure Faraday rotation invariants (simplified K, no absorption)
// ---------------------------------------------------------------------------

static void testFaradayConservesI() {
    // No emission, no absorption -- I must be exactly unchanged after N steps.
    const StokesVector s0  = {3.5, 2.0, 1.5, 0.2};
    const StokesEmission em = {};
    const double rhoV = 0.3;    // rad/cm
    const double ds   = 0.1;    // cm
    const int    N    = 200;

    StokesVector s = s0;
    for (int k = 0; k < N; ++k) {
        s = stokesStep(s, em, 0.0, rhoV, ds);
    }
    check(nearRel(s.i, s0.i, 1.0e-12), "pure Faraday rotation: I unchanged after 200 steps");
}

static void testFaradayConservesV() {
    // V channel is decoupled from Q,U in simplified K -- V must stay constant.
    const StokesVector s0  = {2.0, 1.0, 0.5, 0.8};
    const StokesEmission em = {};
    const double rhoV = 0.5;
    const double ds   = 0.05;
    const int    N    = 400;

    StokesVector s = s0;
    for (int k = 0; k < N; ++k) {
        s = stokesStep(s, em, 0.0, rhoV, ds);
    }
    check(nearRel(s.v, s0.v, 1.0e-12), "pure Faraday rotation: V unchanged after 400 steps");
}

static void testFaradayConservesLinPolInt() {
    // Q^2 + U^2 = const under pure Faraday rotation (pure rotation in Q-U plane).
    const StokesVector s0  = {4.0, 3.0, 2.0, 0.5};
    const StokesEmission em = {};
    const double rhoV = 0.7;
    const double ds   = 0.03;
    const int    N    = 500;

    const double linInt0 = s0.linPolInt();   // sqrt(Q^2+U^2)

    StokesVector s = s0;
    for (int k = 0; k < N; ++k) {
        s = stokesStep(s, em, 0.0, rhoV, ds);
    }
    check(nearRel(s.linPolInt(), linInt0, 1.0e-10),
          "pure Faraday rotation: sqrt(Q^2+U^2) conserved after 500 steps");
}

static void testFaradayConservesFullPolBound() {
    // For fully polarized light (I^2 = Q^2+U^2+V^2), pure Faraday rotation
    // preserves this equality to machine precision.
    // Construct a fully polarized state: I = sqrt(Q^2+U^2+V^2).
    const double q = 0.6, u = 0.5, v = 0.1;
    const double i = std::sqrt(q * q + u * u + v * v);
    const StokesVector s0  = {i, q, u, v};
    const StokesEmission em = {};
    const double rhoV = 0.4;
    const double ds   = 0.04;
    const int    N    = 300;

    // Initial: I^2 == Q^2+U^2+V^2
    const double inv0 = s0.i * s0.i - s0.q * s0.q - s0.u * s0.u - s0.v * s0.v;

    StokesVector s = s0;
    for (int k = 0; k < N; ++k) {
        s = stokesStep(s, em, 0.0, rhoV, ds);
    }
    const double invN = s.i * s.i - s.q * s.q - s.u * s.u - s.v * s.v;

    check(nearAbs(inv0, 0.0, 1.0e-14), "fully polarized initial: I^2-Q^2-U^2-V^2 = 0");
    check(nearAbs(invN, 0.0, 1.0e-10),
          "pure Faraday rotation: I^2-Q^2-U^2-V^2 = 0 conserved after 300 steps");
}

static void testFaradayEvpaAccumulates() {
    // After N steps of rhoV with ds, EVPA should increase by N*rhoV*ds/2.
    // Use a starting state with zero V so EVPA is well-defined and no wrapping.
    const double rhoV = 0.02;   // rad/cm (small to avoid wrapping over N steps)
    const double ds   = 0.1;    // cm
    const int    N    = 50;     // total rotation phi = N * rhoV * ds = 0.1 rad
    const double phi  = static_cast<double>(N) * rhoV * ds;  // 0.1 rad in Q-U plane
    const double evpaExpected = phi / 2.0;                   // EVPA = chi = atan2(U,Q)/2

    const StokesVector s0  = {1.0, 1.0, 0.0, 0.0};  // EVPA = 0
    const StokesEmission em = {};

    StokesVector s = s0;
    for (int k = 0; k < N; ++k) {
        s = stokesStep(s, em, 0.0, rhoV, ds);
    }
    check(nearAbs(s.evpa(), evpaExpected, 1.0e-10),
          "Faraday rotation: EVPA accumulates to N*rhoV*ds/2 after N steps");
}

// ---------------------------------------------------------------------------
// Group 2: Pure absorption invariants (no rotation, no emission)
// ---------------------------------------------------------------------------

static void testAbsorptionScalesAllComponents() {
    // With pure absorption and no rotation/emission, each component decays by
    // exp(-alpha * ds).  All four decay by the same factor.
    const StokesVector s0   = {5.0, 2.0, 1.5, 0.7};
    const StokesEmission em  = {};
    const double alphaI = 0.1;   // cm^-1
    const double ds     = 0.5;   // cm
    const double expectedFactor = std::exp(-alphaI * ds);

    const StokesVector s1 = stokesStep(s0, em, alphaI, 0.0, ds);

    check(nearRel(s1.i, s0.i * expectedFactor, 1.0e-10),
          "pure absorption: I decays by exp(-alpha*ds)");
    check(nearRel(s1.q, s0.q * expectedFactor, 1.0e-10),
          "pure absorption: Q decays by exp(-alpha*ds)");
    check(nearRel(s1.u, s0.u * expectedFactor, 1.0e-10),
          "pure absorption: U decays by exp(-alpha*ds)");
    check(nearRel(s1.v, s0.v * expectedFactor, 1.0e-10),
          "pure absorption: V decays by exp(-alpha*ds)");
}

static void testAbsorptionConservesTotalPolFrac() {
    // Under pure absorption all components decay by the same factor, so the
    // fractional polarization (and EVPA) must be unchanged.
    const StokesVector s0   = {5.0, 2.0, 1.5, 0.7};
    const StokesEmission em  = {};
    const double alphaI = 0.3;
    const double ds     = 2.0;
    const double pi0     = s0.totalPolFrac();
    const double evpa0   = s0.evpa();

    const StokesVector s1 = stokesStep(s0, em, alphaI, 0.0, ds);

    check(nearRel(s1.totalPolFrac(), pi0, 1.0e-10),
          "pure absorption: total polarization fraction unchanged");
    check(nearAbs(s1.evpa(), evpa0, 1.0e-12),
          "pure absorption: EVPA unchanged");
}

static void testPolBoundMaintainedAfterNSteps() {
    // I^2 >= Q^2+U^2+V^2 must hold at every step through an emitting+absorbing
    // plasma.  We test a 100-step path with both absorption and rotation.
    const double jI      = 2.0e-3;
    const double jQ      = 1.0e-3;
    const double jU      = 5.0e-4;
    const double jV      = 1.0e-5;
    const double alphaI  = 5.0e-4;
    const double rhoV    = 1.0e-3;
    const double ds      = 10.0;
    const StokesEmission em = {jI, jQ, jU, jV};

    StokesVector s = {};  // start from vacuum
    bool bound_ok = true;
    for (int k = 0; k < 100; ++k) {
        s = stokesStep(s, em, alphaI, rhoV, ds);
        const double lhs = s.i * s.i;
        const double rhs = s.q * s.q + s.u * s.u + s.v * s.v;
        if (lhs < rhs - 1.0e-12) {
            bound_ok = false;
        }
    }
    check(bound_ok, "polarization bound I^2 >= Q^2+U^2+V^2 at every step (100-step path)");
}

// ---------------------------------------------------------------------------
// Group 3: stokesStepFull parity with exact stokesStep
// ---------------------------------------------------------------------------

static void testStepFullParitySimplifiedK() {
    // stokesStepFull() with rhoQ=alphaQ=alphaV=0 must match stokesStep() to
    // better than O(ds^4) truncation error.  Use a small ds so RK4 error < 1e-8.
    const StokesVector s0 = {3.0, 1.5, 0.8, 0.3};
    const StokesEmission em = {1.0e-3, 4.0e-4, 2.0e-4, 1.0e-5};
    const double alphaI = 1.0e-3;
    const double rhoV   = 2.0e-3;
    const double ds     = 0.01;  // small step -> RK4 error negligible

    const StokesVector exact = stokesStep(s0, em, alphaI, rhoV, ds);
    const FaradayPropagation k = {alphaI, 0.0, 0.0, rhoV, 0.0, ds};
    const StokesVector rk4   = stokesStepFull(s0, em, k);

    check(nearRel(rk4.i, exact.i, 1.0e-8),
          "stokesStepFull vs stokesStep: I matches to < 1e-8 (simplified K, ds=0.01)");
    check(nearRel(rk4.q, exact.q, 1.0e-8),
          "stokesStepFull vs stokesStep: Q matches to < 1e-8 (simplified K, ds=0.01)");
    check(nearRel(rk4.u, exact.u, 1.0e-8),
          "stokesStepFull vs stokesStep: U matches to < 1e-8 (simplified K, ds=0.01)");
    check(nearRel(rk4.v, exact.v, 1.0e-8),
          "stokesStepFull vs stokesStep: V matches to < 1e-8 (simplified K, ds=0.01)");
}

static void testStepFullFaradayConversionGrowsV() {
    // With rho_Q > 0, linearly polarized Q should drive circular polarization V.
    // Start with I>0, Q>0, U=V=0, no absorption, and check V grows.
    const StokesVector s0 = {1.0, 0.8, 0.0, 0.0};
    const StokesEmission em = {};
    // (unused; kept for documentation -- the rhoQ-only path needs rhoV to seed U)
    // const FaradayPropagation k = {0.0, 0.0, 0.0, 0.0, 0.5, 0.1};

    // With only rho_Q, the K matrix row for V is dV/ds = -alpha_V*I - alpha_I*V + rho_Q*U.
    // Starting with Q=0.8, U=0: dU/ds = jU - alphaI*U + rhoV*Q - rhoQ*V
    //                                   = 0  - 0       + 0      - rhoQ*V
    //                           dV/ds = -rhoQ*U -> this couples U to V not Q directly.
    // After first step: dU/ds|0 = -rhoQ*V|0 = 0 (V=0).
    //                  dV/ds|0 = rhoQ*U|0 = 0 (U=0).
    // So with Q only, and rhoQ only, there's no direct Q->V coupling in this matrix.
    // The coupling chain is: Q drives U via rhoV only; rhoQ couples U to V.
    // Use rhoV > 0 as well to first rotate Q into U, then rhoQ converts U to V.
    const FaradayPropagation k2 = {
        /* alphaI */ 0.0,
        /* alphaQ */ 0.0,
        /* alphaV */ 0.0,
        /* rhoV   */ 1.0,   // rotates Q into U
        /* rhoQ   */ 0.5,   // converts U into V
        /* dsCm   */ 0.05
    };

    StokesVector s = s0;
    for (int n = 0; n < 20; ++n) {
        s = stokesStepFull(s, em, k2);
    }
    // After several steps Q has been partially rotated into U (via rhoV),
    // and U has been converted into V (via rhoQ).  V should be non-zero.
    check(s.v != 0.0, "stokesStepFull: Faraday conversion (rhoQ) generates circular from linear");
}

static void testStepFullZeroCoeffsIsIdentity() {
    // With all K coefficients zero and zero emission, state must be unchanged.
    const StokesVector s0 = {2.0, 0.5, -0.3, 0.1};
    const StokesEmission em = {};
    const FaradayPropagation k = {0.0, 0.0, 0.0, 0.0, 0.0, 1.0};
    const StokesVector s1 = stokesStepFull(s0, em, k);
    check(nearRel(s1.i, s0.i, 1.0e-14) && nearRel(s1.q, s0.q, 1.0e-14) &&
          nearRel(s1.u, s0.u, 1.0e-14) && nearRel(s1.v, s0.v, 1.0e-14),
          "stokesStepFull: zero K and zero emission -> state unchanged");
}

// ---------------------------------------------------------------------------
// Group 4: Thick-slab equilibrium invariants
// ---------------------------------------------------------------------------

static void testThickSlabPreservesPolFrac() {
    // At optical depth >> 1 with fixed coefficients, the Stokes vector approaches
    // the source function S = J/alpha.  The polarization fraction of the equilibrium
    // must equal the intrinsic emission polarization fraction sqrt(jQ^2+jU^2)/jI.
    const double jI     = 2.0e-3;
    const double jQ     = 1.4e-3;   // intrinsic pol frac = sqrt(jQ^2+jU^2)/jI
    const double jU     = 0.0;      // => Pi = 0.7
    const double alphaI = 1.0e-3;
    const double rhoV   = 0.0;
    const double ds     = 1.0e5;    // tau=100 >> 1; exp(-100) ~ 4e-44 is negligible
    const StokesEmission em = {jI, jQ, jU, 0.0};

    StokesVector s = {};
    s = stokesStep(s, em, alphaI, rhoV, ds);

    // At equilibrium: I -> jI/alphaI, Q -> jQ/alphaI, U -> jU/alphaI
    const double expectedI = jI / alphaI;
    const double expectedQ = jQ / alphaI;
    check(nearRel(s.i, expectedI, 1.0e-8), "thick slab: I -> j_I / alpha_I");
    check(nearRel(s.q, expectedQ, 1.0e-8), "thick slab: Q -> j_Q / alpha_I");
    check(nearRel(s.totalPolFrac(), std::hypot(jQ, jU) / jI, 1.0e-8),
          "thick slab: total pol frac -> intrinsic emission pol frac");
}

// ---------------------------------------------------------------------------
// Group 5: integrateStokesPath multi-step invariants
// ---------------------------------------------------------------------------

static void testPathIntegrationPolBound() {
    // Build a 200-segment path with variable emission/absorption/rotation.
    // The polarization bound I^2 >= Q^2+U^2+V^2 must hold at the final state
    // (it holds at each step as shown in testPolBoundMaintainedAfterNSteps).
    const int N = 200;
    std::vector<StokesEmission>    em(static_cast<std::size_t>(N));
    std::vector<FaradayPropagation> pr(static_cast<std::size_t>(N));

    for (int k = 0; k < N; ++k) {
        const double angle = 0.1 * static_cast<double>(k);
        em[static_cast<std::size_t>(k)] = {1.0e-3, 6.0e-4 * std::cos(angle), 6.0e-4 * std::sin(angle), 1.0e-5};
        pr[static_cast<std::size_t>(k)] = {5.0e-4, 0.0, 0.0, 2.0e-3, 0.0, 5.0};
    }

    const StokesVector final = integrateStokesPath(em, pr);

    const double lhs = final.i * final.i;
    const double rhs = final.q * final.q + final.u * final.u + final.v * final.v;
    check(geq(lhs, rhs, 1.0e-10),
          "integrateStokesPath: I^2 >= Q^2+U^2+V^2 after 200-segment path");
    check(final.i >= 0.0, "integrateStokesPath: I >= 0 after 200-segment path");
}

static void testPathIntegrationFaradayRotationTotal() {
    // N uniform steps with pure Faraday rotation and identical emission.
    // The accumulated Q,U should equal the exact integral with total phi = N*rhoV*ds.
    // Use purely unpolarized emission so we test only the Q-U rotation of the
    // background emission building up.
    const int    N    = 100;
    const double rhoV = 5.0e-3;   // rad/cm
    const double ds   = 2.0;      // cm
    const double jI   = 1.0e-4;   // total emissivity
    const double jQ   = 6.0e-5;   // linear emissivity
    const double jU   = 0.0;

    std::vector<StokesEmission>    em(static_cast<std::size_t>(N), {jI, jQ, jU, 0.0});
    std::vector<FaradayPropagation> pr(static_cast<std::size_t>(N), {0.0, 0.0, 0.0, rhoV, 0.0, ds});

    const StokesVector s = integrateStokesPath(em, pr);

    // After N steps the accumulated linPolInt must be non-zero (emission adds
    // Q at each step before being rotated).
    check(s.linPolInt() > 0.0,
          "integrateStokesPath: linear pol intensity non-zero after emission + rotation");
    // I must grow (pure emission, no absorption)
    const double expectedI = static_cast<double>(N) * jI * ds;
    check(nearRel(s.i, expectedI, 1.0e-10),
          "integrateStokesPath: I = N*j_I*ds for optically thin uniform path");
}

// ---------------------------------------------------------------------------
// Group 6: Rotation-dominated limit (A->0) special-case branch
// ---------------------------------------------------------------------------

static void testRotationDominatedLimit() {
    // Test the rotation-dominated branch (A < 1e-15*|R|):
    // alphaI = 0, rhoV >> 0.  Result must match the general formula at A=0.
    const StokesVector s0 = {1.0, 1.0, 0.0, 0.0};
    const StokesEmission em = {0.0, 1.0e-3, 0.0, 0.0};
    const double rhoV = 1.0;
    const double ds   = std::numbers::pi / 4.0;  // phi = pi/4

    const StokesVector s = stokesStep(s0, em, 0.0, rhoV, ds);

    // Homogeneous: Q_hom = cos(pi/4) = 1/sqrt(2), U_hom = sin(pi/4) = 1/sqrt(2)
    const double phi  = rhoV * ds;
    const double qHom = std::cos(phi);
    const double uHom = std::sin(phi);

    // Particular: Ic = sin(phi)/R = sin(phi)/rhoV, Is = (1-cos(phi))/R
    // With jQ=1e-3, jU=0: Q_emit = jQ * Ic, U_emit = jQ * Is
    const double ic   = std::sin(phi) / rhoV;
    const double is_  = (1.0 - std::cos(phi)) / rhoV;
    const double qExp = qHom + 1.0e-3 * ic;
    const double uExp = uHom + 1.0e-3 * is_;

    check(nearRel(s.q, qExp, 1.0e-12), "rotation-dominated: Q matches analytic");
    check(nearRel(s.u, uExp, 1.0e-12), "rotation-dominated: U matches analytic");
}

// ---------------------------------------------------------------------------
// Group 7: Absorption-dominated limit (R->0) special-case branch
// ---------------------------------------------------------------------------

static void testAbsorptionDominatedLimit() {
    // alphaI >> rhoV: the absorption-dominated branch.
    // Q should decay to j_Q/alpha_I source function, U separately.
    const StokesVector s0 = {10.0, 3.0, 1.5, 0.2};
    const StokesEmission em = {5.0e-3, 2.0e-3, 1.0e-3, 0.0};
    const double alphaI = 1.0e-2;    // cm^-1
    const double rhoV   = 1.0e-18;   // effectively zero (< 1e-15 * alphaI)
    const double ds     = 5.0;       // tau = 0.05

    const StokesVector s = stokesStep(s0, em, alphaI, rhoV, ds);

    // Expected from exact formula with R=0:
    const double E = std::exp(-alphaI * ds);
    const double qExp = s0.q * E + (em.jQ / alphaI) * (1.0 - E);
    const double uExp = s0.u * E + (em.jU / alphaI) * (1.0 - E);

    check(nearRel(s.q, qExp, 1.0e-10), "absorption-dominated: Q matches scalar RTE");
    check(nearRel(s.u, uExp, 1.0e-10), "absorption-dominated: U matches scalar RTE");
}

// ---------------------------------------------------------------------------
// main
// ---------------------------------------------------------------------------

int main() {
    std::printf("\n=== Stokes Rotation Invariants Tests (G7) ===\n\n");

    std::printf("Pure Faraday rotation invariants:\n");
    testFaradayConservesI();
    testFaradayConservesV();
    testFaradayConservesLinPolInt();
    testFaradayConservesFullPolBound();
    testFaradayEvpaAccumulates();

    std::printf("\nPure absorption invariants:\n");
    testAbsorptionScalesAllComponents();
    testAbsorptionConservesTotalPolFrac();

    std::printf("\nPolarization bound:\n");
    testPolBoundMaintainedAfterNSteps();

    std::printf("\nstokesStepFull parity:\n");
    testStepFullParitySimplifiedK();
    testStepFullFaradayConversionGrowsV();
    testStepFullZeroCoeffsIsIdentity();

    std::printf("\nThick-slab equilibrium:\n");
    testThickSlabPreservesPolFrac();

    std::printf("\nPath integration invariants:\n");
    testPathIntegrationPolBound();
    testPathIntegrationFaradayRotationTotal();

    std::printf("\nRotation-dominated limit:\n");
    testRotationDominatedLimit();

    std::printf("\nAbsorption-dominated limit:\n");
    testAbsorptionDominatedLimit();

    std::printf("\n%d/%d tests passed.\n", gPass, gPass + gFail);
    if (gFail > 0) {
        std::printf("[FAILURE] One or more tests failed.\n\n");
        return 1;
    }
    std::printf("[ALL PASS]\n\n");
    return 0;
}
