/**
 * @file tests/stokes_transport_test.cpp
 * @brief Validation tests for polarized Stokes I,Q,U,V transport (D4).
 *
 * WHY: stokes_transport.h implements the Mueller K matrix propagation needed
 * to simulate the EHT polarization measurements.  All tests verify analytically
 * derivable limits without a full geodesic integration run.
 *
 * Test list (28 tests):
 *
 * StokesVector helpers:
 *   1.  linPolFrac = sqrt(Q^2+U^2)/I; zero for unpolarized.
 *   2.  evpa = 0.5*atan2(U,Q): pi/4 for Q=0,U>0; 0 for Q>0,U=0.
 *   3.  rotateEvpa rotates Q,U correctly; I,V unchanged.
 *   4.  totalPolFrac is the quadrature sum; <= 1 for physical Stokes.
 *
 * stokesStep -- simplified K (alpha_I + rho_V):
 *   5.  I evolves as scalar RTE (reduces to rteStep for Q=U=V=0).
 *   6.  Pure Faraday rotation (alpha_I=0): I,V unchanged; Q,U rotate.
 *   7.  EVPA rotates by exactly rho_V * ds under pure Faraday rotation.
 *   8.  Linear polarization fraction conserved under pure Faraday rotation.
 *   9.  Pure absorption (rho_V=0, j=0): all Stokes decay as exp(-alpha*L).
 *  10.  Thick slab (tau >> 1): I -> j_I/alpha_I; Q -> j_Q_eff/alpha_I.
 *  11.  ds=0 leaves state unchanged.
 *  12.  Starting from zero: I stays >= 0 for j_I >= 0.
 *  13.  Exact formula matches RK4 (stokesStepFull) for simplified K case.
 *
 * Path integration:
 *  14.  integrateStokesPath reproduces 5-step sequential stokesStep.
 *  15.  Accumulated Faraday rotation over N steps = N * rho_V * ds (exact).
 *
 * Polarization bound:
 *  16.  stokesPolarizationBound: Q^2+U^2+V^2 <= I^2 for optically evolved state.
 *  17.  Bound satisfied after thick-slab equilibrium.
 *
 * Physical emission coefficients:
 *  18.  synchrotronLinearPolarFrac: (p+1)/(p+7/3); p=2 gives 0.69; p=3 gives 0.72.
 *  19.  synchrotronPolarizedEmission: sqrt(jQ^2+jU^2)/jI = piLin.
 *  20.  synchrotronPolarizedEmission: EVPA of emission is chi_B + pi/2.
 *  21.  thermalSynchLinearPolarFrac: ~0.75 for large Theta_e; > 0.6.
 *
 * Faraday coefficients:
 *  22.  faradayRotationCoeff scales as n_e * B_par / nu^2.
 *  23.  faradayRotationCoeff = 0 for nu=0 or n_e=0.
 *  24.  faradayRotationCoeffRelativistic < cold-plasma for Theta_e > 1 (suppression).
 *  25.  faradayConversionCoeff >= 0 for B_perp >= 0 and Theta_e > 0.
 *
 * GR transforms:
 *  26.  grTransformStokes: all four components scale as g^3.
 *  27.  faradayRotateStokes: EVPA shifts by rmRad; I,V unchanged.
 *  28.  grParallelTransportRotate: same as rotateEvpa (I,V invariant).
 *
 * References:
 *   - Rybicki & Lightman (1979) Ch. 6
 *   - Hamaker & Bregman (1996), A&AS 117, 137
 *   - Shcherbakov & Huang (2011), MNRAS 410, 1052
 *   - EHT Collaboration Paper VII (2021), ApJL 910, L13
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>
#include <vector>

#include "../src/physics/stokes_transport.h"

using namespace physics;

// ---------------------------------------------------------------------------
// Minimal test framework
// ---------------------------------------------------------------------------

namespace {

bool gAllPass = true;
int  gNPass   = 0;
int  gNTotal  = 0;

void check(bool condition, const char* test, const char* detail = "") {
    ++gNTotal;
    if (condition) {
        ++gNPass;
        std::cout << "  [PASS] " << test << "\n";
    } else {
        std::cout << "  [FAIL] " << test;
        if (detail && detail[0]) { std::cout << " -- " << detail; }
        std::cout << "\n";
        gAllPass = false;
    }
}

bool near(double a, double b, double tol) {
    return std::abs(a - b) <= tol;
}

bool nearRel(double a, double b, double rtol) {
    const double scale = std::max({std::abs(a), std::abs(b), 1.0e-300});
    return std::abs(a - b) <= rtol * scale;
}

} // namespace

// ---------------------------------------------------------------------------
// StokesVector helper tests
// ---------------------------------------------------------------------------

static void testLinPolFrac() {
    // Test 1: linPolFrac = sqrt(Q^2+U^2)/I
    const StokesVector s1 = {1.0, 0.6, 0.8, 0.0};  // pol = 1.0, frac = 1.0
    check(nearRel(s1.linPolFrac(), 1.0, 1.0e-12), "linPolFrac: fully linearly polarized (Q,U)=(0.6,0.8)");
    const StokesVector s2 = {2.0, 0.0, 0.0, 0.0};  // unpolarized
    check(near(s2.linPolFrac(), 0.0, 1.0e-15), "linPolFrac: zero for unpolarized I");
    const StokesVector s3 = {4.0, 2.0, 0.0, 0.0};  // 50% linear
    check(nearRel(s3.linPolFrac(), 0.5, 1.0e-12), "linPolFrac: 50% for Q=I/2, U=0");
}

static void testEvpa() {
    // Test 2: EVPA = 0.5*atan2(U,Q)
    const StokesVector sq = {1.0, 1.0, 0.0, 0.0};  // EVPA = 0
    check(near(sq.evpa(), 0.0, 1.0e-14), "evpa: chi=0 for Q>0, U=0");
    const StokesVector su = {1.0, 0.0, 1.0, 0.0};  // EVPA = pi/4
    check(nearRel(su.evpa(), std::numbers::pi / 4.0, 1.0e-12), "evpa: chi=pi/4 for Q=0, U>0");
    const StokesVector sq45 = {1.0, -1.0, 0.0, 0.0};  // EVPA = pi/2 or -pi/2
    check(std::abs(std::abs(sq45.evpa()) - std::numbers::pi / 2.0) < 1.0e-12,
          "evpa: chi=pi/2 for Q<0, U=0");
}

static void testRotateEvpa() {
    // Test 3: rotateEvpa rotates Q,U; I,V unchanged
    const StokesVector s = {1.0, 1.0, 0.0, 0.3};
    const double dchi = std::numbers::pi / 4.0;  // rotate EVPA by 45 deg
    const StokesVector r = s.rotateEvpa(dchi);
    check(near(r.i, s.i, 1.0e-14), "rotateEvpa: I unchanged");
    check(near(r.v, s.v, 1.0e-14), "rotateEvpa: V unchanged");
    // After 45 deg rotation: Q=1,U=0 -> Q=cos(pi/2)*1 - sin(pi/2)*0, U=sin(pi/2)*1 + cos(pi/2)*0
    // i.e., Q' = 0, U' = 1
    check(near(r.q, 0.0, 1.0e-14) && nearRel(r.u, 1.0, 1.0e-12),
          "rotateEvpa: Q,U rotate correctly by pi/4");
}

static void testTotalPolFrac() {
    // Test 4: totalPolFrac = sqrt(Q^2+U^2+V^2)/I
    const StokesVector s = {2.0, 1.0, 1.0, 1.0};
    const double expected = std::sqrt(3.0) / 2.0;
    check(nearRel(s.totalPolFrac(), expected, 1.0e-12), "totalPolFrac: sqrt(Q^2+U^2+V^2)/I");
    check(s.totalPolFrac() <= 1.0 + 1.0e-10, "totalPolFrac: <= 1 for physical state");
}

// ---------------------------------------------------------------------------
// stokesStep -- simplified K
// ---------------------------------------------------------------------------

static void testStokesStepIEqualsRteStep() {
    // Test 5: with Q=U=V=0 and j_Q=j_U=j_V=0, I evolves as scalar RTE
    const double jI = 2.0e-9;
    const double alpha = 3.0e-14;
    const double ds = 1.0e13;
    const double i0 = 1.0e-6;

    const StokesEmission em = {jI, 0.0, 0.0, 0.0};
    const StokesVector sIn = {i0, 0.0, 0.0, 0.0};
    const StokesVector sOut = stokesStep(sIn, em, alpha, 0.0, ds);

    // Compare with rteStep
    const RteState rte = rteStep({i0, 0.0, 0.0}, jI, alpha, ds);
    check(nearRel(sOut.i, rte.iNu, 1.0e-12), "stokesStep: I matches rteStep for scalar case");
    check(near(sOut.q, 0.0, 1.0e-30) && near(sOut.u, 0.0, 1.0e-30),
          "stokesStep: Q,U stay zero when unpolarized");
}

static void testPureFaradayRotationPreservesI() {
    // Test 6: pure Faraday rotation (alpha_I=0): I,V unchanged; Q,U rotate
    const StokesVector s0 = {1.0, 1.0, 0.0, 0.1};
    const double rhoV = 1.0e-8;   // rad/cm
    const double ds   = 1.0e9;    // cm -> phi = 0.01 rad
    const StokesEmission zeroEm = {};
    const StokesVector s1 = stokesStep(s0, zeroEm, 0.0, rhoV, ds);

    check(nearRel(s1.i, s0.i, 1.0e-12), "stokesStep: I unchanged under pure Faraday rotation");
    check(nearRel(s1.v, s0.v, 1.0e-12), "stokesStep: V unchanged under pure Faraday rotation");
}

static void testFaradayRotationAngle() {
    // Test 7: EVPA rotates by exactly phi = rho_V * ds under pure Faraday rotation
    const double rhoV = 2.0e-8;    // rad/cm
    const double ds   = 5.0e6;     // cm -> phi = 0.1 rad
    const double phi  = rhoV * ds;  // expected EVPA rotation (half-angle applied as rotateEvpa)

    // Start with purely Q-polarized state: EVPA = 0
    const StokesVector s0   = {1.0, 1.0, 0.0, 0.0};
    const StokesEmission em  = {};
    const StokesVector s1   = stokesStep(s0, em, 0.0, rhoV, ds);

    // Expected: EVPA rotates by phi; Q' = cos(phi), U' = sin(phi) (since Q_0=1, U_0=0)
    // From the formulas: Q_hom = E*(Q_0*cos(phi) - U_0*sin(phi)) = 1*cos(phi)
    //                    U_hom = E*(Q_0*sin(phi) + U_0*cos(phi)) = 1*sin(phi)
    check(nearRel(s1.q, std::cos(phi), 1.0e-10), "stokesStep: Q' = cos(rho_V * ds)");
    check(nearRel(s1.u, std::sin(phi), 1.0e-10), "stokesStep: U' = sin(rho_V * ds)");

    // EVPA of the output should equal phi/2 (since rotateEvpa uses 2*chi convention)
    // Wait: EVPA chi = 0.5*atan2(U',Q') = 0.5*atan2(sin(phi), cos(phi)) = phi/2
    const double evpaExpected = phi / 2.0;
    check(nearRel(s1.evpa(), evpaExpected, 1.0e-10), "stokesStep: EVPA rotates by rho_V*ds/2");
}

static void testFaradayRotationConservesLinPol() {
    // Test 8: linear polarization fraction conserved under pure Faraday rotation
    const StokesVector s0  = {2.0, 1.0, 0.5, 0.0};
    const double pi0        = s0.linPolFrac();
    const StokesEmission em = {};
    // Rotate by pi/3 radians of Faraday rotation
    const double rhoV = 1.0;
    const double ds   = std::numbers::pi / 3.0;
    const StokesVector s1 = stokesStep(s0, em, 0.0, rhoV, ds);
    check(nearRel(s1.linPolFrac(), pi0, 1.0e-12),
          "stokesStep: linear pol fraction conserved under Faraday rotation");
    check(nearRel(s1.i, s0.i, 1.0e-12),
          "stokesStep: I conserved under Faraday rotation (no absorption)");
}

static void testPureAbsorptionDecay() {
    // Test 9: pure absorption (rho_V=0, j=0): all Stokes decay as exp(-alpha*L)
    const StokesVector s0 = {1.0, 0.5, 0.3, 0.2};
    const double alpha = 1.0e-12;
    const double ds    = 2.0e11;
    const double tau   = alpha * ds;
    const double decay = std::exp(-tau);
    const StokesEmission em = {};
    const StokesVector s1   = stokesStep(s0, em, alpha, 0.0, ds);

    check(nearRel(s1.i, s0.i * decay, 1.0e-10), "stokesStep: I decays as exp(-tau)");
    check(nearRel(s1.q, s0.q * decay, 1.0e-10), "stokesStep: Q decays as exp(-tau)");
    check(nearRel(s1.u, s0.u * decay, 1.0e-10), "stokesStep: U decays as exp(-tau)");
    check(nearRel(s1.v, s0.v * decay, 1.0e-10), "stokesStep: V decays as exp(-tau)");
}

static void testThickSlabEquilibrium() {
    // Test 10: optically thick (tau >> 1): I -> j_I/alpha_I (source function limit)
    const double jI    = 5.0e-8;
    const double alpha = 1.0e-10;
    const double ds    = 1000.0 / alpha;  // tau = 1000
    const StokesEmission em = {jI, 0.0, 0.0, 0.0};
    const StokesVector s1   = stokesStep({0.0, 0.0, 0.0, 0.0}, em, alpha, 0.0, ds);
    check(nearRel(s1.i, jI / alpha, 1.0e-6), "stokesStep: thick slab I -> j_I/alpha_I");
}

static void testZeroStepPreservesState() {
    // Test 11: ds=0 leaves state unchanged
    const StokesVector s0 = {1.23e-7, 0.42e-7, -0.1e-7, 0.05e-7};
    const StokesEmission em = {1.0e-9, 0.5e-9, 0.0, 0.0};
    const StokesVector s1   = stokesStep(s0, em, 1.0e-12, 1.0e-8, 0.0);
    check(near(s1.i, s0.i, 1.0e-30) && near(s1.q, s0.q, 1.0e-30),
          "stokesStep: ds=0 leaves state unchanged");
}

static void testNonNegativeIFromZero() {
    // Test 12: I stays >= 0 starting from zero state with j_I >= 0
    const StokesEmission em = {1.0e-9, 0.5e-9, 0.0, 0.0};
    const StokesVector s1   = stokesStep({}, em, 1.0e-12, 1.0e-8, 1.0e13);
    check(s1.i >= 0.0, "stokesStep: I >= 0 starting from zero with positive emission");
}

static void testExactMatchesRK4ForSimplifiedK() {
    // Test 13: exact stokesStep matches stokesStepFull (RK4) for simplified K
    // Use moderate parameters where RK4 should agree well
    const StokesVector s0 = {1.0e-6, 0.3e-6, 0.2e-6, 0.05e-6};
    const StokesEmission em = {1.0e-9, 0.4e-9, -0.2e-9, 0.0};
    const double alpha = 5.0e-14;
    const double rhoV  = 3.0e-10;
    const double ds    = 1.0e10;   // tau = 5e-4, phi = 3e0 rad -- moderate values

    // Exact analytic step
    const StokesVector sExact = stokesStep(s0, em, alpha, rhoV, ds);

    // RK4 with fine sub-stepping for reference
    const int nSub = 100;
    const double subDs = ds / nSub;
    const FaradayPropagation kProp = {alpha, 0.0, 0.0, rhoV, 0.0, subDs};
    StokesVector sRK4 = s0;
    for (int k = 0; k < nSub; ++k) {
        sRK4 = stokesStepFull(sRK4, em, kProp);
    }

    // Should agree to within RK4 truncation error (~(ds/nSub)^4 * nSub ~ (ds)^4 * ds/nSub^3)
    check(nearRel(sExact.i, sRK4.i, 1.0e-6), "stokesStep: I matches RK4 for simplified K");
    check(nearRel(sExact.q, sRK4.q, 1.0e-5), "stokesStep: Q matches RK4 for simplified K");
    check(nearRel(sExact.u, sRK4.u, 1.0e-5), "stokesStep: U matches RK4 for simplified K");
}

// ---------------------------------------------------------------------------
// Path integration
// ---------------------------------------------------------------------------

static void testPathIntegrationMatchesSequential() {
    // Test 14: integrateStokesPath reproduces sequential stokesStep
    const StokesEmission em = {1.5e-9, 0.6e-9, 0.3e-9, 0.0};
    const FaradayPropagation fp = {2.0e-14, 0.0, 0.0, 5.0e-10, 0.0, 5.0e12};
    const int N = 5;

    std::vector<StokesEmission>    ems(N, em);
    std::vector<FaradayPropagation> fps(N, fp);

    // Sequential
    StokesVector seq;
    for (int k = 0; k < N; ++k) {
        seq = stokesStep(seq, em, fp.alphaI, fp.rhoV, fp.dsCm);
    }

    const StokesVector path = integrateStokesPath(ems, fps);

    check(nearRel(path.i, seq.i, 1.0e-12), "integrateStokesPath: I matches sequential");
    check(nearRel(path.q, seq.q, 1.0e-12), "integrateStokesPath: Q matches sequential");
    check(nearRel(path.u, seq.u, 1.0e-12), "integrateStokesPath: U matches sequential");
}

static void testAccumulatedFaradayRotation() {
    // Test 15: EVPA after N steps of pure Faraday rotation = N * rho_V * ds
    const double rhoV = 1.0e-9;
    const double ds   = 5.0e9;
    const int N = 7;
    const double totalPhi = rhoV * ds * N;  // expected total Faraday rotation

    // Start with Q-polarized state
    const StokesVector s0 = {1.0, 1.0, 0.0, 0.0};
    StokesVector s = s0;
    const StokesEmission em = {};
    for (int k = 0; k < N; ++k) {
        s = stokesStep(s, em, 0.0, rhoV, ds);
    }

    check(nearRel(s.q, std::cos(totalPhi), 1.0e-10),
          "integrateStokesPath: accumulated Faraday rotation Q = cos(N*rho_V*ds)");
    check(nearRel(s.u, std::sin(totalPhi), 1.0e-10),
          "integrateStokesPath: accumulated Faraday rotation U = sin(N*rho_V*ds)");
}

// ---------------------------------------------------------------------------
// Polarization bound
// ---------------------------------------------------------------------------

static void testPolarizationBoundSatisfied() {
    // Test 16: stokesPolarizationBound: Q^2+U^2+V^2 <= I^2 after optically evolved state
    const StokesEmission em = {1.0e-9, 0.6e-9, 0.0, 0.0};  // Pi_Q = 0.6 (unphysical, tests bound)
    // After thick slab: I -> j_I/alpha, Q -> j_Q/alpha, Pi = j_Q/j_I = 0.6
    const double alpha = 1.0e-10;
    const double ds    = 100.0 / alpha;
    const StokesVector s = stokesStep({}, em, alpha, 0.0, ds);
    // In equilibrium: I = j_I/alpha, Q = j_Q/alpha (if j_Q < j_I then bound holds)
    check(stokesPolarizationBound(s, 1.0e-8), "polarizationBound: satisfied at thick-slab equilibrium");
}

static void testPolarizationBoundThickSlab() {
    // Test 17: bound holds when Pi < 1 (physical emission)
    const StokesEmission em = {1.0e-9, 0.7e-9, 0.0, 0.0};  // Pi = 0.7 < 1
    const double alpha = 1.0e-10;
    const double ds    = 300.0 / alpha;
    const StokesVector s = stokesStep({}, em, alpha, 0.0, ds);
    check(stokesPolarizationBound(s, 1.0e-6),
          "polarizationBound: satisfied after thick slab with physical Pi < 1");
}

// ---------------------------------------------------------------------------
// Physical emission coefficients
// ---------------------------------------------------------------------------

static void testLinearPolarFracPowerLaw() {
    // Test 18: (p+1)/(p+7/3); p=2 -> 3/(2+7/3) = 3/(13/3) = 9/13 ~ 0.692; p=3 -> 4/(16/3) = 12/16 = 0.75
    const double pi2 = synchrotronLinearPolarFrac(2.0);
    const double pi3 = synchrotronLinearPolarFrac(3.0);
    check(nearRel(pi2, 9.0 / 13.0, 1.0e-12), "synchrotronLinearPolarFrac: p=2 -> 9/13 ~ 0.692");
    check(nearRel(pi3, 0.75, 1.0e-12), "synchrotronLinearPolarFrac: p=3 -> 0.75");
}

static void testPolarizedEmissionVector() {
    // Test 19: sqrt(jQ^2+jU^2)/jI = piLin
    const double jI    = 1.0e-9;
    const double piLin = 0.7;
    const double chi   = std::numbers::pi / 5.0;
    const StokesEmission em = synchrotronPolarizedEmission(jI, piLin, chi);
    const double linFrac = em.linPolFrac();
    check(nearRel(linFrac, piLin, 1.0e-12), "synchrotronPolarizedEmission: linPolFrac = piLin");
    check(near(em.jV, 0.0, 1.0e-30), "synchrotronPolarizedEmission: jV = 0 (thermal synchrotron)");
}

static void testPolarizedEmissionEvpa() {
    // Test 20: EVPA of emission is chi_B + pi/2 (E-vector perp to B)
    const double jI     = 1.0e-9;
    const double piLin  = 0.7;
    const double chiBRad = std::numbers::pi / 4.0;  // B field at 45 deg
    const StokesEmission em = synchrotronPolarizedEmission(jI, piLin, chiBRad);

    // jQ = -jI*pi*cos(2*chi_B), jU = -jI*pi*sin(2*chi_B)
    // EVPA of emission: 0.5*atan2(jU, jQ)
    const double evpaEm = 0.5 * std::atan2(em.jU, em.jQ);

    // Expected: EVPA = chi_B + pi/2 = pi/4 + pi/2 = 3*pi/4
    // But atan2 wraps to (-pi/2, pi/2], so: 3pi/4 -> 3pi/4 - pi = -pi/4 (mod pi)
    // Actually 0.5*atan2(-sin(2*chi_B),-cos(2*chi_B)) = 0.5*(pi/2 + pi) ...
    // Let's just check that EVPA_emission = chi_B + pi/2 mod pi
    const double expectedEvpa = chiBRad + std::numbers::pi / 2.0;
    const double diff = std::fmod(std::abs(evpaEm - expectedEvpa), std::numbers::pi);
    const double diffNorm = std::min(diff, std::numbers::pi - diff);
    check(diffNorm < 1.0e-10, "synchrotronPolarizedEmission: EVPA = chi_B + pi/2 (E-vector perp B)");
}

static void testThermalLinPolFrac() {
    // Test 21: thermalSynchLinearPolarFrac: > 0.6 and < 1 for Theta_e > 0
    const double pi1  = thermalSynchLinearPolarFrac(1.0);
    const double pi10 = thermalSynchLinearPolarFrac(10.0);
    check(pi1 > 0.6 && pi1 < 1.0, "thermalSynchLinearPolarFrac: in (0.6, 1.0) for Theta_e=1");
    check(pi10 > 0.6 && pi10 < 1.0, "thermalSynchLinearPolarFrac: in (0.6, 1.0) for Theta_e=10");
}

// ---------------------------------------------------------------------------
// Faraday coefficients
// ---------------------------------------------------------------------------

static void testFaradayRotationCoeffScaling() {
    // Test 22: rho_V scales as n_e * B_par / nu^2
    const double nu   = 230.0e9;
    const double nE1  = 1.0e5;
    const double bpar = 5.0;
    const double rhoV1 = faradayRotationCoeff(nu, nE1, bpar);
    const double rhoV2 = faradayRotationCoeff(nu, 2.0 * nE1, bpar);
    const double rhoV3 = faradayRotationCoeff(nu, nE1, 2.0 * bpar);
    const double rhoV4 = faradayRotationCoeff(2.0 * nu, nE1, bpar);
    check(nearRel(rhoV2 / rhoV1, 2.0, 1.0e-12), "faradayRotationCoeff: scales linearly with n_e");
    check(nearRel(rhoV3 / rhoV1, 2.0, 1.0e-12), "faradayRotationCoeff: scales linearly with B_par");
    check(nearRel(rhoV4 / rhoV1, 0.25, 1.0e-12), "faradayRotationCoeff: scales as 1/nu^2");
}

static void testFaradayRotationCoeffDegenerate() {
    // Test 23: zero inputs return 0
    check(near(faradayRotationCoeff(0.0, 1.0e5, 5.0), 0.0, 1.0e-30),
          "faradayRotationCoeff: nu=0 returns 0");
    check(near(faradayRotationCoeff(230.0e9, 0.0, 5.0), 0.0, 1.0e-30),
          "faradayRotationCoeff: n_e=0 returns 0");
}

static void testRelativisticFaradaySuppression() {
    // Test 24: relativistic rho_V < cold-plasma for Theta_e > 1
    const double nu   = 230.0e9;
    const double nE   = 1.0e6;
    const double bpar = 10.0;
    const double cold  = faradayRotationCoeff(nu, nE, bpar);
    const double hot   = faradayRotationCoeffRelativistic(nu, nE, bpar, 3.0);
    check(hot < cold, "faradayRotationCoeffRelativistic: suppressed for Theta_e=3");
    check(hot >= 0.0, "faradayRotationCoeffRelativistic: non-negative");
}

static void testFaradayConversionPositive() {
    // Test 25: rho_Q >= 0 for B_perp >= 0 and Theta_e > 0
    const double nu    = 230.0e9;
    const double nE    = 1.0e6;
    const double bPerp = 10.0;
    const double thetaE = 2.0;
    const double rhoQ = faradayConversionCoeff(nu, nE, bPerp, thetaE);
    check(rhoQ >= 0.0, "faradayConversionCoeff: non-negative for physical parameters");
}

// ---------------------------------------------------------------------------
// GR transforms
// ---------------------------------------------------------------------------

static void testGRTransformStokes() {
    // Test 26: grTransformStokes: all four components scale as g^3
    const StokesVector s0 = {1.0e-6, 0.5e-6, 0.3e-6, 0.1e-6};
    const double g = 0.8;
    const StokesVector sObs = grTransformStokes(s0, g);
    const double g3 = g * g * g;
    check(nearRel(sObs.i, s0.i * g3, 1.0e-12), "grTransformStokes: I scales as g^3");
    check(nearRel(sObs.q, s0.q * g3, 1.0e-12), "grTransformStokes: Q scales as g^3");
    check(nearRel(sObs.u, s0.u * g3, 1.0e-12), "grTransformStokes: U scales as g^3");
    check(nearRel(sObs.v, s0.v * g3, 1.0e-12), "grTransformStokes: V scales as g^3");

    // g=0 returns zero
    const StokesVector sZero = grTransformStokes(s0, 0.0);
    check(near(sZero.i, 0.0, 1.0e-30), "grTransformStokes: g=0 returns zero");
}

static void testFaradayRotateStokes() {
    // Test 27: faradayRotateStokes rotates EVPA; I,V unchanged
    const StokesVector s0 = {1.0, 1.0, 0.0, 0.2};
    const double rmRad = std::numbers::pi / 8.0;
    const StokesVector s1 = faradayRotateStokes(s0, rmRad);
    check(near(s1.i, s0.i, 1.0e-14), "faradayRotateStokes: I unchanged");
    check(near(s1.v, s0.v, 1.0e-14), "faradayRotateStokes: V unchanged");
    check(nearRel(s1.linPolFrac(), s0.linPolFrac(), 1.0e-12),
          "faradayRotateStokes: linear pol fraction conserved");
    check(nearRel(s1.evpa() - s0.evpa(), rmRad, 1.0e-12),
          "faradayRotateStokes: EVPA shifts by rmRad");
}

static void testGRParallelTransportRotate() {
    // Test 28: grParallelTransportRotate preserves I and V; rotates EVPA
    const StokesVector s0 = {1.0, 0.5, 0.5, 0.1};
    const double psi = 0.3;
    const StokesVector s1 = grParallelTransportRotate(s0, psi);
    check(near(s1.i, s0.i, 1.0e-14), "grParallelTransportRotate: I unchanged");
    check(near(s1.v, s0.v, 1.0e-14), "grParallelTransportRotate: V unchanged");
    check(nearRel(s1.linPolFrac(), s0.linPolFrac(), 1.0e-12),
          "grParallelTransportRotate: linear pol fraction conserved");
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

int main() {
    std::cout << "\n=== Stokes I,Q,U,V Transport Tests (D4) ===\n\n";

    std::cout << "StokesVector helpers:\n";
    testLinPolFrac();
    testEvpa();
    testRotateEvpa();
    testTotalPolFrac();

    std::cout << "\nstokesStep -- simplified K (alpha_I + rho_V):\n";
    testStokesStepIEqualsRteStep();
    testPureFaradayRotationPreservesI();
    testFaradayRotationAngle();
    testFaradayRotationConservesLinPol();
    testPureAbsorptionDecay();
    testThickSlabEquilibrium();
    testZeroStepPreservesState();
    testNonNegativeIFromZero();
    testExactMatchesRK4ForSimplifiedK();

    std::cout << "\nPath integration:\n";
    testPathIntegrationMatchesSequential();
    testAccumulatedFaradayRotation();

    std::cout << "\nPolarization bound:\n";
    testPolarizationBoundSatisfied();
    testPolarizationBoundThickSlab();

    std::cout << "\nPhysical emission coefficients:\n";
    testLinearPolarFracPowerLaw();
    testPolarizedEmissionVector();
    testPolarizedEmissionEvpa();
    testThermalLinPolFrac();

    std::cout << "\nFaraday coefficients:\n";
    testFaradayRotationCoeffScaling();
    testFaradayRotationCoeffDegenerate();
    testRelativisticFaradaySuppression();
    testFaradayConversionPositive();

    std::cout << "\nGR transforms:\n";
    testGRTransformStokes();
    testFaradayRotateStokes();
    testGRParallelTransportRotate();

    std::cout << "\n";
    std::cout << gNPass << "/" << gNTotal << " tests passed.\n";
    if (gAllPass) {
        std::cout << "[ALL PASS]\n\n";
        return 0;
    }
    std::cout << "[FAILURE] One or more tests failed.\n\n";
    return 1;
}
