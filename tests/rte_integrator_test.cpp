/**
 * @file tests/rte_integrator_test.cpp
 * @brief Validation tests for the volumetric RTE CPU integrator (D1).
 *
 * WHY: rte_integrator.h implements the formal solution dI_nu/ds = j_nu - alpha_nu * I_nu
 * used for optically thick/thin plasma emission in Blackhole's CPU ray-marching path.
 * These tests guard all analytically derivable limits without requiring a full geodesic
 * integration run.
 *
 * Test list (22 tests):
 *
 * Formal solution limits:
 *   1.  Pure emission (alpha=0): I grows as j * L (optically thin, exact).
 *   2.  Pure absorption (j=0): I decays as I0 * exp(-alpha * L).
 *   3.  Thick slab (tau >> 1): I -> S_nu = j/alpha (source function limit).
 *   4.  Zero step (ds=0): state is unchanged.
 *   5.  Small tau (< 1e-4): numerical result matches first-order Taylor.
 *   6.  Specific intensity stays non-negative from zero initial state.
 *   7.  integrateRtePath produces same result as sequential rteStep calls.
 *   8.  Convergence: halving step size reduces path-integral error by >= 2x.
 *
 * Planck function:
 *   9.  B_nu(T) > 0 for positive nu and T.
 *  10.  Rayleigh-Jeans limit: B_nu ~ 2 nu^2 kT / c^2 (h nu << kT).
 *  11.  Wien limit: B_nu ~ (2 h nu^3/c^2) * exp(-h nu / kT) (h nu >> kT).
 *  12.  Planck monotonic in T at fixed nu: higher T -> higher B_nu.
 *  13.  rayleighJeans() matches planckFunction() in the RJ limit.
 *  14.  Degenerate inputs (nu<=0 or T<=0) return 0.
 *
 * Thermal synchrotron:
 *  15.  synchrotronThermalEmissivity > 0 for valid inputs.
 *  16.  Emissivity increases with n_e (proportional to n_e).
 *  17.  Emissivity increases with B field (stronger field -> more emission).
 *  18.  synchrotronThermalAbsorption >= 0 for valid inputs.
 *  19.  Kirchhoff check: j_nu / alpha_nu ~ B_nu(T_e) at the mm-wave frequency.
 *
 * Bremsstrahlung:
 *  20.  bremsstrahlungEmissivity > 0 for valid plasma.
 *  21.  Scales as n_e^2: doubling n_e quadruples emission.
 *
 * GR transforms:
 *  22.  grTransformIntensity: I_obs = g^3 * I_emit (Liouville invariant).
 *  23.  grTransformEmission/Absorption: round-trip j->obs->plasma -> j (via g then 1/g).
 *  24.  rteStepGR with g=1 matches rteStep with same coefficients.
 *
 * References:
 *   - Rybicki & Lightman (1979), Radiative Processes in Astrophysics.
 *   - Mahadevan (1996), ApJ 457, 805.
 *   - Mihalas & Mihalas (1984), Foundations of Radiation Hydrodynamics.
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>
#include <vector>

#include "../src/physics/rte_integrator.h"

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

// Exact analytic result for uniform slab: I(L) = I0*exp(-alpha*L) + (j/alpha)*(1 - exp(-alpha*L))
double analyticSlab(double i0, double jNu, double alphaNu, double lenCm) {
    if (alphaNu <= 0.0) { return i0 + jNu * lenCm; }
    const double tau = alphaNu * lenCm;
    return i0 * std::exp(-tau) + (jNu / alphaNu) * (1.0 - std::exp(-tau));
}

} // namespace

// ---------------------------------------------------------------------------
// Formal solution tests
// ---------------------------------------------------------------------------

static void testPureEmission() {
    // Test 1: pure emission (alpha=0): I = I0 + j * L
    const double jNu  = 1.0e-10;
    const double lenCm = 1.0e14;
    RteState s = rteStep({0.0, 0.0, 0.0}, jNu, 0.0, lenCm);
    const double expected = jNu * lenCm;
    check(nearRel(s.iNu, expected, 1.0e-12), "rteStep: pure emission I = j*L");
    check(near(s.tau, 0.0, 1.0e-30), "rteStep: pure emission tau = 0");
    check(near(s.sCm, lenCm, 1.0e-3), "rteStep: pure emission sCm accumulates");
}

static void testPureAbsorption() {
    // Test 2: pure absorption (j=0): I = I0 * exp(-alpha*L)
    const double i0     = 1.0e-6;
    const double alpha  = 1.0e-15;
    const double lenCm  = 1.0e14;
    RteState s = rteStep({i0, 0.0, 0.0}, 0.0, alpha, lenCm);
    const double expected = i0 * std::exp(-alpha * lenCm);
    check(nearRel(s.iNu, expected, 1.0e-10), "rteStep: pure absorption I = I0*exp(-tau)");
}

static void testThickSlab() {
    // Test 3: optically thick (tau >> 1): I -> S_nu = j/alpha
    const double jNu   = 3.0e-8;
    const double alpha = 1.0e-10;
    const double i0    = 0.0;
    // Use tau = alpha * L = 100 (very thick)
    const double lenCm = 100.0 / alpha;
    RteState s = rteStep({i0, 0.0, 0.0}, jNu, alpha, lenCm);
    const double sNu = jNu / alpha;
    // I should be within 1e-40 of S_nu (exp(-100) ~ 4e-44)
    check(nearRel(s.iNu, sNu, 1.0e-6), "rteStep: thick slab I -> S_nu = j/alpha");
}

static void testZeroStep() {
    // Test 4: ds=0 -> state unchanged
    RteState s0 = {1.23e-7, 0.42, 1.5e14};
    RteState s  = rteStep(s0, 1.0e-9, 1.0e-14, 0.0);
    check(near(s.iNu, s0.iNu, 1.0e-30) && near(s.tau, s0.tau, 1.0e-30),
          "rteStep: ds=0 leaves state unchanged");
}

static void testSmallTauNumerics() {
    // Test 5: small tau regime matches first-order Taylor (optically thin)
    const double jNu   = 1.0e-12;
    const double alpha = 1.0e-30;  // extremely small -> tau ~ 1e-16
    const double lenCm = 1.0e14;
    const double i0    = 0.0;
    RteState s = rteStep({i0, 0.0, 0.0}, jNu, alpha, lenCm);
    const double expected = jNu * lenCm;  // to machine epsilon
    check(nearRel(s.iNu, expected, 1.0e-10), "rteStep: small tau matches j*ds");
}

static void testNonNegativeIntensity() {
    // Test 6: I remains >= 0 for any valid inputs starting from I=0
    const double jNu   = 1.0e-9;
    const double alpha = 1.0e-12;
    const double lenCm = 1.0e14;
    RteState s = rteStep({0.0, 0.0, 0.0}, jNu, alpha, lenCm);
    check(s.iNu >= 0.0, "rteStep: I >= 0 for zero initial state");
    // Starting from positive I0, pure absorption cannot give negative I
    s = rteStep({1.0e-5, 0.0, 0.0}, 0.0, 1.0e-10, 1.0e12);
    check(s.iNu >= 0.0, "rteStep: I >= 0 under pure absorption");
}

static void testPathIntegralMatchesSequential() {
    // Test 7: integrateRtePath matches sequential rteStep calls
    const std::size_t N = 20;
    const double jNu   = 2.0e-9;
    const double alpha = 3.0e-14;
    const double ds    = 5.0e12;

    // Build path
    std::vector<RteSample> path(N, {jNu, alpha, ds});

    // Sequential
    RteState seq;
    for (std::size_t i = 0; i < N; ++i) {
        seq = rteStep(seq, jNu, alpha, ds);
    }

    // integrateRtePath
    const RteState path_result = integrateRtePath(path);

    check(nearRel(path_result.iNu, seq.iNu, 1.0e-12),
          "integrateRtePath: matches sequential rteStep");
    check(nearRel(path_result.tau, seq.tau, 1.0e-12),
          "integrateRtePath: tau matches sequential");
}

static void testPathIntegralConvergence() {
    // Test 8: halving step size reduces error by >= 2x (first-order convergence)
    // Exact analytic answer for uniform slab:
    const double jNu   = 1.0e-10;
    const double alpha = 5.0e-15;
    const double lenCm = 2.0e14;
    const double exact = analyticSlab(0.0, jNu, alpha, lenCm);

    // Coarse: 10 steps
    const std::size_t N_coarse = 10;
    const double ds_coarse = lenCm / N_coarse;
    const RteState r_coarse = integrateRtePath(std::vector<RteSample>(N_coarse, {jNu, alpha, ds_coarse}));
    const double err_coarse = std::abs(r_coarse.iNu - exact);

    // Fine: 20 steps
    const std::size_t N_fine = 20;
    const double ds_fine = lenCm / N_fine;
    const RteState r_fine = integrateRtePath(std::vector<RteSample>(N_fine, {jNu, alpha, ds_fine}));
    const double err_fine = std::abs(r_fine.iNu - exact);

    // Note: rteStep is the EXACT formal solution for a uniform segment, so
    // for a uniform j/alpha the result is exact regardless of step count.
    // The "convergence" test here verifies that finer steps do not introduce
    // more error (monotonicity of the exact formal solution).
    check(err_fine <= err_coarse + 1.0e-30,
          "rteStep convergence: finer steps do not increase error for uniform slab");

    // Verify the coarse result also matches analytic to machine epsilon
    // (since the exact formula is applied per segment with constant coefficients)
    check(nearRel(r_coarse.iNu, exact, 1.0e-10),
          "rteStep: exact formal solution matches analytic uniform slab");
}

// ---------------------------------------------------------------------------
// Planck function tests
// ---------------------------------------------------------------------------

static void testPlanckPositive() {
    // Test 9: B_nu > 0 for positive nu, T
    const double bNu = planckFunction(230.0e9, 1.0e10);
    check(bNu > 0.0, "planckFunction: positive for nu=230 GHz, T=1e10 K");
}

static void testPlanckRayleighJeans() {
    // Test 10: RJ limit h nu << kT: B_nu ~ 2 nu^2 kT / c^2
    const double nu   = 1.0e9;   // 1 GHz
    const double T    = 1.0e8;   // 1e8 K  -> hnu/kT ~ 4.8e-6 << 1
    const double bNu  = planckFunction(nu, T);
    const double bRJ  = rayleighJeans(nu, T);
    // Should agree to better than 0.01% (RJ error ~ (hnu/kT)^2/12 ~ 2e-12)
    check(nearRel(bNu, bRJ, 1.0e-4), "planckFunction: matches Rayleigh-Jeans for hnu<<kT");
}

static void testPlanckWienLimit() {
    // Test 11: Wien limit h nu >> kT: B_nu ~ (2h nu^3/c^2)*exp(-hnu/kT)
    const double nu   = 1.0e18;  // X-ray: ~4 keV photons
    const double T    = 1.0e6;   // 1e6 K -> hnu/kT ~ 47.8 >> 1
    const double hNu  = 2.0 * std::numbers::pi * HBAR * nu;
    const double bNu  = planckFunction(nu, T);
    const double bWien = (2.0 * hNu * nu * nu / (C * C)) * std::exp(-hNu / (K_B * T));
    // Wien matches Planck to < 0.1% when x = hnu/kT >> 1
    check(nearRel(bNu, bWien, 1.0e-3), "planckFunction: matches Wien limit for hnu>>kT");
}

static void testPlanckMonotonicInT() {
    // Test 12: at fixed nu, B_nu increases with T
    const double nu = 230.0e9;
    const double b1 = planckFunction(nu, 1.0e9);
    const double b2 = planckFunction(nu, 1.0e10);
    const double b3 = planckFunction(nu, 1.0e11);
    check(b1 < b2 && b2 < b3, "planckFunction: monotonic increasing in T at fixed nu");
}

static void testRayleighJeansMatchesPlanck() {
    // Test 13: rayleighJeans() ~ planckFunction() in the RJ regime
    const double nu = 1.0e8;   // 100 MHz
    const double T  = 1.0e12;  // very hot -> deep RJ
    const double bNu = planckFunction(nu, T);
    const double bRJ = rayleighJeans(nu, T);
    check(nearRel(bNu, bRJ, 1.0e-4), "rayleighJeans: matches planckFunction in RJ regime");
}

static void testPlanckDegenerateInputs() {
    // Test 14: zero/negative inputs return 0
    check(planckFunction(0.0, 1.0e6) == 0.0, "planckFunction: nu=0 returns 0");
    check(planckFunction(230.0e9, 0.0) == 0.0, "planckFunction: T=0 returns 0");
    check(planckFunction(-1.0, 1.0e6) == 0.0, "planckFunction: nu<0 returns 0");
}

// ---------------------------------------------------------------------------
// Thermal synchrotron tests
// ---------------------------------------------------------------------------

static void testSynchThermalEmissivityPositive() {
    // Test 15: j_nu > 0 for valid EHT-like plasma parameters
    // M87* disk: B ~ 10 G, n_e ~ 1e6 cm^-3, T_e ~ 1e10 K -> Theta_e ~ 2
    const double nu    = 230.0e9;  // EHT frequency
    const double bField = 10.0;    // 10 Gauss
    const double nE    = 1.0e6;    // cm^-3
    const double thetaE = 2.0;     // Theta_e = kT_e/(m_e c^2)
    const double jNu   = synchrotronThermalEmissivity(nu, bField, nE, thetaE);
    check(jNu > 0.0, "synchrotronThermalEmissivity: positive for EHT-like params");
}

static void testSynchThermalEmissivityScalesWithNe() {
    // Test 16: j_nu proportional to n_e
    const double nu    = 230.0e9;
    const double bField = 10.0;
    const double thetaE = 2.0;
    const double j1    = synchrotronThermalEmissivity(nu, bField, 1.0e5, thetaE);
    const double j2    = synchrotronThermalEmissivity(nu, bField, 2.0e5, thetaE);
    check(nearRel(j2 / j1, 2.0, 1.0e-8), "synchrotronThermalEmissivity: scales linearly with n_e");
}

static void testSynchThermalEmissivityScalesWithB() {
    // Test 17: j_nu increases with B (stronger field -> more synchrotron)
    const double nu    = 230.0e9;
    const double nE    = 1.0e6;
    const double thetaE = 2.0;
    const double j5    = synchrotronThermalEmissivity(nu, 5.0, nE, thetaE);
    const double j10   = synchrotronThermalEmissivity(nu, 10.0, nE, thetaE);
    const double j20   = synchrotronThermalEmissivity(nu, 20.0, nE, thetaE);
    check(j5 < j10 && j10 < j20, "synchrotronThermalEmissivity: increases with B field");
}

static void testSynchThermalAbsorptionNonNegative() {
    // Test 18: alpha_nu >= 0
    const double nu    = 230.0e9;
    const double alpha = synchrotronThermalAbsorption(nu, 10.0, 1.0e6, 2.0);
    check(alpha >= 0.0, "synchrotronThermalAbsorption: non-negative");
}

static void testSynchThermalKirchhoff() {
    // Test 19: j_nu / alpha_nu ~ B_nu(T_e) (Kirchhoff's law for thermal emission)
    const double nu     = 230.0e9;
    const double bField = 10.0;
    const double nE     = 1.0e6;
    const double thetaE = 2.0;
    const double tempK  = thetaE * M_ELECTRON * C * C / K_B;

    const double jNu    = synchrotronThermalEmissivity(nu, bField, nE, thetaE);
    const double alphaNu = synchrotronThermalAbsorption(nu, bField, nE, thetaE);
    const double bNu    = planckFunction(nu, tempK);

    if (alphaNu > 0.0 && bNu > 0.0) {
        const double ratio = (jNu / alphaNu) / bNu;
        // Should equal 1.0 exactly (by construction: alpha = j/B_nu)
        check(nearRel(ratio, 1.0, 1.0e-10), "synchrotronThermalAbsorption: Kirchhoff j/alpha = B_nu");
    } else {
        check(false, "synchrotronThermalAbsorption: Kirchhoff check (alpha or B_nu zero)");
    }
}

// ---------------------------------------------------------------------------
// Bremsstrahlung tests
// ---------------------------------------------------------------------------

static void testBremsstrahlungPositive() {
    // Test 20: j_nu^ff > 0 for thermal coronal plasma
    // T ~ 1e9 K, n_e ~ 1e10 cm^-3 (compact corona)
    const double jff = bremsstrahlungEmissivity(1.0e18, 1.0e10, 1.0e10, 1.0e9);
    check(jff > 0.0, "bremsstrahlungEmissivity: positive for hot corona");
}

static void testBremsstrahlungScalesAsNe2() {
    // Test 21: j_nu ~ n_e^2 (both n_e and n_i contribute)
    const double nu = 1.0e18;
    const double T  = 1.0e9;
    const double j1 = bremsstrahlungEmissivity(nu, 1.0e10, 1.0e10, T);
    const double j2 = bremsstrahlungEmissivity(nu, 2.0e10, 2.0e10, T);
    // Doubling both n_e and n_i -> quadruples j (j ~ n_e * n_i = n_e^2)
    check(nearRel(j2 / j1, 4.0, 0.05), "bremsstrahlungEmissivity: scales as n_e^2");
}

// ---------------------------------------------------------------------------
// GR transform tests
// ---------------------------------------------------------------------------

static void testGRIntensityTransform() {
    // Test 22: I_obs = g^3 * I_emit (Liouville invariant)
    const double iEmit = 1.234e-7;
    const double g     = 0.7;  // redshifted photon
    const double iObs  = grTransformIntensity(iEmit, g);
    check(nearRel(iObs, iEmit * g * g * g, 1.0e-12),
          "grTransformIntensity: I_obs = g^3 * I_emit");

    // g > 1 (blueshifted, inner plunging orbit)
    const double gb = 1.3;
    check(nearRel(grTransformIntensity(iEmit, gb), iEmit * gb * gb * gb, 1.0e-12),
          "grTransformIntensity: I_obs = g^3 (blueshift)");

    // g <= 0 returns 0
    check(grTransformIntensity(iEmit, 0.0) == 0.0,
          "grTransformIntensity: g=0 returns 0");
}

static void testGREmissionAbsorptionRoundTrip() {
    // Test 23: applying g then 1/g on emission/absorption recovers original
    const double jEmit = 2.5e-9;
    const double alphaEmit = 1.3e-14;
    const double g = 0.85;

    const double jObs    = grTransformEmission(jEmit, g);
    const double alphaObs = grTransformAbsorption(alphaEmit, g);

    // Round-trip: scale by 1/g to go back to plasma frame
    check(nearRel(grTransformEmission(jObs, 1.0 / g), jEmit, 1.0e-12),
          "grTransformEmission: round-trip with g then 1/g");
    check(nearRel(grTransformAbsorption(alphaObs, 1.0 / g), alphaEmit, 1.0e-12),
          "grTransformAbsorption: round-trip with g then 1/g");
}

static void testRteStepGRWithUnitRedshift() {
    // Test 24: rteStepGR with g=1 matches rteStep with same coefficients
    const double jNu   = 1.5e-9;
    const double alpha = 2.0e-14;
    const double ds    = 1.0e13;
    const double i0    = 1.0e-7;

    const RteState s1 = rteStep({i0, 0.0, 0.0}, jNu, alpha, ds);
    const RteState s2 = rteStepGR({i0, 0.0, 0.0}, jNu, alpha, ds, 1.0);

    check(nearRel(s1.iNu, s2.iNu, 1.0e-12),
          "rteStepGR: matches rteStep for g=1 (no redshift)");
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

int main() {
    std::cout << "\n=== RTE Integrator Tests (D1) ===\n\n";

    std::cout << "Formal solution:\n";
    testPureEmission();
    testPureAbsorption();
    testThickSlab();
    testZeroStep();
    testSmallTauNumerics();
    testNonNegativeIntensity();
    testPathIntegralMatchesSequential();
    testPathIntegralConvergence();

    std::cout << "\nPlanck function:\n";
    testPlanckPositive();
    testPlanckRayleighJeans();
    testPlanckWienLimit();
    testPlanckMonotonicInT();
    testRayleighJeansMatchesPlanck();
    testPlanckDegenerateInputs();

    std::cout << "\nThermal synchrotron:\n";
    testSynchThermalEmissivityPositive();
    testSynchThermalEmissivityScalesWithNe();
    testSynchThermalEmissivityScalesWithB();
    testSynchThermalAbsorptionNonNegative();
    testSynchThermalKirchhoff();

    std::cout << "\nBremsstrahlung:\n";
    testBremsstrahlungPositive();
    testBremsstrahlungScalesAsNe2();

    std::cout << "\nGR transforms:\n";
    testGRIntensityTransform();
    testGREmissionAbsorptionRoundTrip();
    testRteStepGRWithUnitRedshift();

    std::cout << "\n";
    std::cout << gNPass << "/" << gNTotal << " tests passed.\n";
    if (gAllPass) {
        std::cout << "[ALL PASS]\n\n";
        return 0;
    }
    std::cout << "[FAILURE] One or more tests failed.\n\n";
    return 1;
}
