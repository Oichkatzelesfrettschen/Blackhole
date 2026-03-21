/**
 * @file tests/gw_memory_precession_test.cpp
 * @brief Validation tests for GW memory effect (D7) and precessing binary PN phase (D8).
 *
 * WHY: gravitational_waves.h now implements the non-linear GW memory (Christodoulou
 * 1991; Favata 2009) and the "simple precession" (Apostolatos 1994) parameterisation
 * for generic-spin binaries (Schmidt 2015 chi_p).  These tests guard the formulas
 * against regressions and verify physical limits that are analytically derivable
 * without full numerical relativity.
 *
 * D7 -- GW Memory (8 tests):
 *   1. Memory strain is positive for standard GW150914-like parameters.
 *   2. Memory grows monotonically with GW frequency (inspiral accumulates memory).
 *   3. Face-on memory (iota=0) exceeds edge-on (iota=pi/2) because 18 > 17.
 *   4. Memory scales linearly with eta (at fixed M, D, f).
 *   5. Memory scales as M^{5/3} with total mass (from v^2 ~ (G M f)^{2/3}).
 *   6. gwMemoryDelta = gwMemoryStrain(fHi) - gwMemoryStrain(fLo) exactly.
 *   7. GW150914-like memory amplitude is in the expected 1e-23 to 1e-21 range.
 *   8. Memory vanishes for zero eta, mass, distance, or frequency.
 *
 * D8 -- Precessing Binary PN Phase (9 tests):
 *   9.  chiP equals chi1Perp when secondary has no in-plane spin (chi2Perp=0).
 *  10.  chiP equals max(chi1Perp, chi2Perp) at equal mass (q=1).
 *  11.  chiP < max(chi1Perp, chi2Perp) for q < 1 (secondary spin down-weighted).
 *  12.  chiP is zero when both in-plane spins are zero.
 *  13.  Opening angle is zero for aligned spins (chi_p=0, chiEff!=0).
 *  14.  Opening angle is pi/2 for purely in-plane spin (chiEff=0, chi_p>0).
 *  15.  Precession phase is positive for positive chi_eff (prograde precession).
 *  16.  Precession phase DECREASES with frequency (alpha ~ 1/f: measures remaining
 *        precession to coalescence, dominated by the 1/v^3 factor). The accumulated
 *        precession DURING inspiral from fLo to fHi is alpha(fLo) - alpha(fHi) > 0.
 *  17.  precessedPolarizations preserves the GW polarization invariant h+^2 + hx^2.
 *
 * References:
 *   - Christodoulou (1991), PRL 67, 1486
 *   - Favata (2009), PRD 80, 024002
 *   - Apostolatos et al. (1994), PRD 49, 6274
 *   - Schmidt, Hannam & Husa (2015), PRD 91, 024039
 *   - Hannam et al. (2014), PRD 89, 124025
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>

#include "../src/physics/gravitational_waves.h"
#include "../src/physics/constants.h"

using namespace physics;

namespace {

bool gAllPass = true;

void check(bool condition, const char* test, const char* detail = "") {
    if (condition) {
        std::cout << "  [PASS] " << test << "\n";
    } else {
        std::cout << "  [FAIL] " << test;
        if (detail[0] != '\0') { std::cout << " -- " << detail; }
        std::cout << "\n";
        gAllPass = false;
    }
}

// GW150914-like parameters in CGS (matching constants.h convention).
constexpr double kM1Solar  = 36.3;    // Msun
constexpr double kM2Solar  = 29.1;    // Msun
constexpr double kDist_Mpc = 410.0;   // Mpc

[[nodiscard]] double mTotal_g()  { return (kM1Solar + kM2Solar) * M_SUN; }
[[nodiscard]] double eta150914() {
    const double m1 = kM1Solar * M_SUN;
    const double m2 = kM2Solar * M_SUN;
    const double mT = m1 + m2;
    return (m1 * m2) / (mT * mT);
}
[[nodiscard]] double dist_cm() { return kDist_Mpc * 1.0e6 * PARSEC; }

// ============================================================================
// D7 tests: GW Memory
// ============================================================================

/* Test 1: Memory strain is positive for standard parameters. */
bool testMemoryPositive() {
    std::cout << "Test 1: memory strain > 0 for GW150914-like params\n";

    const double h = gwMemoryStrain(mTotal_g(), eta150914(),
                                    /*fGw=*/35.0, dist_cm(), /*iota=*/0.0);
    char buf[128];
    std::snprintf(buf, sizeof(buf), "h_mem = %.3e (expected > 0)", h);
    check(h > 0.0, "memory strain is positive", buf);
    return true;
}

/* Test 2: Memory grows monotonically with frequency. */
bool testMemoryMonotonicallyIncreases() {
    std::cout << "Test 2: memory strain grows monotonically with frequency\n";

    const double mT  = mTotal_g();
    const double eta = eta150914();
    const double d   = dist_cm();

    const double freqs[] = {10.0, 20.0, 35.0, 50.0, 68.0};
    double prev = gwMemoryStrain(mT, eta, freqs[0], d, 0.0);

    for (std::size_t i = 1; i < 5; ++i) {
        const double h = gwMemoryStrain(mT, eta, freqs[i], d, 0.0);
        char buf[128];
        std::snprintf(buf, sizeof(buf), "h(f=%g) = %.3e, h(f=%g) = %.3e",
                      freqs[i-1], prev, freqs[i], h);
        check(h > prev, "memory increases with frequency", buf);
        prev = h;
    }
    return true;
}

/* Test 3: Face-on memory > edge-on (17 + cos^2 iota: iota=0 gives 18, iota=pi/2 gives 17). */
bool testMemoryAngularFactor() {
    std::cout << "Test 3: face-on memory > edge-on (angular factor 18 vs 17)\n";

    const double mT  = mTotal_g();
    const double eta = eta150914();
    const double d   = dist_cm();
    const double f   = 35.0;

    const double hFaceOn  = gwMemoryStrain(mT, eta, f, d, 0.0);
    const double hEdgeOn  = gwMemoryStrain(mT, eta, f, d, std::numbers::pi / 2.0);

    char buf[128];
    std::snprintf(buf, sizeof(buf), "h_face_on=%.3e, h_edge_on=%.3e", hFaceOn, hEdgeOn);
    check(hFaceOn > hEdgeOn, "face-on > edge-on", buf);

    // Exact ratio should be 18/17
    const double ratio = hFaceOn / hEdgeOn;
    std::snprintf(buf, sizeof(buf), "ratio = %.6f, expected 18/17 = %.6f", ratio, 18.0/17.0);
    check(std::abs(ratio - 18.0/17.0) < 1.0e-10, "angular factor ratio = 18/17", buf);
    return true;
}

/* Test 4: Memory scales linearly with eta. */
bool testMemoryEtaScaling() {
    std::cout << "Test 4: memory scales linearly with eta\n";

    const double mT = mTotal_g();
    const double d  = dist_cm();
    const double f  = 35.0;

    const double eta1 = 0.20;
    const double eta2 = 0.25;
    const double h1   = gwMemoryStrain(mT, eta1, f, d, 0.0);
    const double h2   = gwMemoryStrain(mT, eta2, f, d, 0.0);

    const double measured = h2 / h1;
    const double expected = eta2 / eta1;  // 0.25 / 0.20 = 1.25

    char buf[128];
    std::snprintf(buf, sizeof(buf), "h2/h1 = %.6f, expected %.6f", measured, expected);
    check(std::abs(measured - expected) < 1.0e-10, "linear eta scaling", buf);
    return true;
}

/* Test 5: Memory scales as M^{5/3} (from (G M)^{5/3} f^{2/3} / (D c^{10/3})). */
bool testMemoryMassScaling() {
    std::cout << "Test 5: memory scales as M^{5/3}\n";

    const double eta = 0.25;
    const double d   = dist_cm();
    const double f   = 35.0;

    const double mT1 = 30.0 * M_SUN;
    const double mT2 = 60.0 * M_SUN;

    const double h1 = gwMemoryStrain(mT1, eta, f, d, 0.0);
    const double h2 = gwMemoryStrain(mT2, eta, f, d, 0.0);

    const double measured = h2 / h1;
    const double expected = std::pow(2.0, 5.0/3.0);  // (60/30)^{5/3}

    char buf[128];
    std::snprintf(buf, sizeof(buf), "h2/h1 = %.6f, expected 2^{5/3} = %.6f", measured, expected);
    check(std::abs(measured - expected) < 1.0e-10, "M^{5/3} mass scaling", buf);
    return true;
}

/* Test 6: gwMemoryDelta = h(fHi) - h(fLo) exactly. */
bool testMemoryDeltaConsistency() {
    std::cout << "Test 6: gwMemoryDelta = h(fHi) - h(fLo)\n";

    const double mT  = mTotal_g();
    const double eta = eta150914();
    const double d   = dist_cm();

    const double fLo = 20.0;
    const double fHi = 68.0;

    const double delta = gwMemoryDelta(mT, eta, fLo, fHi, d, 0.0);
    const double diff  = gwMemoryStrain(mT, eta, fHi, d, 0.0)
                       - gwMemoryStrain(mT, eta, fLo, d, 0.0);

    char buf[128];
    std::snprintf(buf, sizeof(buf), "delta=%.6e, diff=%.6e", delta, diff);
    check(std::abs(delta - diff) < 1.0e-30, "gwMemoryDelta matches h(fHi)-h(fLo)", buf);

    // Also verify delta > 0
    check(delta > 0.0, "delta is positive (fHi > fLo)");
    return true;
}

/* Test 7: GW150914-like memory amplitude order of magnitude. */
bool testMemoryOrderOfMagnitude() {
    std::cout << "Test 7: GW150914-like memory order of magnitude\n";

    // At f = 35 Hz (representative LIGO band), memory should be in [1e-23, 1e-21].
    const double h = gwMemoryStrain(mTotal_g(), eta150914(), 35.0, dist_cm(), 0.0);

    char buf[128];
    std::snprintf(buf, sizeof(buf), "h_mem(35Hz) = %.3e [expect 1e-23..1e-21]", h);
    check(h > 1.0e-23 && h < 1.0e-21, "memory in [1e-23, 1e-21]", buf);
    return true;
}

/* Test 8: Memory vanishes for degenerate inputs. */
bool testMemoryDegenerateInputs() {
    std::cout << "Test 8: memory vanishes for degenerate inputs\n";

    const double mT = mTotal_g();
    const double d  = dist_cm();

    check(gwMemoryStrain(0.0,  0.25, 35.0, d,   0.0) == 0.0, "mTotal = 0");
    check(gwMemoryStrain(mT,   0.0,  35.0, d,   0.0) == 0.0, "eta = 0");
    check(gwMemoryStrain(mT,   0.25, 0.0,  d,   0.0) == 0.0, "fGw = 0");
    check(gwMemoryStrain(mT,   0.25, 35.0, 0.0, 0.0) == 0.0, "d = 0");
    check(gwMemoryDelta(mT,    0.25, 20.0, 10.0, d, 0.0) == 0.0, "fHi < fLo");
    return true;
}

// ============================================================================
// D8 tests: Precessing Binary PN Phase
// ============================================================================

/* Test 9: chiP = chi1Perp when secondary has no in-plane spin. */
bool testChiPSingleSpin() {
    std::cout << "Test 9: chiP = chi1Perp when chi2Perp = 0\n";

    const double m1       = 36.3 * M_SUN;
    const double m2       = 29.1 * M_SUN;
    const double chi1Perp = 0.65;

    const double cp = chiP(m1, m2, chi1Perp, 0.0);
    char buf[128];
    std::snprintf(buf, sizeof(buf), "chiP = %.6f, expected %.6f", cp, chi1Perp);
    check(std::abs(cp - chi1Perp) < 1.0e-12, "chiP = chi1Perp (no secondary in-plane spin)", buf);
    return true;
}

/* Test 10: chiP = max(chi1Perp, chi2Perp) at equal mass (q=1). */
bool testChiPEqualMass() {
    std::cout << "Test 10: chiP = max(chi1, chi2) at q=1\n";

    const double m     = 30.0 * M_SUN;
    const double cp1   = 0.40;
    const double cp2   = 0.70;

    const double cp = chiP(m, m, cp1, cp2);  // q=1 => ratio = 1*7/7 = 1
    const double expected = std::max(cp1, cp2);
    char buf[128];
    std::snprintf(buf, sizeof(buf), "chiP = %.6f, expected %.6f", cp, expected);
    check(std::abs(cp - expected) < 1.0e-12, "chiP = max(chi1, chi2) at equal mass", buf);
    return true;
}

/* Test 11: chiP < max(chi1, chi2) for q < 1 (secondary down-weighted). */
bool testChiPDownweighting() {
    std::cout << "Test 11: chiP < max(chi1, chi2) for q < 1\n";

    // q = 0.5: ratio = 0.5 * (4*0.5+3) / (4+3*0.5) = 0.5 * 5 / 5.5 = 0.4545
    const double m1   = 40.0 * M_SUN;
    const double m2   = 20.0 * M_SUN;    // q = 0.5
    const double cp1  = 0.0;
    const double cp2  = 0.80;

    const double cp = chiP(m1, m2, cp1, cp2);
    const double expected_max = std::max(cp1, cp2);  // = 0.80
    char buf[128];
    std::snprintf(buf, sizeof(buf), "chiP = %.6f < max = %.6f", cp, expected_max);
    check(cp < expected_max, "chiP < max(chi1,chi2) for q < 1", buf);
    check(cp > 0.0, "chiP > 0 (some precession from secondary spin)");

    // Verify the exact ratio: 0.5 * 5 / 5.5 = 5/11
    const double ratio    = 0.5 * (4.0 * 0.5 + 3.0) / (4.0 + 3.0 * 0.5);  // = 5/11
    const double expected = ratio * cp2;
    std::snprintf(buf, sizeof(buf), "chiP = %.6f, expected %.6f", cp, expected);
    check(std::abs(cp - expected) < 1.0e-12, "exact chiP formula at q=0.5", buf);
    return true;
}

/* Test 12: chiP = 0 when both in-plane spins are zero. */
bool testChiPZeroSpins() {
    std::cout << "Test 12: chiP = 0 for aligned spins (no in-plane components)\n";

    const double m1 = 36.3 * M_SUN;
    const double m2 = 29.1 * M_SUN;

    check(chiP(m1, m2, 0.0, 0.0) == 0.0, "chiP = 0 for aligned spins");
    return true;
}

/* Test 13: Opening angle = 0 for aligned spins. */
bool testOpeningAngleAligned() {
    std::cout << "Test 13: opening angle = 0 for aligned spins (chi_p = 0)\n";

    const double beta = precessingOpeningAngle(0.7, 0.0);
    char buf[128];
    std::snprintf(buf, sizeof(buf), "beta = %.6f rad (expected 0)", beta);
    check(std::abs(beta) < 1.0e-12, "beta = 0 for aligned spins", buf);
    return true;
}

/* Test 14: Opening angle = pi/2 for purely in-plane spin (chi_eff = 0). */
bool testOpeningAngleInPlane() {
    std::cout << "Test 14: opening angle = pi/2 for purely in-plane spin (chiEff = 0)\n";

    const double beta     = precessingOpeningAngle(0.0, 0.6);
    const double expected = std::numbers::pi / 2.0;
    char buf[128];
    std::snprintf(buf, sizeof(buf), "beta = %.6f, expected %.6f", beta, expected);
    check(std::abs(beta - expected) < 1.0e-12, "beta = pi/2 for in-plane spin", buf);
    return true;
}

/* Test 15: Precession phase is positive for positive chi_eff (prograde precession). */
bool testPrecessionPhaseSign() {
    std::cout << "Test 15: precession phase is positive for chi_eff > 0\n";

    const double mT     = mTotal_g();
    const double eta    = eta150914();
    const double chiEff = 0.5;
    const double f      = 35.0;

    const double alpha = simplePrecessionPhase(mT, eta, chiEff, f);
    char buf[128];
    std::snprintf(buf, sizeof(buf), "alpha = %.4f rad (expected > 0)", alpha);
    check(alpha > 0.0, "precession phase > 0 for chi_eff > 0", buf);

    // Retrograde (chi_eff < 0) should give negative precession phase
    const double alphaRetro = simplePrecessionPhase(mT, eta, -chiEff, f);
    std::snprintf(buf, sizeof(buf), "alpha_retro = %.4f rad (expected < 0)", alphaRetro);
    check(alphaRetro < 0.0, "precession phase < 0 for chi_eff < 0", buf);
    return true;
}

/* Test 16: simplePrecessionPhase is the total remaining precession from fGw to coalescence,
 *          so it DECREASES with frequency (1/f behaviour).  The ACCUMULATED precession
 *          during the inspiral from fLo to fHi > fLo is alpha(fLo) - alpha(fHi) > 0. */
bool testPrecessionPhaseDecreaseWithFrequency() {
    std::cout << "Test 16: precession angle decreases with frequency (1/f scaling)\n";

    const double mT     = mTotal_g();
    const double eta    = eta150914();
    const double chiEff = 0.5;

    // alpha(f) = (3/4) chi_eff / (eta * pi * M_geo * f)  so alpha ~ 1/f: decreases.
    const double freqs[]  = {10.0, 20.0, 35.0, 50.0, 68.0};
    double prev = simplePrecessionPhase(mT, eta, chiEff, freqs[0]);

    for (std::size_t i = 1; i < 5; ++i) {
        const double alpha = simplePrecessionPhase(mT, eta, chiEff, freqs[i]);
        char buf[128];
        std::snprintf(buf, sizeof(buf),
                      "alpha(f=%g) = %.4f < alpha(f=%g) = %.4f (1/f decrease)",
                      freqs[i], alpha, freqs[i-1], prev);
        check(alpha < prev, "alpha decreases with frequency (1/f scaling)", buf);
        prev = alpha;
    }

    // The ACCUMULATED precession during the inspiral from fLo to fHi is alpha(fLo) - alpha(fHi) > 0.
    const double fLo  = 10.0;
    const double fHi  = 68.0;
    const double accumulated = simplePrecessionPhase(mT, eta, chiEff, fLo)
                             - simplePrecessionPhase(mT, eta, chiEff, fHi);
    char buf[128];
    std::snprintf(buf, sizeof(buf), "accumulated precession from %g to %g Hz = %.2f rad",
                  fLo, fHi, accumulated);
    check(accumulated > 0.0, "accumulated precession from fLo to fHi is positive", buf);
    return true;
}

/* Test 17: precessedPolarizations preserves h+^2 + hx^2 (isometry). */
bool testPolarizationIsometry() {
    std::cout << "Test 17: precessedPolarizations preserves h+^2 + hx^2\n";

    const double h0     = 1.2e-21;
    const double hCross = 0.8e-21;
    const double inv0   = h0 * h0 + hCross * hCross;  // reference invariant

    // Test at several precession angles
    const double angles[] = {0.0, 0.3, 0.7, 1.2, std::numbers::pi / 4.0,
                              std::numbers::pi / 2.0, std::numbers::pi};
    for (double alpha : angles) {
        double hpPrec = 0.0;
        double hcPrec = 0.0;
        precessedPolarizations(h0, hCross, alpha, hpPrec, hcPrec);

        const double inv = hpPrec * hpPrec + hcPrec * hcPrec;
        const double err = std::abs(inv - inv0) / inv0;

        char buf[128];
        std::snprintf(buf, sizeof(buf),
                      "alpha=%.3f rad: rel err in h+^2+hx^2 = %.2e (expected < 1e-14)",
                      alpha, err);
        check(err < 1.0e-14, "polarization invariant preserved", buf);
    }
    return true;
}

} // namespace

// ============================================================================
// Main
// ============================================================================

int main() {
    std::cout << "\n================================================\n"
              << "GW MEMORY (D7) + PRECESSING BINARY (D8) VALIDATION\n"
              << "Physics: Favata 2009 + Apostolatos 1994 + Schmidt 2015\n"
              << "================================================\n\n";

    // D7: GW Memory
    std::cout << "--- D7: GW Memory Effect ---\n\n";
    testMemoryPositive();              std::cout << "\n";
    testMemoryMonotonicallyIncreases(); std::cout << "\n";
    testMemoryAngularFactor();          std::cout << "\n";
    testMemoryEtaScaling();             std::cout << "\n";
    testMemoryMassScaling();            std::cout << "\n";
    testMemoryDeltaConsistency();       std::cout << "\n";
    testMemoryOrderOfMagnitude();       std::cout << "\n";
    testMemoryDegenerateInputs();       std::cout << "\n";

    // D8: Precessing Binary PN Phase
    std::cout << "--- D8: Precessing Binary PN Phase ---\n\n";
    testChiPSingleSpin();               std::cout << "\n";
    testChiPEqualMass();                std::cout << "\n";
    testChiPDownweighting();            std::cout << "\n";
    testChiPZeroSpins();                std::cout << "\n";
    testOpeningAngleAligned();          std::cout << "\n";
    testOpeningAngleInPlane();          std::cout << "\n";
    testPrecessionPhaseSign();          std::cout << "\n";
    testPrecessionPhaseDecreaseWithFrequency(); std::cout << "\n";
    testPolarizationIsometry();         std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
