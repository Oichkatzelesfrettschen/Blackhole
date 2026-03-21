/**
 * @file newman_penrose_test.cpp
 * @brief Validation tests for Newman-Penrose null tetrad formalism (Kerr).
 *
 * WHY: newman_penrose.h provides exact Weyl scalars and the Kretschmann
 * invariant for Kerr spacetime.  These feed the AMR step-size controller
 * (strong curvature -> smaller RK4 steps) and the Petrov Type D self-consistency
 * identity.  The tests guard against regressions in closed-form expressions that
 * are easy to get wrong by a sign, a factor of 2, or a wrong power of Sigma.
 *
 * Test plan (10 tests):
 *   1.  Schwarzschild limit (a=0): Re(Psi_2) = -M_geo/r^3, Im(Psi_2) = 0
 *   2.  Equatorial plane (cos theta=0): Im(Psi_2) = 0 for any spin
 *   3.  |Psi_2|^2 = M_geo^2 / Sigma^3 exactly (Petrov Type D identity)
 *   4.  Kretschmann Schwarzschild: K = 48 M_geo^2 / r^6
 *   5.  Kretschmann equatorial (any spin): K = 48 M_geo^2 / r^6
 *   6.  Petrov Type D check: K = 48 |Psi_2|^2 to < 1e-12 relative error
 *   7.  Kretschmann is finite and positive at outer horizon r_+
 *   8.  Ring singularity guard (r=0, cos theta=0, a!=0): kerrWeylPsi2 returns 0
 *       and kerrKretschmann returns +infinity
 *   9.  Large-r falloff: K ~ 48 M_geo^2 / r^6 as r -> 10^6 M_geo
 *  10.  Kinnersley n^mu ingoing vector: n^r < 0 (directed inward for r > r_+)
 *
 * References:
 *   Kinnersley (1969), J. Math. Phys. 10, 1195
 *   Chandrasekhar (1983), Mathematical Theory of Black Holes, Ch. 9
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>

#include "../src/physics/newman_penrose.h"
#include "../src/physics/constants.h"
#include "../src/physics/safe_limits.h"

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

/* GW150914-like Kerr black hole: M_final ~ 62 Msun, a* ~ 0.68. */
constexpr double MASS_SUN_FINAL  = 62.0;
constexpr double A_STAR_FINAL    = 0.68;

[[nodiscard]] double mGeoTest() {
    return (G * MASS_SUN_FINAL * M_SUN) / (C * C);
}
[[nodiscard]] double aTest() {
    return A_STAR_FINAL * mGeoTest();
}

/* =========================================================================
 * Test 1: Schwarzschild limit a=0
 *   Re(Psi_2) = -M_geo/r^3,  Im(Psi_2) = 0
 * ======================================================================= */
bool testSchwarzschild() {
    std::cout << "Test 1: Schwarzschild limit (a=0)\n";

    const double mGeo = mGeoTest();
    const double a    = 0.0;

    /* Test at several radii to ensure 1/r^3 scaling */
    const double radii[] = {3.0 * mGeo, 6.0 * mGeo, 20.0 * mGeo, 100.0 * mGeo};
    bool ok = true;
    for (const double r : radii) {
        const NPWeylPsi2 psi2 = kerrWeylPsi2(r, 0.0, mGeo, a);
        const double expectedRe = -mGeo / (r * r * r);
        const double relRe = std::abs(psi2.re - expectedRe) / std::abs(expectedRe);
        const double relIm = std::abs(psi2.im);  /* should be exactly 0 */

        char buf[256];
        (void)std::snprintf(buf, sizeof(buf),
                            "r=%g M: Re(Psi_2)=%.6e expected=%.6e relErr=%.2e Im=%.2e",
                            r / mGeo, psi2.re, expectedRe, relRe, relIm);
        if (relRe > 1.0e-12 || relIm != 0.0) {
            std::cout << "  [FAIL] " << buf << "\n";
            gAllPass = false;
            ok = false;
        }
    }
    if (ok) { check(true, "Re(Psi_2) = -M/r^3, Im(Psi_2) = 0 for a=0"); }
    return ok;
}

/* =========================================================================
 * Test 2: Equatorial plane (cos theta = 0): Im(Psi_2) = 0 for any spin.
 * Im(Psi_2) = -M a c (3r^2 - a^2c^2) / Sigma^3; c=0 => Im = 0.
 * ======================================================================= */
bool testEquatorialImaginary() {
    std::cout << "Test 2: Equatorial plane -- Im(Psi_2) = 0 for any spin\n";

    const double mGeo = mGeoTest();
    const double a    = aTest();
    const double r    = 6.0 * mGeo;  /* r = 6 M, outside ISCO */

    const NPWeylPsi2 psi2 = kerrWeylPsi2(r, 0.0 /* equatorial */, mGeo, a);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "Im(Psi_2) = %.3e (expected 0)", psi2.im);
    check(psi2.im == 0.0, "Im(Psi_2) = 0 at equatorial plane", buf);
    check(psi2.re < 0.0, "Re(Psi_2) < 0 (negative in Kinnersley convention)");
    return true;
}

/* =========================================================================
 * Test 3: |Psi_2|^2 = M_geo^2 / Sigma^3 (Petrov Type D identity).
 * Verified at general (r, theta) to confirm complex arithmetic is correct.
 * ======================================================================= */
bool testPsi2ModSq() {
    std::cout << "Test 3: |Psi_2|^2 = M_geo^2 / Sigma^3\n";

    const double mGeo = mGeoTest();
    const double a    = aTest();

    /* Test at several (r, theta) combinations */
    const double testCases[4][2] = {
        {4.0 * mGeo, 0.0},                    /* equatorial */
        {4.0 * mGeo, 0.6},                    /* cos theta = 0.6 */
        {10.0 * mGeo, -0.4},                  /* southern hemisphere */
        {2.5 * mGeo, 1.0 / std::numbers::sqrt2}   /* 45 degrees */
    };

    bool ok = true;
    for (const auto& tc : testCases) {
        const double r        = tc[0];
        const double cosTheta = tc[1];

        const NPWeylPsi2 psi2  = kerrWeylPsi2(r, cosTheta, mGeo, a);
        const double    modsq  = (psi2.re * psi2.re) + (psi2.im * psi2.im);
        const double    sigma  = kerrSigma(r, cosTheta, a);
        const double    expect = (mGeo * mGeo) / (sigma * sigma * sigma);
        const double    relErr = std::abs(modsq - expect) / expect;

        char buf[256];
        (void)std::snprintf(buf, sizeof(buf),
                            "r=%g M, c=%.2f: |Psi2|^2=%.6e expected=%.6e relErr=%.2e",
                            r / mGeo, cosTheta, modsq, expect, relErr);
        if (relErr > 1.0e-12) {
            std::cout << "  [FAIL] " << buf << "\n";
            gAllPass = false;
            ok = false;
        }
    }
    if (ok) { check(true, "|Psi_2|^2 = M^2/Sigma^3 at all test points (relErr < 1e-12)"); }
    return ok;
}

/* =========================================================================
 * Test 4: Kretschmann Schwarzschild: K = 48 M_geo^2 / r^6
 * ======================================================================= */
bool testKretschmannSchwarzschild() {
    std::cout << "Test 4: Kretschmann K = 48 M^2/r^6 for a=0\n";

    const double mGeo = mGeoTest();
    const double a    = 0.0;

    const double radii[] = {3.0 * mGeo, 6.0 * mGeo, 20.0 * mGeo};
    bool ok = true;
    for (const double r : radii) {
        const double k        = kerrKretschmann(r, 0.0, mGeo, a);
        const double expected = 48.0 * mGeo * mGeo / (r * r * r * r * r * r);
        const double relErr   = std::abs(k - expected) / expected;

        char buf[256];
        (void)std::snprintf(buf, sizeof(buf),
                            "r=%g M: K=%.6e expected=%.6e relErr=%.2e",
                            r / mGeo, k, expected, relErr);
        if (relErr > 1.0e-12) {
            std::cout << "  [FAIL] " << buf << "\n";
            gAllPass = false;
            ok = false;
        }
    }
    if (ok) { check(true, "K = 48 M^2/r^6 for a=0 (relErr < 1e-12)"); }
    return ok;
}

/* =========================================================================
 * Test 5: Kretschmann equatorial = 48 M^2/r^6 (spin-independent at theta=pi/2)
 * WHY: At theta=pi/2, Sigma = r^2 regardless of spin, so K = 48 M^2/r^6.
 * ======================================================================= */
bool testKretschmannEquatorial() {
    std::cout << "Test 5: Kretschmann equatorial is spin-independent\n";

    const double mGeo = mGeoTest();
    const double r    = 8.0 * mGeo;

    const double k0   = kerrKretschmann(r, 0.0, mGeo, 0.0);          /* Schwarzschild */
    const double k068 = kerrKretschmann(r, 0.0, mGeo, aTest());       /* a* = 0.68 */
    const double k099 = kerrKretschmann(r, 0.0, mGeo, 0.99 * mGeo);  /* near-extreme */

    const double expected = 48.0 * mGeo * mGeo / std::pow(r, 6.0);

    char buf[256];
    (void)std::snprintf(buf, sizeof(buf),
                        "K(a=0)=%.6e, K(a*=0.68)=%.6e, K(a*=0.99)=%.6e, expected=%.6e",
                        k0, k068, k099, expected);

    const double tol = 1.0e-12;
    check(std::abs(k0   - expected) / expected < tol,
          "K equatorial a=0 matches 48M^2/r^6", buf);
    check(std::abs(k068 - expected) / expected < tol,
          "K equatorial a*=0.68 matches 48M^2/r^6", buf);
    check(std::abs(k099 - expected) / expected < tol,
          "K equatorial a*=0.99 matches 48M^2/r^6", buf);
    return true;
}

/* =========================================================================
 * Test 6: Petrov Type D identity: K = 48 |Psi_2|^2 to < 1e-12 relative error
 * ======================================================================= */
bool testPetrovTypeDIdentity() {
    std::cout << "Test 6: Petrov Type D -- K = 48 |Psi_2|^2 everywhere\n";

    const double mGeo = mGeoTest();
    const double a    = aTest();

    const double testCases[5][2] = {
        {3.5 * mGeo,  0.0},
        {5.0 * mGeo,  0.5},
        {10.0 * mGeo, -0.7},
        {2.0 * mGeo,  0.9},
        {50.0 * mGeo, 0.1}
    };

    bool ok = true;
    for (const auto& tc : testCases) {
        const double relErr = petrovTypeDCheck(tc[0], tc[1], mGeo, a);
        char buf[128];
        (void)std::snprintf(buf, sizeof(buf),
                            "r=%g M, c=%.1f: relErr=%.2e", tc[0] / mGeo, tc[1], relErr);
        if (relErr > 1.0e-12) {
            std::cout << "  [FAIL] " << buf << "\n";
            gAllPass = false;
            ok = false;
        }
    }
    if (ok) { check(true, "K = 48|Psi_2|^2 at all test points (relErr < 1e-12)"); }
    return ok;
}

/* =========================================================================
 * Test 7: Kretschmann is finite and positive at outer horizon r_+.
 * r_+ = M_geo + sqrt(M_geo^2 - a^2); K = 48 M_geo^2 / Sigma(r_+)^3
 * ======================================================================= */
bool testKretschmannAtHorizon() {
    std::cout << "Test 7: Kretschmann is finite and positive at outer horizon\n";

    const double mGeo = mGeoTest();
    const double a    = aTest();

    /* Outer horizon radius r_+ = M + sqrt(M^2 - a^2) */
    const double rPlus = mGeo + std::sqrt((mGeo * mGeo) - (a * a));

    /* Test at several polar angles */
    const double cosVals[] = {0.0, 0.5, -0.5, 1.0 / std::numbers::sqrt2};
    bool ok = true;
    for (const double c : cosVals) {
        const double k = kerrKretschmann(rPlus, c, mGeo, a);
        char buf[128];
        (void)std::snprintf(buf, sizeof(buf), "K(r_+, cos=%g) = %.4e", c, k);
        if (!(k > 0.0) || !safeIsfinite(k)) {
            std::cout << "  [FAIL] " << buf << " (not positive finite)\n";
            gAllPass = false;
            ok = false;
        }
    }
    if (ok) { check(true, "K(r_+, theta) is finite and positive for all theta"); }
    return ok;
}

/* =========================================================================
 * Test 8: Ring singularity guard.
 * At r=0, cos theta=0 (equatorial), a != 0: Sigma=0.
 * kerrWeylPsi2 must return {0,0} (guard); kerrKretschmann must return +inf.
 * ======================================================================= */
bool testRingSingularityGuard() {
    std::cout << "Test 8: Ring singularity guard (r=0, equatorial, a!=0)\n";

    const double mGeo = mGeoTest();
    const double a    = aTest();

    /* Ring singularity: r=0, theta=pi/2 (cos=0) */
    const double sigma = kerrSigma(0.0, 0.0, a);
    check(sigma == 0.0, "Sigma = 0 at ring singularity");

    const NPWeylPsi2 psi2 = kerrWeylPsi2(0.0, 0.0, mGeo, a);
    check(psi2.re == 0.0 && psi2.im == 0.0,
          "kerrWeylPsi2 returns (0,0) at Sigma=0 (guard)");

    const double k = kerrKretschmann(0.0, 0.0, mGeo, a);
    check(!safeIsfinite(k) || k > 1.0e100,
          "kerrKretschmann returns +inf (or very large) at Sigma=0");
    return true;
}

/* =========================================================================
 * Test 9: Large-r falloff K ~ 48 M^2 / r^6 (leading asymptotic).
 * At r >> M, Sigma ~ r^2, so K ~ 48 M^2/r^6.
 * The relative difference from 48 M^2/r^6 should be < (a/r)^2.
 * ======================================================================= */
bool testLargeRFalloff() {
    std::cout << "Test 9: Large-r falloff K ~ 48 M^2/r^6\n";

    const double mGeo = mGeoTest();
    const double a    = aTest();

    /* At r = 1e6 M, (a/r)^2 < 1e-12 for a* <= 1 */
    const double r        = 1.0e6 * mGeo;
    const double cosTheta = 0.3; /* off-equatorial to test cos-theta corrections */

    const double k        = kerrKretschmann(r, cosTheta, mGeo, a);
    const double expected = 48.0 * mGeo * mGeo / std::pow(r, 6.0);
    const double relErr   = std::abs(k - expected) / expected;

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "K=%.6e, 48M^2/r^6=%.6e, relErr=%.2e",
                        k, expected, relErr);
    /* (a/r)^2 ~ (a_star * M / 1e6 M)^2 = a_star^2 * 1e-12 << 1 */
    check(relErr < 1.0e-9, "K -> 48M^2/r^6 at r = 1e6 M (relErr < 1e-9)", buf);
    return true;
}

/* =========================================================================
 * Test 10: Kinnersley n^mu ingoing vector: n^r < 0 for r > r_+ (inward).
 * Also verifies n^t > 0 (future-directed).
 * ======================================================================= */
bool testKinnersleyNVector() {
    std::cout << "Test 10: Kinnersley n^mu is ingoing (n^r < 0) outside horizon\n";

    const double mGeo = mGeoTest();
    const double a    = aTest();

    /* Evaluate at r = 6 M (equatorial) */
    const double r = 6.0 * mGeo;
    double nT  = 0.0;
    double nR  = 0.0;
    double nPhi = 0.0;
    kinnersleyN(r, 0.0, mGeo, a, nT, nR, nPhi);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "n^t=%.4f, n^r=%.4f, n^phi=%.4f", nT, nR, nPhi);
    check(nT > 0.0, "n^t > 0 (future-directed)", buf);
    check(nR < 0.0, "n^r < 0 at r=6M (ingoing null direction)", buf);

    /* Verify n^r = -Delta / (2 Sigma) at equatorial theta=pi/2 */
    const double sigma  = kerrSigma(r, 0.0, a);
    const double delta  = kerrDelta(r, mGeo, a);
    const double nRExact = -delta / (2.0 * sigma);
    const double relErr  = std::abs(nR - nRExact) / std::abs(nRExact);
    (void)std::snprintf(buf, sizeof(buf), "n^r=%.6e exact=%.6e relErr=%.2e", nR, nRExact, relErr);
    check(relErr < 1.0e-12, "n^r = -Delta/(2 Sigma) exactly", buf);
    return true;
}

} // namespace

/* =========================================================================
 * Main
 * ======================================================================= */
int main() {
    std::cout << "\n================================================\n"
              << "NEWMAN-PENROSE NULL TETRAD VALIDATION (KERR)\n"
              << "Physics: Kinnersley 1969 + Chandrasekhar 1983\n"
              << "================================================\n\n";

    testSchwarzschild();             std::cout << "\n";
    testEquatorialImaginary();       std::cout << "\n";
    testPsi2ModSq();                 std::cout << "\n";
    testKretschmannSchwarzschild();  std::cout << "\n";
    testKretschmannEquatorial();     std::cout << "\n";
    testPetrovTypeDIdentity();       std::cout << "\n";
    testKretschmannAtHorizon();      std::cout << "\n";
    testRingSingularityGuard();      std::cout << "\n";
    testLargeRFalloff();             std::cout << "\n";
    testKinnersleyNVector();         std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
