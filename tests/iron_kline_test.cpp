/**
 * @file tests/iron_kline_test.cpp
 * @brief Validation tests for the Fe K-alpha relativistic line profile (iron_kline.h).
 *
 * WHY: The Laor (1991) g-factor and 2-D disk integral must satisfy several
 *      analytically verifiable limits before being trusted for X-ray spectral
 *      comparison.  Any regression in the g-factor formula or the normalization
 *      convention changes synthetic spectra in ways that are not immediately
 *      obvious from visual inspection of the profile alone.
 *
 * Tests (10):
 *   1. g-factor at Schwarzschild ISCO face-on = sqrt(1/2) (pure gravitational redshift).
 *   2. g-factor > 1 on approaching side (phi=pi/2) for edge-on view (Doppler boost).
 *   3. g-factor < 1 on receding side (phi=3pi/2) for edge-on view (Doppler redshift).
 *   4. g-factor -> 1 for large r (flat spacetime limit).
 *   5. Profile integral = 1.0 +/- 1% (normalization).
 *   6. Profile is non-empty and all energies are positive.
 *   7. Profile minimum energy decreases with spin (higher spin -> smaller ISCO -> lower g_min).
 *   8. Profile width (full range) increases with inclination (Doppler broadening).
 *   9. ironKLineGMin for Schwarzschild = sqrt(0.5) ~ 0.707.
 *  10. All flux values are non-negative.
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>
#include <vector>

#include "../src/physics/iron_kline.h"

using namespace physics;

namespace {

bool gAllPass = true;

void check(bool cond, const char *label, const char *detail = "") {
    if (cond) {
        std::cout << "  [PASS] " << label << "\n";
    } else {
        std::cout << "  [FAIL] " << label;
        if (detail[0] != '\0') {
            std::cout << "  -- " << detail;
        }
        std::cout << "\n";
        gAllPass = false;
    }
}

/* Test 1: g-factor at Schwarzschild ISCO (r=6M, a=0) face-on (iota=0, phi=0). */
bool testGFactorSchwarzschild() {
    std::cout << "Test 1: g-factor at Schwarzschild ISCO face-on = sqrt(0.5)\n";

    const double g        = kerrDiskGFactor(6.0, 0.0, 0.0, 0.0);
    const double expected = std::sqrt(0.5);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "g=%.8f, expected=%.8f", g, expected); // NOLINT(cert-err33-c)
    check(std::abs(g - expected) < 1.0e-12, "g at Schwarzschild ISCO (face-on) = sqrt(0.5)", buf);
    return true;
}

/* Test 2: g > 1 on approaching side (phi=pi/2) for edge-on inclination. */
bool testGFactorApproachingBlueshifted() {
    std::cout << "Test 2: g > 1 on approaching side (phi=pi/2) for edge-on view\n";

    const double iota = std::numbers::pi / 2.0;  // edge-on
    const double g    = kerrDiskGFactor(10.0, std::numbers::pi / 2.0, 0.0, iota);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "g(r=10, phi=pi/2, a=0, iota=pi/2) = %.6f (expected > 1)", g);
    check(g > 1.0, "approaching side is blueshifted (g > 1)", buf);
    return true;
}

/* Test 3: g < 1 on receding side (phi=3pi/2) for edge-on inclination. */
bool testGFactorRecedingRedshifted() {
    std::cout << "Test 3: g < 1 on receding side (phi=3pi/2) for edge-on view\n";

    const double iota = std::numbers::pi / 2.0;
    const double g    = kerrDiskGFactor(10.0, 3.0 * std::numbers::pi / 2.0, 0.0, iota);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "g(r=10, phi=3pi/2, a=0, iota=pi/2) = %.6f (expected < 1)", g);
    check(g < 1.0, "receding side is redshifted (g < 1)", buf);
    return true;
}

/* Test 4: g -> 1 for large r (flat spacetime limit). */
bool testGFactorFlatSpaceLimit() {
    std::cout << "Test 4: g -> 1 for large r (flat spacetime)\n";

    const double iota = std::numbers::pi / 4.0;
    const double g    = kerrDiskGFactor(1.0e6, 0.0, 0.0, iota);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "g(r=1e6, phi=0, a=0, iota=pi/4) = %.8f (expected ~1)", g);
    check(std::abs(g - 1.0) < 1.0e-4, "g -> 1 at large r", buf);
    return true;
}

/* Test 5: Profile integral = 1.0 +/- 1%. */
bool testProfileNormalization() {
    std::cout << "Test 5: profile integral = 1.0 +/- 1%\n";

    IronKLineParams p;
    p.aStar       = 0.0;
    p.inclination = 0.3;
    p.nEnergy     = 300;
    p.nR          = 300;
    p.nPhi        = 600;

    const auto profile = ironKLineProfile(p);

    if (profile.empty()) {
        check(false, "profile is non-empty");
        return false;
    }

    // Trapezoid integration over E (in keV); divide by E0 to get dimensionless g integral
    double integral = 0.0;
    for (std::size_t i = 0; i + 1 < profile.size(); ++i) {
        const double dE = profile.at(i + 1).first - profile.at(i).first;
        integral += 0.5 * (profile.at(i).second + profile.at(i + 1).second) * dE;
    }
    integral /= p.lineEnergyKeV;  // normalize to unit g interval

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "integral = %.4f (expected 1.0 +/- 0.01)", integral);
    check(std::abs(integral - 1.0) < 0.01, "profile integral = 1.0 +/- 1%", buf);
    return true;
}

/* Test 6: Profile is non-empty and all energies and fluxes are positive. */
bool testProfilePositive() {
    std::cout << "Test 6: all profile energies and fluxes are positive\n";

    IronKLineParams p;
    p.aStar       = 0.5;
    p.inclination = 0.5;

    const auto profile = ironKLineProfile(p);

    if (profile.empty()) {
        check(false, "profile is non-empty");
        return false;
    }

    check(!profile.empty(), "profile is non-empty");

    bool allPositive = true;
    for (const auto &pt : profile) {
        if (pt.first <= 0.0 || pt.second < 0.0) {
            allPositive = false;
            break;
        }
    }
    check(allPositive, "all energies > 0 and all fluxes >= 0");
    return true;
}

/* Test 7: Profile minimum energy decreases with spin (more spin -> lower g_min). */
bool testProfileSpinRedshift() {
    std::cout << "Test 7: higher spin -> lower profile minimum energy\n";

    IronKLineParams p;
    p.inclination = 0.2;  // nearly face-on to emphasize gravitational redshift
    p.nEnergy     = 150;
    p.nR          = 150;
    p.nPhi        = 300;

    p.aStar             = 0.0;
    const auto profileA0 = ironKLineProfile(p);

    p.aStar             = 0.9;
    const auto profileA9 = ironKLineProfile(p);

    if (profileA0.empty() || profileA9.empty()) {
        check(false, "both profiles non-empty");
        return false;
    }

    const double eMinA0 = profileA0.front().first;
    const double eMinA9 = profileA9.front().first;

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "E_min(a*=0.0)=%.3f keV, E_min(a*=0.9)=%.3f keV", eMinA0, eMinA9);
    check(eMinA9 < eMinA0, "a*=0.9 profile extends to lower energy than a*=0", buf);
    return true;
}

/* Test 8: Profile width increases with inclination (Doppler broadening). */
bool testProfileInclinationBroadening() {
    std::cout << "Test 8: higher inclination -> broader profile (Doppler broadening)\n";

    IronKLineParams p;
    p.aStar   = 0.0;
    p.nEnergy = 150;
    p.nR      = 150;
    p.nPhi    = 300;

    p.inclination       = 0.1;  // nearly face-on
    const auto profileFace = ironKLineProfile(p);

    p.inclination       = 1.2;  // nearly edge-on
    const auto profileEdge = ironKLineProfile(p);

    if (profileFace.empty() || profileEdge.empty()) {
        check(false, "both profiles non-empty");
        return false;
    }

    const double widthFace = profileFace.back().first - profileFace.front().first;
    const double widthEdge = profileEdge.back().first - profileEdge.front().first;

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "width_face=%.3f keV, width_edge=%.3f keV", widthFace, widthEdge);
    check(widthEdge > widthFace, "edge-on profile wider than face-on", buf);
    return true;
}

/* Test 9: ironKLineGMin for Schwarzschild = sqrt(0.5). */
bool testGMinSchwarzschild() {
    std::cout << "Test 9: ironKLineGMin(a*=0) = sqrt(0.5)\n";

    const double gm       = ironKLineGMin(0.0);
    const double expected = std::sqrt(0.5);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "gMin=%.8f, expected %.8f", gm, expected);
    check(std::abs(gm - expected) < 1.0e-12, "gMin(a*=0) = sqrt(0.5)", buf);
    return true;
}

/* Test 10: All flux values in the profile are non-negative. */
bool testProfileFluxNonNegative() {
    std::cout << "Test 10: all flux values are non-negative\n";

    IronKLineParams p;
    p.aStar       = 0.7;
    p.inclination = 0.7;

    const auto profile = ironKLineProfile(p);

    bool allOk = true;
    for (const auto &pt : profile) {
        if (pt.second < 0.0) {
            allOk = false;
            break;
        }
    }
    check(allOk, "all flux values >= 0");
    return true;
}

} // namespace

// NOLINTNEXTLINE(bugprone-exception-escape) -- test binary; exceptions propagate to crash with useful messages
int main() {
    std::cout << "\n================================================\n"
              << "Fe K-ALPHA RELATIVISTIC LINE PROFILE VALIDATION\n"
              << "Physics: Laor (1991) / Cunningham (1975)\n"
              << "================================================\n\n";

    testGFactorSchwarzschild();            std::cout << "\n";
    testGFactorApproachingBlueshifted();   std::cout << "\n";
    testGFactorRecedingRedshifted();       std::cout << "\n";
    testGFactorFlatSpaceLimit();           std::cout << "\n";
    testProfileNormalization();            std::cout << "\n";
    testProfilePositive();                 std::cout << "\n";
    testProfileSpinRedshift();             std::cout << "\n";
    testProfileInclinationBroadening();    std::cout << "\n";
    testGMinSchwarzschild();               std::cout << "\n";
    testProfileFluxNonNegative();          std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
