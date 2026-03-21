/**
 * @file tests/analytic_geodesic_reproducibility_test.cpp
 * @brief Validation tests for analytic_kerr_geodesic.h and reproducibility.h.
 *
 * WHY: Both headers had zero test coverage.
 *   analytic_kerr_geodesic.h provides O(1) Kerr null-geodesic evaluation via
 *   Jacobi elliptic functions (vs. O(N) numerical RK4). Its photon-sphere
 *   limits are analytic and exact.
 *   reproducibility.h records build and physics metadata for scientific outputs.
 *
 * Tests (15):
 *   Photon sphere (radialPotential + criticalImpactParams) (1-4):
 *   1.  radialPotential(r=3, a=0, xi=0, eta=27) == 0  (Schwarzschild photon sphere)
 *   2.  criticalImpactParams(r=3, a=0) == {xi=0, eta=27}
 *   3.  R(r_ph, a, xi_c, eta_c) == 0 for a=0.5 (Kerr self-consistency)
 *   4.  radialPotential positive away from photon sphere (xi=0, eta=27, r != 3)
 *   Photon orbit radii (5-9):
 *   5.  progradePhotonOrbit(0.0) == 3.0  (Schwarzschild)
 *   6.  retrogradePhotonOrbit(0.0) == 3.0  (Schwarzschild)
 *   7.  progradePhotonOrbit(1.0) == 1.0  (extremal Kerr prograde)
 *   8.  retrogradePhotonOrbit(1.0) == 4.0  (extremal Kerr retrograde)
 *   9.  progradePhotonOrbit monotonically decreasing, retrograde increasing
 *   Reproducibility manifest (10-15):
 *  10.  buildManifest() returns non-empty manifest
 *  11.  get("code") == "Blackhole"
 *  12.  get("build_type") is "Release" or "Debug"  (non-empty, valid)
 *  13.  add(key, double) / get() round-trip with setprecision(15)
 *  14.  add(key, int) / get() round-trip
 *  15.  addPhysicsParams() populates mass and spin via get()
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>
#include <string>

#include "../src/physics/analytic_kerr_geodesic.h"
#include "../src/physics/reproducibility.h"

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

// ============================================================================
// Tests 1-4: Radial potential at the photon sphere
// ============================================================================

bool testRadialPotentialSchwarzschildPhotonSphere() {
    std::cout << "Test 1: radialPotential(r=3, a=0, xi=0, eta=27) == 0  (photon sphere)\n";

    // For Schwarzschild (a=0, M=1), the photon sphere at r=3 satisfies R(3) = 0.
    // Convention: xi=L/E=0 (equatorial, azimuthal symmetry broken) + eta=b^2=27
    // => R(3) = (9)^2 - (9-6)*(27) = 81 - 81 = 0.
    const double rVal = radialPotential(3.0, 0.0, 0.0, 27.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "R(3, 0, 0, 27) = %.6e (expected 0)", rVal); // NOLINT(cert-err33-c)
    check(std::abs(rVal) < 1.0e-10, "R(r_ph, a=0, xi=0, eta=27) = 0", buf);
    return true;
}

bool testCriticalImpactParamsSchwarzschild() {
    std::cout << "Test 2: criticalImpactParams(r=3, a=0) == {xi=0, eta=27}\n";

    const ImpactParams ip = criticalImpactParams(3.0, 0.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "xi=%.4f, eta=%.4f  (expected xi=0, eta=27)", ip.xi, ip.eta); // NOLINT(cert-err33-c)
    check(std::abs(ip.xi) < 1.0e-12 && std::abs(ip.eta - 27.0) < 1.0e-10,
          "criticalImpactParams(r=3, a=0) = {0, 27}", buf);
    return true;
}

bool testCriticalImpactParamsKerrSelfConsistency() {
    std::cout << "Test 3: R(r_ph, a, xi_c, eta_c) == 0 for a=0.5  (self-consistency)\n";

    // Get prograde photon orbit radius for a=0.5, then verify R=0 there.
    const double a   = 0.5;
    const double rPh = progradePhotonOrbit(a);
    const ImpactParams ip = criticalImpactParams(rPh, a);
    const double rVal = radialPotential(rPh, a, ip.xi, ip.eta);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "r_ph=%.6f, R(r_ph)=%.4e", rPh, rVal); // NOLINT(cert-err33-c)
    check(std::abs(rVal) < 1.0e-8,
          "R(r_ph, a=0.5, xi_c, eta_c) = 0  (self-consistency)", buf);
    return true;
}

bool testRadialPotentialPositiveOffPhotonSphere() {
    std::cout << "Test 4: radialPotential(r != 3, a=0, xi=0, eta=27) > 0  (no turning pt)\n";

    // For Schwarzschild, R(r) = r(r-3)^2(r+6) >= 0 for r>0.  Check r=2 and r=5.
    const double rIn  = radialPotential(2.0, 0.0, 0.0, 27.0);
    const double rOut = radialPotential(5.0, 0.0, 0.0, 27.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "R(2)=%.4f, R(5)=%.4f  (both expected > 0)", rIn, rOut); // NOLINT(cert-err33-c)
    check(rIn > 0.0 && rOut > 0.0,
          "R(2) > 0 and R(5) > 0 for Schwarzschild critical orbit", buf);
    return true;
}

// ============================================================================
// Tests 5-9: Photon orbit radii
// ============================================================================

bool testProgradePhotonOrbitSchwarzschild() {
    std::cout << "Test 5: progradePhotonOrbit(0.0) == 3.0  (Schwarzschild limit)\n";

    const double r = progradePhotonOrbit(0.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "r_ph(a=0) = %.12f  (expected 3.0)", r); // NOLINT(cert-err33-c)
    check(std::abs(r - 3.0) < 1.0e-12, "progradePhotonOrbit(0) = 3", buf);
    return true;
}

bool testRetrogradePhotonOrbitSchwarzschild() {
    std::cout << "Test 6: retrogradePhotonOrbit(0.0) == 3.0  (Schwarzschild limit)\n";

    const double r = retrogradePhotonOrbit(0.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "r_ph_retro(a=0) = %.12f  (expected 3.0)", r); // NOLINT(cert-err33-c)
    check(std::abs(r - 3.0) < 1.0e-12, "retrogradePhotonOrbit(0) = 3", buf);
    return true;
}

bool testProgradePhotonOrbitExtremal() {
    std::cout << "Test 7: progradePhotonOrbit(1.0) == 1.0  (extremal Kerr)\n";

    // r_ph = 2*(1 + cos(2/3*acos(-1))) = 2*(1 + cos(2pi/3)) = 2*(1 - 1/2) = 1
    const double r = progradePhotonOrbit(1.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "r_ph(a=1) = %.12f  (expected 1.0)", r); // NOLINT(cert-err33-c)
    check(std::abs(r - 1.0) < 1.0e-12, "progradePhotonOrbit(1) = 1", buf);
    return true;
}

bool testRetrogradePhotonOrbitExtremal() {
    std::cout << "Test 8: retrogradePhotonOrbit(1.0) == 4.0  (extremal Kerr)\n";

    // r_ph = 2*(1 + cos(2/3*acos(1))) = 2*(1 + cos(0)) = 2*(1 + 1) = 4
    const double r = retrogradePhotonOrbit(1.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "r_ph_retro(a=1) = %.12f  (expected 4.0)", r); // NOLINT(cert-err33-c)
    check(std::abs(r - 4.0) < 1.0e-12, "retrogradePhotonOrbit(1) = 4", buf);
    return true;
}

bool testPhotonOrbitMonotonicity() {
    std::cout << "Test 9: progradePhotonOrbit decreasing, retrograde increasing with spin\n";

    // Prograde: 3 > r_ph(0.5) > 1  (orbit tightens with prograde spin)
    // Retrograde: 3 < r_ph_retro(0.5) < 4  (orbit widens with retrograde spin)
    const double rPro0  = progradePhotonOrbit(0.0);
    const double rPro5  = progradePhotonOrbit(0.5);
    const double rPro1  = progradePhotonOrbit(1.0);
    const double rRet0  = retrogradePhotonOrbit(0.0);
    const double rRet5  = retrogradePhotonOrbit(0.5);
    const double rRet1  = retrogradePhotonOrbit(1.0);
    const bool proDecr  = (rPro0 > rPro5) && (rPro5 > rPro1);
    const bool retIncr  = (rRet0 < rRet5) && (rRet5 < rRet1);
    char buf[256];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "pro: %.3f>%.3f>%.3f  retro: %.3f<%.3f<%.3f",
        rPro0, rPro5, rPro1, rRet0, rRet5, rRet1);
    check(proDecr && retIncr,
          "prograde decreasing, retrograde increasing with spin", buf);
    return true;
}

// ============================================================================
// Tests 10-15: Reproducibility manifest
// ============================================================================

bool testManifestNonEmpty() {
    std::cout << "Test 10: buildManifest() returns non-empty manifest\n";

    const ReproducibilityManifest m = buildManifest();
    check(!m.entries.empty(), "buildManifest().entries is non-empty");
    return true;
}

bool testManifestCodeKey() {
    std::cout << "Test 11: get(\"code\") == \"Blackhole\"\n";

    const ReproducibilityManifest m = buildManifest();
    const std::string code = m.get("code");
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), R"(code="%s" (expected "Blackhole"))", code.c_str()); // NOLINT(cert-err33-c)
    check(code == "Blackhole", R"(get("code") = "Blackhole")", buf);
    return true;
}

bool testManifestBuildType() {
    std::cout << "Test 12: get(\"build_type\") is \"Release\" or \"Debug\"\n";

    const ReproducibilityManifest m = buildManifest();
    const std::string bt = m.get("build_type");
    const bool valid = (bt == "Release") || (bt == "Debug");
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "build_type=\"%s\"", bt.c_str()); // NOLINT(cert-err33-c)
    check(valid, "build_type is Release or Debug", buf);
    return true;
}

bool testManifestAddDoubleRoundTrip() {
    std::cout << "Test 13: add(key, double) / get() round-trip (setprecision(15))\n";

    ReproducibilityManifest m;
    const double val = std::numbers::pi;
    m.add("pi_test", val);
    const std::string stored = m.get("pi_test");
    // setprecision(15) gives ~15 significant digits; reconstruct and compare.
    const double recovered = std::stod(stored);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "stored=\"%s\", recovered=%.15f", stored.c_str(), recovered); // NOLINT(cert-err33-c)
    check(std::abs(recovered - val) / val < 1.0e-14,
          "add/get double round-trip to within 1e-14", buf);
    return true;
}

bool testManifestAddIntRoundTrip() {
    std::cout << "Test 14: add(key, int) / get() round-trip\n";

    ReproducibilityManifest m;
    m.add("nx_test", 1920);
    const std::string stored = m.get("nx_test");
    const int recovered = std::stoi(stored);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "stored=\"%s\" -> %d", stored.c_str(), recovered); // NOLINT(cert-err33-c)
    check(recovered == 1920, "add/get int round-trip for 1920", buf);
    return true;
}

bool testManifestAddPhysicsParams() {
    std::cout << "Test 15: addPhysicsParams() populates bh_mass_msun and bh_spin\n";

    ReproducibilityManifest m;
    addPhysicsParams(m, 6.5e9, 0.9375, 17.0, 230.0e9, 1024, 1024, 160.0);
    const double mass = std::stod(m.get("bh_mass_msun"));
    const double spin = std::stod(m.get("bh_spin"));
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "mass=%.4e, spin=%.4f", mass, spin); // NOLINT(cert-err33-c)
    check(std::abs(mass - 6.5e9) / 6.5e9 < 1.0e-12 &&
          std::abs(spin - 0.9375) < 1.0e-12,
          "addPhysicsParams: mass=6.5e9 Msun, spin=0.9375 recovered", buf);
    return true;
}

} // namespace

// NOLINTNEXTLINE(bugprone-exception-escape) -- test binary; exceptions propagate to crash
int main() {
    std::cout << "\n================================================\n"
              << "ANALYTIC KERR GEODESIC + REPRODUCIBILITY VALIDATION\n"
              << "analytic_kerr_geodesic.h + reproducibility.h\n"
              << "================================================\n\n";

    testRadialPotentialSchwarzschildPhotonSphere(); std::cout << "\n";
    testCriticalImpactParamsSchwarzschild();        std::cout << "\n";
    testCriticalImpactParamsKerrSelfConsistency();  std::cout << "\n";
    testRadialPotentialPositiveOffPhotonSphere();   std::cout << "\n";
    testProgradePhotonOrbitSchwarzschild();         std::cout << "\n";
    testRetrogradePhotonOrbitSchwarzschild();       std::cout << "\n";
    testProgradePhotonOrbitExtremal();              std::cout << "\n";
    testRetrogradePhotonOrbitExtremal();            std::cout << "\n";
    testPhotonOrbitMonotonicity();                  std::cout << "\n";
    testManifestNonEmpty();                         std::cout << "\n";
    testManifestCodeKey();                          std::cout << "\n";
    testManifestBuildType();                        std::cout << "\n";
    testManifestAddDoubleRoundTrip();               std::cout << "\n";
    testManifestAddIntRoundTrip();                  std::cout << "\n";
    testManifestAddPhysicsParams();                 std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
