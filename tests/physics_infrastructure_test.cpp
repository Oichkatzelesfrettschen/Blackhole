/**
 * @file tests/physics_infrastructure_test.cpp
 * @brief Validation tests for conservation_monitor.h, event_detection.h,
 *        source_presets.h, and unit_system.h.
 *
 * WHY: Four infrastructure headers had zero test coverage despite being
 *      used by the geodesic integrator and observational pipeline.
 *      Analytic limits and round-trip identities verify their correctness.
 *
 * Tests (18):
 *   Conservation monitor (1-5):
 *   1.  computeConserved: E = sqrt(1-2M/r) for Schwarzschild static observer
 *   2.  computeConserved: L_z = 0 for radial motion (u^phi=0, a=0)
 *   3.  GeodesicConservationMonitor: zero drift when state unchanged
 *   4.  GeodesicConservationMonitor: violated() = false at zero drift
 *   5.  GeodesicConservationMonitor: maxDrift() tracks 1% E perturbation
 *   Event detection (6-11):
 *   6.  crossedRadius: detects r0->r1 sign change across rTarget
 *   7.  crossedRadius: no detection when both r0, r1 on same side
 *   8.  hasTurningPoint: sign change in vr detected
 *   9.  hasTurningPoint: same-sign vr not detected
 *  10.  crossedEquator: theta crossing pi/2 detected
 *  11.  bisectRadialCrossing: locates r=rTarget within 1e-6 tolerance
 *   Source presets (12-15):
 *  12.  sourceM87: mass=6.5e9 Msun, spin in [0,1)
 *  13.  sourceSgra: mass=4.0e6 Msun, spin in [0,1)
 *  14.  sourceM87: shadow diameter in [38, 46] uas  (EHT: 42+-3 uas)
 *  15.  sourceSgra: angular scale in [4, 6] uas/r_g
 *   Unit system (16-18):
 *  16.  massCgsToGeom / massGeomToCgs: round-trip for 1 Msun
 *  17.  rS(1.0 Msun) == R_SCHW_SUN from constants.h
 *  18.  radToUas / uasToRad: round-trip
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>

#include "../src/physics/conservation_monitor.h"
#include "../src/physics/constants.h"
#include "../src/physics/event_detection.h"
#include "../src/physics/source_presets.h"
#include "../src/physics/unit_system.h"

using namespace physics;
using namespace physics::units;

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
// Tests 1-5: Conservation monitor
// ============================================================================

bool testComputeConservedEnergy() {
    std::cout << "Test 1: computeConserved E = sqrt(1-2M/r) for Schwarzschild static observer\n";

    // Static observer at r=100, theta=pi/2, Schwarzschild (a=0, mGeom=1).
    // g_tt = -(1 - 2M/r).  Static 4-velocity: u^t = 1/sqrt(-g_tt), rest = 0.
    // E = -g_tt * u^t = sqrt(1 - 2M/r).
    const double r     = 100.0;
    const double theta = std::numbers::pi / 2.0;
    const double mGeom = 1.0;
    const double a     = 0.0;

    const double gTt = -(1.0 - 2.0 * mGeom / r);
    const double ut  = 1.0 / std::sqrt(-gTt);

    const ConservedQuantities cq =
        computeConserved(r, theta, ut, 0.0, 0.0, 0.0, mGeom, a);
    const double expected = std::sqrt(1.0 - 2.0 * mGeom / r);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "E = %.10f, expected = %.10f", cq.e, expected);
    check(std::abs(cq.e - expected) < 1.0e-12,
          "E = sqrt(1-2M/r) for static observer at r=100M", buf);
    return true;
}

bool testComputeConservedLzRadial() {
    std::cout << "Test 2: computeConserved L_z = 0 for radial motion (u^phi=0, a=0)\n";

    // In Schwarzschild (a=0), g_tphi = 0 identically.
    // L_z = g_tphi * u^t + g_phiphi * u^phi = 0 for any radial motion.
    const ConservedQuantities cq =
        computeConserved(50.0, std::numbers::pi / 2.0,
                         1.0, -0.5, 0.0, 0.0,
                         1.0, 0.0);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "L_z = %.4e (expected 0)", cq.lz); // NOLINT(cert-err33-c)
    check(std::abs(cq.lz) < 1.0e-14,
          "L_z = 0 for radial geodesic in Schwarzschild", buf);
    return true;
}

bool testMonitorZeroDrift() {
    std::cout << "Test 3: GeodesicConservationMonitor -- zero drift when state unchanged\n";

    GeodesicConservationMonitor mon;
    ConservedQuantities cq0;
    cq0.e = 0.95; cq0.lz = 3.5; cq0.q = 1.2; cq0.mu2 = 0.0;

    mon.init(cq0);
    const double drift = mon.update(cq0);  // same state

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "drift = %.4e (expected 0)", drift); // NOLINT(cert-err33-c)
    check(drift < 1.0e-14, "monitor.update(same) -> drift = 0", buf);
    return true;
}

bool testMonitorViolated() {
    std::cout << "Test 4: GeodesicConservationMonitor -- violated() = false at zero drift\n";

    GeodesicConservationMonitor mon;
    ConservedQuantities cq0;
    cq0.e = 0.95; cq0.lz = 3.5; cq0.q = 1.2; cq0.mu2 = 0.0;

    mon.init(cq0);
    (void)mon.update(cq0);

    check(!mon.violated(1.0e-8), "violated(1e-8) = false when drift = 0");
    return true;
}

bool testMonitorMaxDrift() {
    std::cout << "Test 5: GeodesicConservationMonitor -- maxDrift() tracks 1% E perturbation\n";

    GeodesicConservationMonitor mon;
    ConservedQuantities cq0;
    cq0.e = 1.0; cq0.lz = 2.0; cq0.q = 0.5; cq0.mu2 = 0.0;

    mon.init(cq0);

    ConservedQuantities cq1 = cq0;
    cq1.e = 1.01;  // 1% perturbation in E
    (void)mon.update(cq1);

    const double drift = mon.maxDrift();
    // relDrift(1.0, 1.01) = |1.01 - 1.0| / max(|1.0|, 1e-30) = 0.01
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "maxDrift = %.6e (expected 0.01)", drift); // NOLINT(cert-err33-c)
    check(std::abs(drift - 0.01) < 1.0e-10,
          "maxDrift = 0.01 for 1% E perturbation", buf);
    return true;
}

// ============================================================================
// Tests 6-11: Event detection
// ============================================================================

bool testCrossedRadiusYesNo() {
    std::cout << "Test 6: crossedRadius -- detects sign change, not same-side\n";

    // 5 -> 3 crosses rTarget=4; 5 -> 6 does not.
    const bool yes = crossedRadius(5.0, 3.0, 4.0);
    const bool no  = crossedRadius(5.0, 6.0, 4.0);
    check(yes && !no,
          "crossedRadius(5->3, 4)=true and crossedRadius(5->6, 4)=false");
    return true;
}

bool testHasTurningPointYesNo() {
    std::cout << "Test 7: hasTurningPoint -- sign change in vr detected\n";

    const bool yes = hasTurningPoint(1.0, -1.0);
    const bool no  = hasTurningPoint(1.0,  0.5);
    check(yes && !no,
          "hasTurningPoint(+1,-1)=true and hasTurningPoint(+1,+0.5)=false");
    return true;
}

bool testCrossedEquator() {
    std::cout << "Test 8: crossedEquator -- theta crossing pi/2 detected\n";

    // pi/2 ~ 1.5708, so [1.0, 2.0] brackets it; [0.1, 0.5] does not.
    const bool yes = crossedEquator(1.0, 2.0);
    const bool no  = crossedEquator(0.1, 0.5);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "[1->2]: %s, [0.1->0.5]: %s  (pi/2=%.4f)",
        yes ? "true" : "false", no ? "true" : "false",
        std::numbers::pi / 2.0);
    check(yes && !no, "crossedEquator: 1->2 crosses pi/2; 0.1->0.5 does not", buf);
    return true;
}

bool testPhotonSubringIndex() {
    std::cout << "Test 9: photonSubringIndex(n) = n  (identity function)\n";

    check(photonSubringIndex(0) == 0 &&
          photonSubringIndex(1) == 1 &&
          photonSubringIndex(2) == 2,
          "photonSubringIndex returns its argument unchanged");
    return true;
}

struct MockState {
    double x1;  // r (radial coordinate)
    double x2;  // theta (polar angle)
    double v1;  // dr/dlambda
};

bool testBisectRadialCrossing() {
    std::cout << "Test 10: bisectRadialCrossing -- locates r=rTarget within 1e-6\n";

    // r(lambda) = 5.0 - 2.0 * lambda  crosses r=4.0 at lambda=0.5 exactly.
    const MockState state0{5.0, std::numbers::pi / 2.0, -2.0};

    auto stepper = [](double /*la*/, double lb, MockState /*sa*/) -> MockState {
        return MockState{5.0 - 2.0 * lb, std::numbers::pi / 2.0, -2.0};
    };

    const EventResult ev =
        bisectRadialCrossing(0.0, 1.0, state0, 4.0, stepper, 1.0e-8, 60);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "r_cross = %.10f (expected 4.0), lambda = %.10f (expected 0.5)",
        ev.r, ev.lambda);
    check(ev.detected && std::abs(ev.r - 4.0) < 1.0e-6,
          "bisectRadialCrossing finds r=4.0 to within 1e-6", buf);
    return true;
}

// ============================================================================
// Tests 11-14: Source presets (EHT calibration targets)
// ============================================================================

bool testM87Preset() {
    std::cout << "Test 11: sourceM87 -- mass=6.5e9 Msun, spin in [0,1)\n";

    const SourceParams m87 = sourceM87();
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "mass=%.2e Msun, spin=%.4f", m87.massMsun, m87.spin);
    check(m87.massMsun == 6.5e9 && m87.spin >= 0.0 && m87.spin < 1.0,
          "M87*: mass=6.5e9 Msun, spin in [0,1)  (EHT 2019)", buf);
    return true;
}

bool testSgraPreset() {
    std::cout << "Test 12: sourceSgra -- mass=4.0e6 Msun, spin in [0,1)\n";

    const SourceParams sgra = sourceSgra();
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "mass=%.2e Msun, spin=%.4f", sgra.massMsun, sgra.spin);
    check(sgra.massMsun == 4.0e6 && sgra.spin >= 0.0 && sgra.spin < 1.0,
          "Sgr A*: mass=4.0e6 Msun, spin in [0,1)  (EHT 2022)", buf);
    return true;
}

bool testM87ShadowDiameter() {
    std::cout << "Test 13: sourceM87 shadow diameter in [38, 46] uas  (EHT: 42+-3 uas)\n";

    // shadowDiameterUas = 10.4 * r_g / D * RAD_TO_UAS
    // With M87* constants this evaluates to ~39.7 uas.
    // EHT 2019 measured 42+-3 uas; 10.4 r_g is the Schwarzschild formula.
    const SourceParams m87 = sourceM87();
    const double shadow    = m87.shadowDiameterUas();
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "shadow = %.2f uas  (EHT: 42+-3 uas)", shadow);
    check(shadow > 38.0 && shadow < 46.0,
          "M87* shadow diameter in [38, 46] uas", buf);
    return true;
}

bool testSgraAngularScale() {
    std::cout << "Test 14: sourceSgra angular scale in [4, 6] uas/r_g\n";

    // r_g / D for Sgr A* at 8.178 kpc: ~4.8 uas per gravitational radius.
    // EHT 2022 shadow ~50 uas => ~50/10.4 ~ 4.8 uas/r_g.
    const SourceParams sgra = sourceSgra();
    const double scale      = sgra.angularScaleUas();
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "angular scale = %.3f uas/r_g", scale);
    check(scale > 4.0 && scale < 6.0,
          "Sgr A* angular scale in [4, 6] uas/r_g", buf);
    return true;
}

// ============================================================================
// Tests 15-18: Unit system conversions
// ============================================================================

bool testMassRoundTrip() {
    std::cout << "Test 15: massCgsToGeom / massGeomToCgs -- round-trip for 1 Msun\n";

    const double mCgs  = M_SUN;
    const double mGeom = massCgsToGeom(mCgs);
    const double mBack = massGeomToCgs(mGeom);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "M_SUN -> %.10e g (expected %.10e g)", mBack, mCgs);
    check(std::abs(mBack - mCgs) / mCgs < 1.0e-14,
          "mass CGS -> geom -> CGS round-trip for 1 Msun", buf);
    return true;
}

bool testSchwarzschildRadius() {
    std::cout << "Test 16: rS(1.0 Msun) == R_SCHW_SUN from constants.h\n";

    // rS = 2 * G * M_SUN / C2, independently computed in both places.
    const double computed = rS(1.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "rS(1 Msun) = %.10e cm,  R_SCHW_SUN = %.10e cm", computed, R_SCHW_SUN);
    check(std::abs(computed - R_SCHW_SUN) / R_SCHW_SUN < 1.0e-14,
          "rS(1 Msun) == R_SCHW_SUN", buf);
    return true;
}

bool testAngleRoundTrip() {
    std::cout << "Test 17: radToUas / uasToRad -- round-trip\n";

    const double angle = 1.23456789e-10;
    const double uas   = radToUas(angle);
    const double back  = uasToRad(uas);

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "angle=%.10e -> %.4f uas -> %.10e rad", angle, uas, back);
    check(std::abs(back - angle) / angle < 1.0e-14,
          "radToUas / uasToRad round-trip", buf);
    return true;
}

bool testMassMsunToGeomRelation() {
    std::cout << "Test 18: 2 * massMsunToGeom(1) == rS(1) == R_SCHW_SUN\n";

    // r_s = 2 * r_g; massMsunToGeom gives r_g = G*M/c^2.
    const double twice_rg = 2.0 * massMsunToGeom(1.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
        "2*r_g = %.10e cm,  R_SCHW_SUN = %.10e cm", twice_rg, R_SCHW_SUN);
    check(std::abs(twice_rg - R_SCHW_SUN) / R_SCHW_SUN < 1.0e-14,
          "2 * massMsunToGeom(1) == R_SCHW_SUN", buf);
    return true;
}

} // namespace

// NOLINTNEXTLINE(bugprone-exception-escape) -- test binary; exceptions propagate to crash
int main() {
    std::cout << "\n================================================\n"
              << "PHYSICS INFRASTRUCTURE VALIDATION\n"
              << "conservation_monitor + event_detection + source_presets + unit_system\n"
              << "================================================\n\n";

    testComputeConservedEnergy();    std::cout << "\n";
    testComputeConservedLzRadial();  std::cout << "\n";
    testMonitorZeroDrift();          std::cout << "\n";
    testMonitorViolated();           std::cout << "\n";
    testMonitorMaxDrift();           std::cout << "\n";
    testCrossedRadiusYesNo();        std::cout << "\n";
    testHasTurningPointYesNo();      std::cout << "\n";
    testCrossedEquator();            std::cout << "\n";
    testPhotonSubringIndex();        std::cout << "\n";
    testBisectRadialCrossing();      std::cout << "\n";
    testM87Preset();                 std::cout << "\n";
    testSgraPreset();                std::cout << "\n";
    testM87ShadowDiameter();         std::cout << "\n";
    testSgraAngularScale();          std::cout << "\n";
    testMassRoundTrip();             std::cout << "\n";
    testSchwarzschildRadius();       std::cout << "\n";
    testAngleRoundTrip();            std::cout << "\n";
    testMassMsunToGeomRelation();    std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
