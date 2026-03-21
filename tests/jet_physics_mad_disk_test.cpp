/**
 * @file tests/jet_physics_mad_disk_test.cpp
 * @brief Validation tests for jet_physics.h and mad_disk.h.
 *
 * WHY: Blandford-Znajek power, Lorentz factor, Doppler beaming, and MAD disk
 *      thermodynamics have analytically verifiable limits that must be checked
 *      before trusting synthetic jet observables.
 *
 * Tests (20):
 *   Jet kinematics (1-6):
 *   1.  lorentzToBeta(1)   = 0          (rest limit).
 *   2.  lorentzToBeta(2)   = sqrt(3)/2  (exact SR result).
 *   3.  lorentzToBeta(1e6) -> 1         (ultra-relativistic limit).
 *   4.  jetDopplerFactor(gamma, pi/2) = 1/gamma (transverse Doppler).
 *   5.  jetDopplerFactor(gamma, 0)    > gamma   (head-on blueshift).
 *   6.  jetDopplerFactor(gamma, pi)   < 1/gamma (receding redshift).
 *   BZ mechanism (7-10):
 *   7.  horizonAngularVelocity(M, a=0) = 0  (no frame dragging in Schwarzschild).
 *   8.  horizonAngularVelocity increases monotonically with spin.
 *   9.  blandfordZnajekPower = 0 for Schwarzschild (no BZ without spin).
 *  10.  blandfordZnajekPower > 0 for spinning M87 jet.
 *   Jet geometry (11-12):
 *  11.  jetLorentzFactorAtRadius -> terminal Gamma at large r.
 *  12.  isInsideJet: false below baseDistance, true on axis above baseDistance.
 *   MAD disk (13-20):
 *  13.  madJetPower(SANE) = 0.01 * Mdot * c^2  (weak SANE jets).
 *  14.  madJetPower(MAD)  > madJetPower(SANE).
 *  15.  madJetLorentzFactor(SANE) = 2.0.
 *  16.  madJetLorentzFactor(Sgr A* MAD) in (5, 20).
 *  17.  isFluxEruptionActive(SANE) = false.
 *  18.  isFluxEruptionActive(MAD) = true at mid-cycle phase.
 *  19.  madFluxVariability(SANE) = 1.0 (no variability).
 *  20.  madDiskTemperature(r, MAD) >= diskTemperature(r, disk) (heating).
 */

#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>

#include "../src/physics/constants.h"
#include "../src/physics/jet_physics.h"
#include "../src/physics/kerr.h"
#include "../src/physics/mad_disk.h"
#include "../src/physics/thin_disk.h"

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
// Tests 1-3: lorentzToBeta
// ============================================================================

bool testLorentzToBetaRest() {
    std::cout << "Test 1: lorentzToBeta(1) = 0  (rest limit)\n";

    const double beta = lorentzToBeta(1.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "beta(gamma=1) = %.2f, expected 0", beta); // NOLINT(cert-err33-c)
    check(beta == 0.0, "lorentzToBeta(1) = 0 (rest limit)", buf);
    return true;
}

bool testLorentzToBetaExact() {
    std::cout << "Test 2: lorentzToBeta(2) = sqrt(3)/2  (exact SR)\n";

    const double beta     = lorentzToBeta(2.0);
    const double expected = std::numbers::sqrt3 / 2.0;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "beta = %.15f, expected %.15f", beta, expected); // NOLINT(cert-err33-c)
    check(std::abs(beta - expected) < 1.0e-14, "lorentzToBeta(2) = sqrt(3)/2", buf);
    return true;
}

bool testLorentzToBetaUltraRel() {
    std::cout << "Test 3: lorentzToBeta(1e6) -> 1  (ultra-relativistic)\n";

    const double beta = lorentzToBeta(1.0e6);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "beta(gamma=1e6) = %.15f (expected > 1 - 1e-12)", beta); // NOLINT(cert-err33-c)
    check(beta > 1.0 - 1.0e-12, "lorentzToBeta(1e6) -> 1", buf);
    return true;
}

// ============================================================================
// Tests 4-6: jetDopplerFactor
// ============================================================================

bool testDopplerTransverse() {
    std::cout << "Test 4: jetDopplerFactor(gamma, pi/2) = 1/gamma  (transverse Doppler)\n";

    // At theta = pi/2, cos(theta) = 0, so delta = 1 / (gamma * 1) = 1/gamma.
    // Use loose tolerance because cos(pi/2) is not exactly 0 in IEEE 754.
    const double gamma    = 10.0;
    const double delta    = jetDopplerFactor(gamma, std::numbers::pi / 2.0);
    const double expected = 1.0 / gamma;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "delta = %.10f, 1/gamma = %.10f", delta, expected); // NOLINT(cert-err33-c)
    check(std::abs(delta - expected) < 1.0e-12, "jetDopplerFactor(10, pi/2) = 1/gamma", buf);
    return true;
}

bool testDopplerHeadOn() {
    std::cout << "Test 5: jetDopplerFactor(gamma, 0) > gamma  (head-on blueshift)\n";

    // At theta = 0 (head-on), delta = 1/(gamma*(1-beta)) >> gamma for large gamma.
    const double gamma = 10.0;
    const double delta = jetDopplerFactor(gamma, 0.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "delta(head-on) = %.4f, gamma = %.1f", delta, gamma); // NOLINT(cert-err33-c)
    check(delta > gamma, "jetDopplerFactor(10, 0) > gamma (head-on blueshift)", buf);
    return true;
}

bool testDopplerReceding() {
    std::cout << "Test 6: jetDopplerFactor(gamma, pi) < 1/gamma  (receding redshift)\n";

    // At theta = pi (counter-jet), delta = 1/(gamma*(1+beta)) << 1/gamma.
    const double gamma      = 10.0;
    const double delta      = jetDopplerFactor(gamma, std::numbers::pi);
    const double transverse = 1.0 / gamma;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "delta(receding) = %.5f, 1/gamma = %.3f", delta, transverse); // NOLINT(cert-err33-c)
    check(delta < transverse, "jetDopplerFactor(10, pi) < 1/gamma (receding)", buf);
    return true;
}

// ============================================================================
// Tests 7-8: horizonAngularVelocity
// ============================================================================

bool testHorizonOmegaSchwarzschild() {
    std::cout << "Test 7: horizonAngularVelocity(M, a=0) = 0  (no frame dragging)\n";

    const double mass    = 6.5e9 * M_SUN;
    const double omegaH  = horizonAngularVelocity(mass, 0.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "Omega_H(a=0) = %.4e rad/s (expected 0)", omegaH); // NOLINT(cert-err33-c)
    check(omegaH == 0.0, "Omega_H = 0 for Schwarzschild (a=0)", buf);
    return true;
}

bool testHorizonOmegaMonotone() {
    std::cout << "Test 8: horizonAngularVelocity increases with spin\n";

    const double mass       = 6.5e9 * M_SUN;
    const double mGeo       = G * mass / C2;
    const double omegaLow   = horizonAngularVelocity(mass, 0.5 * mGeo);
    const double omegaHigh  = horizonAngularVelocity(mass, 0.9 * mGeo);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "Omega_H(a*=0.5) = %.4e, Omega_H(a*=0.9) = %.4e rad/s",
                        omegaLow, omegaHigh);
    check(omegaHigh > omegaLow, "Omega_H increases monotonically with spin", buf);
    return true;
}

// ============================================================================
// Tests 9-10: blandfordZnajekPower
// ============================================================================

bool testBZPowerSchwarzschild() {
    std::cout << "Test 9: blandfordZnajekPower = 0 for Schwarzschild (a=0)\n";

    // Override M87 spin to zero: no spin -> Omega_H = 0 -> P_BZ = 0 exactly.
    JetParams jet = m87Jet();
    jet.a         = 0.0;
    const double pBz = blandfordZnajekPower(jet);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "P_BZ(a=0) = %.4e erg/s (expected 0)", pBz); // NOLINT(cert-err33-c)
    check(pBz == 0.0, "BZ power = 0 for non-spinning BH", buf);
    return true;
}

bool testBZPowerSpinning() {
    std::cout << "Test 10: blandfordZnajekPower > 0 for spinning M87 (a*=0.9)\n";

    const JetParams jet = m87Jet();
    const double    pBz = blandfordZnajekPower(jet);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "P_BZ(M87, a*=0.9) = %.4e erg/s (expected > 0)", pBz); // NOLINT(cert-err33-c)
    check(pBz > 0.0, "BZ power > 0 for spinning M87", buf);
    return true;
}

// ============================================================================
// Tests 11-12: Jet geometry
// ============================================================================

bool testLorentzFactorTerminal() {
    std::cout << "Test 11: jetLorentzFactorAtRadius -> terminal Gamma at large r\n";

    const JetParams jet  = m87Jet();
    const double rPlus   = kerrOuterHorizon(jet.mass, jet.a);
    const double rAccel  = 10.0 * rPlus;
    // At 1e5 acceleration lengths, tanh(1e5) = 1 to double precision.
    const double rFar    = jet.baseDistance + (1.0e5 * rAccel);
    const double gamma   = jetLorentzFactorAtRadius(rFar, jet);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "gamma(r_far) = %.8f, gamma_inf = %.1f", gamma, jet.lorentzFactor);
    check(std::abs(gamma - jet.lorentzFactor) < 1.0e-3,
          "jet Lorentz factor converges to terminal value at large r", buf);
    return true;
}

bool testIsInsideJet() {
    std::cout << "Test 12: isInsideJet false below baseDistance, true on axis above\n";

    const JetParams jet    = m87Jet();
    const double rBelow    = 0.5 * jet.baseDistance;
    const double rAbove    = 1.5 * jet.baseDistance;

    const bool outsideBase = !isInsideJet(rBelow, 0.0, jet);
    const bool insideAxis  =  isInsideJet(rAbove, 0.0, jet);

    check(outsideBase, "isInsideJet = false below jet base");
    check(insideAxis,  "isInsideJet = true on axis above jet base");
    return true;
}

// ============================================================================
// Tests 13-14: madJetPower
// ============================================================================

bool testMadJetPowerSane() {
    std::cout << "Test 13: madJetPower(SANE) = 0.01 * Mdot * c^2\n";

    MADDiskParams disk  = sgrAStarMadDisk();
    disk.state          = AccretionState::SANE;
    const double expected = 0.01 * disk.mDot * C2;
    const double actual   = madJetPower(disk);
    // Both expressions are identical floating-point ops on the same mDot value.
    const double relErr   = std::abs(actual - expected) / expected;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "P_jet = %.4e, 0.01*Mdot*c^2 = %.4e, relErr = %.2e",
                        actual, expected, relErr);
    check(relErr < 1.0e-14, "madJetPower(SANE) = 0.01*Mdot*c^2 exactly", buf);
    return true;
}

bool testMadJetPowerMadGtSane() {
    std::cout << "Test 14: madJetPower(MAD) > madJetPower(SANE)\n";

    const MADDiskParams diskMad  = sgrAStarMadDisk();  // state = MAD
    MADDiskParams diskSane = sgrAStarMadDisk();
    diskSane.state         = AccretionState::SANE;
    const double pMad      = madJetPower(diskMad);
    const double pSane     = madJetPower(diskSane);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "P_MAD = %.4e, P_SANE = %.4e erg/s", pMad, pSane);
    check(pMad > pSane, "MAD jet power exceeds SANE jet power", buf);
    return true;
}

// ============================================================================
// Tests 15-16: madJetLorentzFactor
// ============================================================================

bool testMadLorentzFactorSane() {
    std::cout << "Test 15: madJetLorentzFactor(SANE) = 2.0\n";

    MADDiskParams disk = sgrAStarMadDisk();
    disk.state         = AccretionState::SANE;
    const double gamma = madJetLorentzFactor(disk);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "Gamma(SANE) = %.4f (expected 2.0)", gamma); // NOLINT(cert-err33-c)
    check(gamma == 2.0, "madJetLorentzFactor(SANE) = 2.0", buf);
    return true;
}

bool testMadLorentzFactorMad() {
    std::cout << "Test 16: madJetLorentzFactor(Sgr A* MAD) in (5, 20)\n";

    const MADDiskParams disk = sgrAStarMadDisk();  // a* = 0.94, MAD
    const double        gamma = madJetLorentzFactor(disk);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "Gamma(MAD, a*=0.94) = %.4f (expected in (5, 20))", gamma);
    check(gamma > 5.0 && gamma < 20.0,
          "madJetLorentzFactor(Sgr A*, MAD) in (5, 20)", buf);
    return true;
}

// ============================================================================
// Tests 17-18: isFluxEruptionActive
// ============================================================================

bool testEruptionSane() {
    std::cout << "Test 17: isFluxEruptionActive(SANE) = false\n";

    MADDiskParams disk = sgrAStarMadDisk();
    disk.state         = AccretionState::SANE;
    // Set time to mid-cycle to confirm SANE never erupts regardless of phase.
    disk.time          = 0.5 * disk.fluxEruptionPeriod * 3600.0;
    check(!isFluxEruptionActive(disk), "SANE state never triggers eruption");
    return true;
}

bool testEruptionMadMidCycle() {
    std::cout << "Test 18: isFluxEruptionActive(MAD) = true at mid-cycle (phase=0.5)\n";

    MADDiskParams disk = sgrAStarMadDisk();  // state = MAD
    // phase = fmod(t, T) / T = 0.5 -> active when 0.4 < 0.5 < 0.6.
    disk.time = 0.5 * disk.fluxEruptionPeriod * 3600.0;
    char buf[128];
    const double period = disk.fluxEruptionPeriod * 3600.0;
    const double phase  = std::fmod(disk.time, period) / period;
    (void)std::snprintf(buf, sizeof(buf), "phase = %.4f (expected in [0.4, 0.6])", phase); // NOLINT(cert-err33-c)
    check(isFluxEruptionActive(disk), "eruption active at mid-cycle phase", buf);
    return true;
}

// ============================================================================
// Tests 19-20: Variability and temperature
// ============================================================================

bool testVariabilitySane() {
    std::cout << "Test 19: madFluxVariability(SANE) = 1.0  (steady)\n";

    MADDiskParams disk = sgrAStarMadDisk();
    disk.state         = AccretionState::SANE;
    const double v     = madFluxVariability(disk);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "variability(SANE) = %.4f (expected 1.0)", v); // NOLINT(cert-err33-c)
    check(v == 1.0, "madFluxVariability(SANE) = 1.0 (steady accretion)", buf);
    return true;
}

bool testMadTemperatureHeating() {
    std::cout << "Test 20: madDiskTemperature(r, MAD) >= diskTemperature(r, disk)\n";

    // MAD magnetic reconnection heating near ISCO multiplies base temp by
    // (1 + 0.2*(rIn/r)^2) >= 1, so MAD temperature >= Novikov-Thorne base.
    const MADDiskParams disk = sgrAStarMadDisk();   // state = MAD
    const double  r    = 5.0 * disk.rIn;     // inside disk: rIn < r < rOut
    const double  tMad  = madDiskTemperature(r, disk);
    const double  tBase = diskTemperature(r, disk);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), // NOLINT(cert-err33-c)
                        "T_MAD = %.4e K, T_base = %.4e K", tMad, tBase);
    check(tMad >= tBase, "MAD magnetic heating raises disk temperature", buf);
    return true;
}

} // namespace

// NOLINTNEXTLINE(bugprone-exception-escape) -- test binary; exceptions propagate to crash
int main() {
    std::cout << "\n================================================\n"
              << "JET PHYSICS AND MAD DISK VALIDATION\n"
              << "Physics: BZ (1977), Tchekhovskoy+ (2011), EHT (2026)\n"
              << "================================================\n\n";

    testLorentzToBetaRest();          std::cout << "\n";
    testLorentzToBetaExact();         std::cout << "\n";
    testLorentzToBetaUltraRel();      std::cout << "\n";
    testDopplerTransverse();          std::cout << "\n";
    testDopplerHeadOn();              std::cout << "\n";
    testDopplerReceding();            std::cout << "\n";
    testHorizonOmegaSchwarzschild();  std::cout << "\n";
    testHorizonOmegaMonotone();       std::cout << "\n";
    testBZPowerSchwarzschild();       std::cout << "\n";
    testBZPowerSpinning();            std::cout << "\n";
    testLorentzFactorTerminal();      std::cout << "\n";
    testIsInsideJet();                std::cout << "\n";
    testMadJetPowerSane();            std::cout << "\n";
    testMadJetPowerMadGtSane();       std::cout << "\n";
    testMadLorentzFactorSane();       std::cout << "\n";
    testMadLorentzFactorMad();        std::cout << "\n";
    testEruptionSane();               std::cout << "\n";
    testEruptionMadMidCycle();            std::cout << "\n";
    testVariabilitySane();            std::cout << "\n";
    testMadTemperatureHeating();      std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
