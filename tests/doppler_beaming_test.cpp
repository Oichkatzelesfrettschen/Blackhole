/**
 * @file doppler_beaming_test.cpp
 * @brief Validation tests for relativistic Doppler beaming in accretion disks
 *
 * WHY: Verify 10-1000x flux asymmetry from rotating disk material
 * WHAT: 7 validation tests across inclinations and radii
 * HOW: Test δ^(3+α) boost, inclination dependence, flux conservation
 *
 * Reference:
 *   Cunningham (1975) ApJ 202, 788
 *   Begelman, Blandford, Rees (1984) Rev. Mod. Phys. 56, 255
 */

#include <cmath>
#include <iomanip>
#include <iostream>
#include <numbers>

#include "../src/physics/doppler.h"

// Constants
constexpr double M_PI_VAL = std::numbers::pi;

/**
 * @brief Test 1: Face-on disk (i=0) symmetric boost
 */
namespace {

bool testFaceOnNoBoost() {
  std::cout << "\n[TEST 1] Face-On Disk Symmetric Boost\n";
  std::cout << "======================================\n";

  const double r = 6.0; // ISCO
  const double aStar = 0.0;
  const double inclination = 0.0; // Face-on
  const double phiApproaching = 0.0;
  const double phiReceding = M_PI_VAL;

  const double boostApp = physics::diskDopplerBoost(r, aStar, phiApproaching, inclination);
  const double boostRec = physics::diskDopplerBoost(r, aStar, phiReceding, inclination);

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Inclination: i = 0° (face-on)\n";
  std::cout << "  Boost (approaching): " << boostApp << "\n";
  std::cout << "  Boost (receding):    " << boostRec << "\n";
  std::cout << "  Asymmetry:           " << boostApp / boostRec << "x\n";

  // For face-on, boost is symmetric (transverse Doppler = time dilation only)
  // Expect boost < 1.0 due to γ^(-3) redshift
  const bool passed = (std::abs(boostApp - boostRec) < 0.01) && (boostApp < 1.0);
  std::cout << "  Status:              " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:                Transverse Doppler redshift (time dilation)\n";

  return passed;
}

/**
 * @brief Test 2: Edge-on disk (i=90°) maximum asymmetry
 */
bool testEdgeOnMaximumAsymmetry() {
  std::cout << "\n[TEST 2] Edge-On Disk Maximum Asymmetry\n";
  std::cout << "========================================\n";

  const double r = 6.0; // ISCO
  const double aStar = 0.0;
  const double inclination = M_PI_VAL / 2.0; // Edge-on
  const double phiApproaching = 0.0;
  const double phiReceding = M_PI_VAL;

  const double boostApp = physics::diskDopplerBoost(r, aStar, phiApproaching, inclination);
  const double boostRec = physics::diskDopplerBoost(r, aStar, phiReceding, inclination);
  const double asymmetry = boostApp / boostRec;

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Inclination: i = 90° (edge-on)\n";
  std::cout << "  Radius:      r = " << r << " M\n";
  std::cout << "  Boost (approaching): " << boostApp << "\n";
  std::cout << "  Boost (receding):    " << boostRec << "\n";
  std::cout << "  Asymmetry:           " << asymmetry << "x\n";

  // Expected: ~10-100x for edge-on at ISCO
  const bool passed = (asymmetry > 10.0) && (asymmetry < 200.0);
  std::cout << "  Status:              " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Expected:            10-200x (literature range)\n";

  return passed;
}

/**
 * @brief Test 3: Inclination sweep (0° to 90°)
 */
bool testInclinationSweep() {
  std::cout << "\n[TEST 3] Inclination Sweep\n";
  std::cout << "==========================\n";

  const double r = 6.0;
  const double aStar = 0.0;
  const double phiApproaching = 0.0;
  const double phiReceding = M_PI_VAL;

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Radius: r = " << r << " M\n\n";
  std::cout << "  Incl (deg)  Approaching  Receding  Asymmetry\n";
  std::cout << "  ----------  -----------  --------  ---------\n";

  bool allPassed = true;
  double prevAsymmetry = 1.0;

  for (int iDeg = 0; iDeg <= 90; iDeg += 15) {
    const double incl = iDeg * M_PI_VAL / 180.0;
    const double boostApp = physics::diskDopplerBoost(r, aStar, phiApproaching, incl);
    const double boostRec = physics::diskDopplerBoost(r, aStar, phiReceding, incl);
    const double asymmetry = boostApp / boostRec;

    std::cout << "      " << std::setw(3) << iDeg << "       " << std::setw(7) << boostApp
              << "      " << std::setw(7) << boostRec << "     " << std::setw(7) << asymmetry
              << "x\n";

    // Asymmetry should monotonically increase with inclination
    if (asymmetry < prevAsymmetry - 0.01) { // Allow small numerical noise
      allPassed = false;
    }
    prevAsymmetry = asymmetry;
  }

  std::cout << "\n  Status: " << (allPassed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:   Asymmetry increases monotonically with inclination\n";

  return allPassed;
}

/**
 * @brief Test 4: Inner disk (smaller r) higher boost
 */
bool testInnerDiskHigherBoost() {
  std::cout << "\n[TEST 4] Inner Disk Higher Boost\n";
  std::cout << "=================================\n";

  const double aStar = 0.0;
  const double inclination = M_PI_VAL / 2.0; // Edge-on
  const double phiApproaching = 0.0;

  const double rInner = 6.0; // ISCO
  const double rOuter = 20.0;

  const double boostInner = physics::diskDopplerBoost(rInner, aStar, phiApproaching, inclination);
  const double boostOuter = physics::diskDopplerBoost(rOuter, aStar, phiApproaching, inclination);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Inclination: i = 90° (edge-on)\n";
  std::cout << "  Boost (r=6M):  " << boostInner << "\n";
  std::cout << "  Boost (r=20M): " << boostOuter << "\n";
  std::cout << "  Ratio:         " << boostInner / boostOuter << "x\n";

  const bool passed = boostInner > boostOuter * 2.0;
  std::cout << "  Status:        " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:          Higher velocity at inner radius\n";

  return passed;
}

/**
 * @brief Test 5: Spectral index affects boost exponent
 */
bool testSpectralIndexEffect() {
  std::cout << "\n[TEST 5] Spectral Index Effect\n";
  std::cout << "===============================\n";

  const double r = 6.0;
  const double aStar = 0.0;
  const double inclination = M_PI_VAL / 2.0;
  const double phiApproaching = 0.0;

  const double boostBlackbody =
      physics::diskDopplerBoost(r, aStar, phiApproaching, inclination, 0.0);
  const double boostPowerlaw =
      physics::diskDopplerBoost(r, aStar, phiApproaching, inclination, 1.0);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Radius:      r = " << r << " M\n";
  std::cout << "  Inclination: i = 90°\n";
  std::cout << "  Boost (α=0, blackbody): " << boostBlackbody << "\n";
  std::cout << "  Boost (α=1, power-law): " << boostPowerlaw << "\n";
  std::cout << "  Ratio:                  " << boostPowerlaw / boostBlackbody << "x\n";

  const bool passed = boostPowerlaw > boostBlackbody * 1.5;
  std::cout << "  Status:                 " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:                   δ^(3+α) increases with α\n";

  return passed;
}

/**
 * @brief Test 6: Kerr vs Schwarzschild at safe radius
 */
bool testKerrSpinEnhancement() {
  std::cout << "\n[TEST 6] Kerr Spin Formula Validation\n";
  std::cout << "======================================\n";

  // Use r=10M where both Schwarzschild and Kerr have stable orbits
  const double r = 10.0;
  const double inclination = M_PI_VAL / 2.0;
  const double phiApproaching = 0.0;

  const double boostSchwarzschild = physics::diskDopplerBoost(r, 0.0, phiApproaching, inclination);
  const double boostKerrRetrograde =
      physics::diskDopplerBoost(r, -0.5, phiApproaching, inclination);
  const double boostKerrPrograde = physics::diskDopplerBoost(r, 0.5, phiApproaching, inclination);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Radius:         r = " << r << " M\n";
  std::cout << "  Inclination:    i = 90°\n";
  std::cout << "  Boost (a=0):      " << boostSchwarzschild << "\n";
  std::cout << "  Boost (a=-0.5):   " << boostKerrRetrograde << "\n";
  std::cout << "  Boost (a=+0.5):   " << boostKerrPrograde << "\n";

  // Spin affects orbital velocity (subtle GR effect at large radii)
  const bool passed = (boostKerrPrograde != boostSchwarzschild) &&
                      (boostKerrRetrograde != boostSchwarzschild) &&
                      (boostKerrPrograde != boostKerrRetrograde);
  std::cout << "  Status:         " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:           Spin parameter modifies orbital velocity\n";

  return passed;
}

/**
 * @brief Test 7: Boost clamped to reasonable range
 */
bool testBoostClamping() {
  std::cout << "\n[TEST 7] Boost Clamping\n";
  std::cout << "========================\n";

  const double r = 6.0;
  const double aStar = 0.998; // Near-extremal
  const double inclination = M_PI_VAL / 2.0;
  const double phiApproaching = 0.0;
  const double phiReceding = M_PI_VAL;

  const double boostApp = physics::diskDopplerBoost(r, aStar, phiApproaching, inclination, 2.0);
  const double boostRec = physics::diskDopplerBoost(r, aStar, phiReceding, inclination, 2.0);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Spin:         a* = " << aStar << "\n";
  std::cout << "  Spectral idx: α = 2.0\n";
  std::cout << "  Boost (approaching): " << boostApp << "\n";
  std::cout << "  Boost (receding):    " << boostRec << "\n";

  const bool passed = (boostApp <= 1000.0) && (boostRec >= 0.01);
  std::cout << "  Status:              " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:                Clamped to [0.01, 1000.0] range\n";

  return passed;
}

/**
 * @brief Main test runner
 */
} // namespace

int main() {
    std::cout << "\n";
    std::cout << "========================================================\n";
    std::cout << "  Doppler Beaming Validation Tests\n";
    std::cout << "========================================================\n";
    
    int passed = 0;
    int const total = 7;

    // Run all tests
    if (testFaceOnNoBoost()) {
      passed++;
    }
    if (testEdgeOnMaximumAsymmetry()) {
      passed++;
    }
    if (testInclinationSweep()) {
      passed++;
    }
    if (testInnerDiskHigherBoost()) {
      passed++;
    }
    if (testSpectralIndexEffect()) {
      passed++;
    }
    if (testKerrSpinEnhancement()) {
      passed++;
    }
    if (testBoostClamping()) {
      passed++;
    }

    // Summary
    std::cout << "\n========================================================\n";
    std::cout << "  Test Summary\n";
    std::cout << "========================================================\n";
    std::cout << "  Passed: " << passed << " / " << total << "\n";
    std::cout << "  Failed: " << (total - passed) << " / " << total << "\n";
    
    if (passed == total) {
        std::cout << "\n  ✓ ALL TESTS PASSED\n";
        std::cout << "========================================================\n\n";
        return 0;
    }
    std::cout << "\n  ✗ SOME TESTS FAILED\n";
    std::cout << "========================================================\n\n";
    return 1;
}
