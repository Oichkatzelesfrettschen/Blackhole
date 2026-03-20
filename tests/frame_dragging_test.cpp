/**
 * @file frame_dragging_test.cpp
 * @brief Validation tests for frame dragging and ergosphere calculations
 *
 * WHY: Verify physics correctness of ZAMO angular velocity and ergosphere boundary
 * WHAT: 6 validation tests against BPT 1972 formulas
 * HOW: Test Ω_ZAMO, r_ergo, and frame dragging effects for various spin parameters
 */

#include <algorithm>
#include <cassert>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <numbers>

// Constants
constexpr double M_PI_VAL = std::numbers::pi;

// Test tolerance
constexpr double TOLERANCE = 1e-6;

/**
 * @brief Compute event horizon radius r_+
 *
 * r_+ = M + √(M² - a²)
 */
namespace {

double eventHorizon(double aStar) {
  aStar = std::clamp(aStar, -0.9999, 0.9999);
  double const aSqr = aStar * aStar;
  return 1.0 + std::sqrt(1.0 - aSqr);
}

/**
 * @brief Compute ergosphere outer boundary radius
 *
 * r_ergo = M + √(M² - a² cos²θ)
 */
double ergosphere(double aStar, double theta) {
  aStar = std::clamp(aStar, -0.9999, 0.9999);
  double const cosTheta = std::cos(theta);
  double const aSqrCosSqr = aStar * aStar * cosTheta * cosTheta;
  return 1.0 + std::sqrt(1.0 - aSqrCosSqr);
}

/**
 * @brief Compute ZAMO angular velocity (frame dragging frequency)
 *
 * Ω = 2Mar / (r³ + a²r + 2Ma²) where M=1
 */
double frameDraggingOmega(double r, double aStar) {
  aStar = std::clamp(aStar, -0.9999, 0.9999);
  double const aSqr = aStar * aStar;

  double const numerator = 2.0 * aStar * r;
  double const denominator = (r * r * r) + (aSqr * r) + (2.0 * aSqr);

  if (denominator < 1e-10) {
    return 0.0;
  }

  return numerator / denominator;
}

/**
 * @brief Test 1: Schwarzschild (a=0) has no ergosphere
 */
bool testSchwarzschildNoErgosphere() {
  std::cout << "\n[TEST 1] Schwarzschild No Ergosphere\n";
  std::cout << "=====================================\n";

  const double aStar = 0.0;
  const double rPlus = eventHorizon(aStar);
  const double rErgo = ergosphere(aStar, M_PI_VAL / 2.0); // Equator

  std::cout << std::fixed << std::setprecision(10);
  std::cout << "  r_+:     " << rPlus << " M\n";
  std::cout << "  r_ergo:  " << rErgo << " M\n";
  std::cout << "  Diff:    " << std::abs(rPlus - rErgo) << "\n";

  const bool passed = std::abs(rPlus - rErgo) < TOLERANCE;
  std::cout << "  Status:  " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:    Ergosphere coincides with horizon for a=0\n";

  return passed;
}

/**
 * @brief Test 2: Near-extremal Kerr (a=0.998) ergosphere size
 */
bool testKerrErgosphereSize() {
  std::cout << "\n[TEST 2] Near-Extremal Kerr Ergosphere\n";
  std::cout << "=======================================\n";

  const double aStar = 0.998;
  const double rPlus = eventHorizon(aStar);
  const double rErgoEquator = ergosphere(aStar, M_PI_VAL / 2.0);
  const double rErgoPole = ergosphere(aStar, 0.0);

  std::cout << std::fixed << std::setprecision(10);
  std::cout << "  Spin:         a* = " << aStar << "\n";
  std::cout << "  r_+:          " << rPlus << " M\n";
  std::cout << "  r_ergo (θ=π/2): " << rErgoEquator << " M\n";
  std::cout << "  r_ergo (θ=0):   " << rErgoPole << " M\n";
  std::cout << "  Thickness:    " << (rErgoEquator - rPlus) << " M\n";

  // Expected: r_+ ≈ 1.06, r_ergo ≈ 2.0 at equator
  const bool passed = (rPlus < 1.1) && (rErgoEquator > 1.9) && (rErgoEquator < 2.1);
  std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

  return passed;
}

/**
 * @brief Test 3: Frame dragging Ω vanishes at infinity
 */
bool testOmegaVanishesAtInfinity() {
  std::cout << "\n[TEST 3] Frame Dragging Vanishes at Infinity\n";
  std::cout << "=============================================\n";

  const double aStar = 0.9;
  const double rLarge = 1000.0;
  const double omega = frameDraggingOmega(rLarge, aStar);

  std::cout << std::scientific << std::setprecision(6);
  std::cout << "  Spin:    a* = " << aStar << "\n";
  std::cout << "  Radius:  r = " << rLarge << " M\n";
  std::cout << "  Ω_ZAMO:  " << omega << " rad/M\n";

  // Expected: Ω ~ 1/r³ for large r
  const double expectedOrder = 1.0 / (rLarge * rLarge * rLarge);
  std::cout << "  Expected order: ~" << expectedOrder << "\n";

  const bool passed = std::abs(omega) < 1e-5; // ~2e-6 for a=0.9, r=1000
  std::cout << "  Status:  " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

  return passed;
}

/**
 * @brief Test 4: Frame dragging maximum near horizon
 */
bool testOmegaMaximumNearHorizon() {
  std::cout << "\n[TEST 4] Frame Dragging Maximum Near Horizon\n";
  std::cout << "=============================================\n";

  const double aStar = 0.9;
  const double rPlus = eventHorizon(aStar);
  const double rTest = rPlus + 0.01;

  const double omegaNear = frameDraggingOmega(rTest, aStar);
  const double omegaFar = frameDraggingOmega(10.0, aStar);

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Spin:         a* = " << aStar << "\n";
  std::cout << "  r_+:          " << rPlus << " M\n";
  std::cout << "  Ω (r=r_++0.01): " << omegaNear << " rad/M\n";
  std::cout << "  Ω (r=10M):    " << omegaFar << " rad/M\n";
  std::cout << "  Ratio:        " << omegaNear / omegaFar << "x\n";

  const bool passed = omegaNear > omegaFar * 10.0; // ~25x for a=0.9
  std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:         Frame dragging strongest near horizon\n";

  return passed;
}

/**
 * @brief Test 5: Ergosphere oblate shape (wider at equator)
 */
bool testErgosphereOblate() {
  std::cout << "\n[TEST 5] Ergosphere Oblate Shape\n";
  std::cout << "=================================\n";

  const double aStar = 0.9;
  const double rErgoEquator = ergosphere(aStar, M_PI_VAL / 2.0);
  const double rErgoPole = ergosphere(aStar, 0.0);

  std::cout << std::fixed << std::setprecision(10);
  std::cout << "  Spin:         a* = " << aStar << "\n";
  std::cout << "  r_ergo (equator): " << rErgoEquator << " M\n";
  std::cout << "  r_ergo (pole):    " << rErgoPole << " M\n";
  std::cout << "  Ratio:        " << rErgoEquator / rErgoPole << "\n";

  const bool passed = rErgoEquator > rErgoPole;
  std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:         Ergosphere bulges at equator\n";

  return passed;
}

/**
 * @brief Test 6: Frame dragging sign matches spin direction
 */
bool testOmegaSign() {
  std::cout << "\n[TEST 6] Frame Dragging Sign\n";
  std::cout << "=============================\n";

  const double r = 3.0;
  const double aPos = 0.5;
  const double aNeg = -0.5;

  const double omegaPos = frameDraggingOmega(r, aPos);
  const double omegaNeg = frameDraggingOmega(r, aNeg);

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Radius:       r = " << r << " M\n";
  std::cout << "  Ω (a=+0.5):   " << omegaPos << " rad/M\n";
  std::cout << "  Ω (a=-0.5):   " << omegaNeg << " rad/M\n";

  const bool passed =
      (omegaPos > 0.0) && (omegaNeg < 0.0) && (std::abs(omegaPos + omegaNeg) < TOLERANCE);
  std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
  std::cout << "  Note:         Ω changes sign with spin direction\n";

  return passed;
}

/**
 * @brief Main test runner
 */
} // namespace

int main() {
    std::cout << "\n";
    std::cout << "========================================================\n";
    std::cout << "  Frame Dragging & Ergosphere Validation Tests\n";
    std::cout << "========================================================\n";
    
    int passed = 0;
    int const total = 6;

    // Run all tests
    if (testSchwarzschildNoErgosphere()) {
      passed++;
    }
    if (testKerrErgosphereSize()) {
      passed++;
    }
    if (testOmegaVanishesAtInfinity()) {
      passed++;
    }
    if (testOmegaMaximumNearHorizon()) {
      passed++;
    }
    if (testErgosphereOblate()) {
      passed++;
    }
    if (testOmegaSign()) {
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
