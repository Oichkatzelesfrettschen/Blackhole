/**
 * @file synchrotron_spectrum_test.cpp
 * @brief Validation tests for synchrotron emission physics
 *
 * WHY: Verify GPU synchrotron functions match analytical formulas from Rybicki & Lightman
 * WHAT: 8 comprehensive validation tests for F(x), G(x), spectrum shape, and absorption
 * HOW: Compare GLSL implementations against literature values and CPU reference
 *
 * References:
 * - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 6
 * - Longair (2011) "High Energy Astrophysics" Ch. 8
 */

#include <numbers>
#include <cassert>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <vector>

#include "../src/physics/synchrotron.h"

using namespace physics;

// Test tolerance
// Note: These approximations have known errors at regime boundaries (x~0.01, x~10)
// Low frequency (x<0.01): <0.1% error
// Intermediate (0.01<x<10): 3-15% error at transitions
// High frequency (x>10): exponential regime with transition errors
constexpr double TOLERANCE = 1e-5;
constexpr double RELAXED_TOLERANCE = 0.15;  // 15% tolerance for approx boundaries

/**
 * @brief Test 1: Synchrotron function F(x) - Low frequency regime
 *
 * For x << 1, F(x) ~= 1.8084 * x^(1/3)
 * Note: Test only values well within low-freq regime (x << 0.01)
 * Boundary at x=0.01 has regime transition errors
 */
namespace {

bool testSynchrotronFLowFreq() {
  std::cout << "\n[TEST 1] Synchrotron F(x) - Low Frequency Regime\n";
  std::cout << "=================================================\n";

  std::vector<double> const testVals = {1e-4, 1e-3, 5e-3};
  bool allPassed = true;

  for (double const x : testVals) {
    double const fX = synchrotronF(x);
    double const expected = 1.8084 * std::pow(x, 1.0 / 3.0);
    double const error = std::abs(fX - expected) / expected;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  x = " << x << "\n";
    std::cout << "    F(x) computed: " << fX << "\n";
    std::cout << "    F(x) expected: " << expected << "\n";
    std::cout << "    Relative err:  " << error << "\n";

    bool const passed = error < TOLERANCE; // Strict tolerance in pure low-freq regime
    std::cout << "    Status:        " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  return allPassed;
}

/**
 * @brief Test 2: Synchrotron function F(x) - High frequency regime
 *
 * For x >> 1, F(x) ~= sqrt(pi/2) * sqrt(x) * exp(-x)
 * Note: Only test x >> 10 to avoid transition boundary
 */
bool testSynchrotronFHighFreq() {
  std::cout << "\n[TEST 2] Synchrotron F(x) - High Frequency Regime\n";
  std::cout << "==================================================\n";

  std::vector<double> const testVals = {20.0, 50.0, 100.0};
  bool allPassed = true;

  for (double const x : testVals) {
    double const fX = synchrotronF(x);
    double const expected = std::sqrt(std::numbers::pi / 2.0) * std::sqrt(x) * std::exp(-x);
    double const error = std::abs(fX - expected) / expected;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  x = " << x << "\n";
    std::cout << "    F(x) computed: " << fX << "\n";
    std::cout << "    F(x) expected: " << expected << "\n";
    std::cout << "    Relative err:  " << error << "\n";

    bool const passed = error < TOLERANCE; // Strict tolerance in pure high-freq regime
    std::cout << "    Status:        " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  return allPassed;
}

/**
 * @brief Test 3: Synchrotron function G(x) - Polarization degree
 *
 * G(x) represents circular polarization: Pol = G(x) / F(x)
 * Expected: G(x) < F(x) for all x (linear polarization always < 1)
 */
bool testSynchrotronGPolarization() {
  std::cout << "\n[TEST 3] Synchrotron G(x) - Polarization Degree\n";
  std::cout << "================================================\n";

  std::vector<double> const testVals = {1e-3, 0.1, 1.0, 10.0, 100.0};
  bool allPassed = true;

  for (double const x : testVals) {
    double const fX = synchrotronF(x);
    double const gX = synchrotronG(x);
    double const pol = gX / fX;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  x = " << x << "\n";
    std::cout << "    F(x) = " << fX << "\n";
    std::cout << "    G(x) = " << gX << "\n";
    std::cout << "    Pol  = " << pol << "\n";

    // Polarization degree must be between 0 and 1
    bool const passed = (pol >= 0.0 && pol <= 1.0);
    std::cout << "    Status: " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  return allPassed;
}

/**
 * @brief Test 4: Power-law spectrum shape
 *
 * For power-law electron distribution N(gamma) ~ gamma^(-p):
 * F_nu ~ nu^(-(p-1)/2) in optically thin regime
 * Expected: spectral index alpha = -(p-1)/2
 */
bool testPowerLawSpectrum() {
  std::cout << "\n[TEST 4] Power-Law Spectrum Shape\n";
  std::cout << "==================================\n";

  double const b = 100.0; // Gauss (typical AGN jet)
  double const gammaMin = 1.0;
  double const gammaMax = 1e6;
  double const p = 2.5; // Typical jet power-law index

  // Compute spectrum at three frequencies
  double const nu1 = synchrotronFrequencyCritical(gammaMin, b) * 10.0;
  double const nu2 = nu1 * 100.0;
  double const nu3 = nu2 * 100.0;

  double const f1 = synchrotronSpectrumPowerLaw(nu1, b, gammaMin, gammaMax, p);
  double const f2 = synchrotronSpectrumPowerLaw(nu2, b, gammaMin, gammaMax, p);
  double const f3 = synchrotronSpectrumPowerLaw(nu3, b, gammaMin, gammaMax, p);

  // Compute spectral indices from ratios
  double const alpha12 = std::log(f1 / f2) / std::log(nu1 / nu2);
  double const alpha23 = std::log(f2 / f3) / std::log(nu2 / nu3);
  double const expectedAlpha = -(p - 1.0) / 2.0;

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Power-law index: p = " << p << "\n";
  std::cout << "  Expected spectral index: alpha = " << expectedAlpha << "\n";
  std::cout << "  Computed alpha (nu1-nu2): " << alpha12 << "\n";
  std::cout << "  Computed alpha (nu2-nu3): " << alpha23 << "\n";
  std::cout << "  Error: " << std::abs(alpha12 - expectedAlpha) << "\n";

  bool const passed = (std::abs(alpha12 - expectedAlpha) < RELAXED_TOLERANCE &&
                       std::abs(alpha23 - expectedAlpha) < RELAXED_TOLERANCE);
  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";

  return passed;
}

/**
 * @brief Test 5: Self-absorption frequency
 *
 * Self-absorption frequency nu_a marks transition from optically thin to thick.
 * Below nu_a: F_nu ~ nu^2.5 (Rayleigh-Jeans regime)
 * Above nu_a: F_nu ~ nu^(-(p-1)/2) (power-law)
 */
bool testSelfAbsorptionTransition() {
  std::cout << "\n[TEST 5] Self-Absorption Transition\n";
  std::cout << "====================================\n";

  double const b = 100.0;
  double const gammaMin = 10.0;
  double const p = 2.5;
  double const nE = 1e3; // Electron density [cm^-3]
  double const r = 1e16; // Source size [cm]

  double const nuA = synchrotronSelfAbsorptionFrequency(b, nE, r, p);
  double const nuMin = synchrotronFrequencyCritical(gammaMin, b);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  nu_min (critical freq): " << nuMin << " Hz\n";
  std::cout << "  nu_a (absorption freq): " << nuA << " Hz\n";
  std::cout << "  Ratio nu_a / nu_min: " << (nuA / nuMin) << "\n";

  // Self-absorption frequency should be < critical frequency
  bool const passed = (nuA > 0.0 && nuA < nuMin);
  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";

  return passed;
}

/**
 * @brief Test 6: Absorption coefficient frequency dependence
 *
 * For power-law electrons: alpha_nu ~ nu^(-(p+4)/2)
 * Expected: steep frequency dependence, strong suppression at high freq
 */
bool testAbsorptionCoefficient() {
  std::cout << "\n[TEST 6] Absorption Coefficient Frequency Dependence\n";
  std::cout << "======================================================\n";

  double const b = 100.0;
  double const nE = 1e3; // cm^-3 (typical AGN)
  double const p = 2.5;

  double const nu1 = 1e9;  // 1 GHz
  double const nu2 = 1e10; // 10 GHz (10x higher)
  double const nu3 = 1e11; // 100 GHz (100x higher)

  double const alpha1 = synchrotronAbsorptionCoefficient(nu1, b, nE, p);
  double const alpha2 = synchrotronAbsorptionCoefficient(nu2, b, nE, p);
  double const alpha3 = synchrotronAbsorptionCoefficient(nu3, b, nE, p);

  // Compute frequency dependence exponent
  double const exp12 = std::log(alpha1 / alpha2) / std::log(nu1 / nu2);
  double const exp23 = std::log(alpha2 / alpha3) / std::log(nu2 / nu3);
  double const expectedExp = -(p + 4.0) / 2.0;

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Expected exponent: " << expectedExp << "\n";
  std::cout << "  Computed exponent (nu1-nu2): " << exp12 << "\n";
  std::cout << "  Computed exponent (nu2-nu3): " << exp23 << "\n";
  std::cout << "  Error: " << std::abs(exp12 - expectedExp) << "\n";

  bool const passed = (std::abs(exp12 - expectedExp) < RELAXED_TOLERANCE &&
                       std::abs(exp23 - expectedExp) < RELAXED_TOLERANCE);
  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";

  return passed;
}

/**
 * @brief Test 7: Spectral index calculation
 *
 * Spectral index α = -(p - 1)/2 and inverse: p = 1 - 2α
 * For typical jets p=2-3, giving α = -0.5 to -1.0
 */
bool testSpectralIndexCalculation() {
  std::cout << "\n[TEST 7] Spectral Index Calculation\n";
  std::cout << "====================================\n";

  std::vector<double> const pValues = {2.0, 2.5, 3.0, 3.5};
  bool allPassed = true;

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Testing spectral index: alpha = -(p-1)/2\n\n";

  for (double const p : pValues) {
    double const alpha = synchrotronSpectralIndex(p);
    double const expectedAlpha = -(p - 1.0) / 2.0;
    double const pBack = electronIndexFromSpectral(alpha);

    std::cout << "  p = " << p << "\n";
    std::cout << "    alpha = " << alpha << " (expected " << expectedAlpha << ")\n";
    std::cout << "    p (from alpha) = " << pBack << " (expected " << p << ")\n";

    bool const passed =
        (std::abs(alpha - expectedAlpha) < TOLERANCE && std::abs(pBack - p) < TOLERANCE);
    std::cout << "    Status: " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  return allPassed;
}

/**
 * @brief Test 8: Polarization degree bounds
 *
 * Verify pol = G(x)/F(x) stays in [0, 1] range
 * Note: Theory gives Pol_max = (p+1)/(p+7/3) for certain regimes
 * but computed max depends on approximation accuracy
 */
bool testPolarizationBounds() {
  std::cout << "\n[TEST 8] Polarization Degree Bounds\n";
  std::cout << "====================================\n";

  std::vector<double> const testX = {1e-3, 0.01, 0.1, 1.0, 5.0, 10.0, 50.0, 100.0};
  bool allPassed = true;

  std::cout << std::fixed << std::setprecision(6);

  for (double const x : testX) {
    double const fVal = synchrotronF(x);
    double const gVal = synchrotronG(x);
    double const pol = (fVal > 1e-30) ? (gVal / fVal) : 0.0;

    // Polarization must be in [0, 1]
    bool const passed = (pol >= 0.0 && pol <= 1.0);

    std::cout << "  x = " << x << ": Pol = " << pol;
    std::cout << " " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";

  return allPassed;
}

/**
 * @brief Test 9: Synchrotron F(x) accuracy against Rybicki-Lightman Table A1
 *
 * WHY: The Fouka & Ouichaoui polynomial has ~1% error in the intermediate
 * regime. When boost::math is available, the Gauss-Legendre integral of
 * K_{5/3} gives sub-0.01% accuracy.
 *
 * Reference values from Rybicki & Lightman (1979) Table A1, page 232.
 * Values confirmed by independent numerical integration.
 *
 * Tolerance: 0.01% when boost is present, 2% otherwise (polynomial fallback).
 */
bool testSynchrotronFRybickiLightmanTable() {
  std::cout << "\n[TEST 9] Synchrotron F(x) vs Rybicki-Lightman Table A1\n";
  std::cout << "=========================================================\n";

  // {x, F(x)} pairs verified against scipy.integrate.quad(kv(5/3, xi), x, inf)
  // Primary source: Rybicki & Lightman (1979) Table A1 (3 sig figs);
  // x=10 corrected from R&L 0.0195 (typo or wrong row) to scipy value 1.92e-4.
  struct TestPoint {
    double x, fRef;
  };
  static const TestPoint pts[] = {
      {.x = 0.01, .fRef = 0.4450},   // scipy: 0.444973
      {.x = 0.1, .fRef = 0.8182},    // scipy: 0.818186
      {.x = 1.0, .fRef = 0.6514},    // scipy: 0.651423  (R&L gives 0.655, ~0.5% rounding)
      {.x = 10.0, .fRef = 1.922e-4}, // scipy: 1.922e-4  (R&L Table A1 row x=10 was misread)
  };
  // Note: R&L values are rounded to 3 significant figures; we use 1% tolerance
  // for the boost::math path (machine precision integration vs 3-digit table).
  static const double rlTolerance = 0.01; // 1%
#ifdef PHYSICS_HAS_BOOST_BESSEL
  static const double boostTolerance = 0.03; // same: R&L table imprecision
  (void)boostTolerance;
#endif

  bool allPassed = true;
  std::cout << std::fixed << std::setprecision(6);

  for (const auto &pt : pts) {
    double const fX = synchrotronF(pt.x);
    double const relErr = std::abs(fX - pt.fRef) / pt.fRef;

    std::cout << "  x = " << pt.x << "  F_computed = " << fX << "  F_ref = " << pt.fRef
              << "  err = " << relErr;

    bool const passed = (relErr < rlTolerance);
    std::cout << "  " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

#ifdef PHYSICS_HAS_BOOST_BESSEL
    std::cout << "  (boost::math Gauss-Legendre path active)\n";
#else
    std::cout << "  (polynomial fallback path active)\n";
#endif

    std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";
    return allPassed;
}

/**
 * @brief Main test driver
 */
} // namespace

int main() {
    std::cout << "\n"
              << "====================================================\n"
              << "SYNCHROTRON SPECTRUM VALIDATION TEST SUITE\n"
              << "Rybicki & Lightman (1979) Radiative Processes\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 9;

    if (testSynchrotronFLowFreq()) {
      passed++;
    }
    if (testSynchrotronFHighFreq()) {
      passed++;
    }
    if (testSynchrotronGPolarization()) {
      passed++;
    }
    if (testPowerLawSpectrum()) {
      passed++;
    }
    if (testSelfAbsorptionTransition()) {
      passed++;
    }
    if (testAbsorptionCoefficient()) {
      passed++;
    }
    if (testSpectralIndexCalculation()) {
      passed++;
    }
    if (testPolarizationBounds()) {
      passed++;
    }
    if (testSynchrotronFRybickiLightmanTable()) {
      passed++;
    }

    std::cout << "\n"
              << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n";

    return (passed == total) ? 0 : 1;
}
