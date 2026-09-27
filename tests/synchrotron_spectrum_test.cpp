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

#include <algorithm>
#include <array>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <exception>
#include <iomanip>
#include <iostream>
#include <vector>

#include "../shader/include/synchrotron_lut_domain.h"
#include "../src/physics/synchrotron.h"

using namespace physics;

// Tolerances for algebraic and approximate spectral-index checks.
constexpr double TOLERANCE = 1e-5;
constexpr double RELAXED_TOLERANCE = 0.15;

namespace {

/// Mirrors synchLutSample in shader/include/synchrotron_emission.glsl: linear
/// interpolation at texel centers over the log domain, continued past the
/// table ends by the leading asymptotes x^(1/3) and sqrt(x) e^-x.
double sampleSynchrotronLut(const std::vector<float> &values, double x) {
  constexpr int entryCount = SYNCH_G_LUT_DOMAIN_ENTRIES;
  constexpr double xMin = SYNCH_G_LUT_DOMAIN_X_MIN;
  constexpr double xMax = SYNCH_G_LUT_DOMAIN_X_MAX;
  const double logRatio = std::log(xMax / xMin);
  const double clamped = std::clamp(x, xMin, xMax);
  const double coordinate = std::log(clamped / xMin) / logRatio;
  const double texcoord = ((coordinate * (entryCount - 1)) + 0.5) / entryCount;
  const double texel = (texcoord * entryCount) - 0.5;
  const int left = std::clamp(static_cast<int>(std::floor(texel)), 0, entryCount - 1);
  const int right = std::clamp(left + 1, 0, entryCount - 1);
  const double weight = std::clamp(texel - std::floor(texel), 0.0, 1.0);
  const auto leftValue = static_cast<double>(values.at(static_cast<std::size_t>(left)));
  const auto rightValue = static_cast<double>(values.at(static_cast<std::size_t>(right)));
  const double value = (leftValue * (1.0 - weight)) + (rightValue * weight);
  if (x < xMin) {
    return value * std::cbrt(x / xMin);
  }
  if (x > xMax) {
    return value * std::sqrt(x / xMax) * std::exp(xMax - x);
  }
  return value;
}

bool withinRelative(double got, double expected, double tolerance, const char *label, double x) {
  const double error = std::abs((got / expected) - 1.0);
  if (error > tolerance) {
    std::cerr << label << " x=" << x << " relative error=" << error << '\n';
    return false;
  }
  return true;
}

bool testSynchrotronFLut() {
  constexpr int entryCount = SYNCH_G_LUT_DOMAIN_ENTRIES;
  constexpr double xMin = SYNCH_G_LUT_DOMAIN_X_MIN;
  constexpr double xMax = SYNCH_G_LUT_DOMAIN_X_MAX;
  std::vector<float> values(entryCount);
  synchrotronFGenerateLut(values.data(), entryCount, xMin, xMax);
  const double logRatio = std::log(xMax / xMin);
  bool passed = true;
  for (int index = 0; index < entryCount; ++index) {
    const double x = xMin * std::exp(index * logRatio / (entryCount - 1));
    passed = withinRelative(static_cast<double>(values.at(static_cast<std::size_t>(index))),
                            synchrotronF(x), 1.0e-6, "F LUT entry", x) &&
             passed;
  }
  const auto sample = [&values](double x) { return sampleSynchrotronLut(values, x); };
  // The continuation meets the end entries and follows the asymptotes.
  for (const double join : {xMin, xMax}) {
    passed = withinRelative(sample(join * (1.0 - 1.0e-9)), sample(join * (1.0 + 1.0e-9)), 1.0e-6,
                            "F LUT join", join) &&
             passed;
  }
  const std::array<double, 6> probes = {1.0e-5, 50.0, 0.0099, 0.0101, 9.9, 10.1};
  passed = std::ranges::all_of(probes,
                               [&](double x) {
                                 return withinRelative(sample(x), synchrotronF(x), 0.02,
                                                       "F LUT sample", x);
                               }) &&
           passed;
  return passed;
}

} // namespace

/**
 * @brief Test 1: Synchrotron F(x) against mpmath at low frequencies
 *
 * The reference values use the mpmath 1.4.1 scaled-tail rows in
 * tests/bessel_k_reference.inc, evaluated as x * exp(-x) * e^x * tail.
 */
namespace {

bool testSynchrotronFLowFreq() {
  std::cout << "\n[TEST 1] Synchrotron F(x) - Low Frequency Regime\n";
  std::cout << "=================================================\n";

  struct TestPoint {
    double x;
    double fRef;
  };
  constexpr TestPoint testPoints[] = {
      {.x = 1.0e-4, .fRef = 0.09959088308506682},
      {.x = 1.0e-3, .fRef = 0.21313906509145042},
      {.x = 0.0099, .fRef = 0.44360483593514838},
  };
  bool allPassed = true;

  for (const TestPoint &point : testPoints) {
    const double fX = synchrotronF(point.x);
    const double error = std::abs(fX - point.fRef) / point.fRef;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  x = " << point.x << "\n";
    std::cout << "    F(x) computed: " << fX << "\n";
    std::cout << "    F(x) expected: " << point.fRef << "\n";
    std::cout << "    Relative err:  " << error << "\n";

    bool const passed = error < 2.0e-15;
    std::cout << "    Status:        " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  return allPassed;
}

/**
 * @brief Test 2: Synchrotron F(x) against mpmath at high frequencies
 *
 * The reference values use the mpmath 1.4.1 scaled-tail rows in
 * tests/bessel_k_reference.inc, evaluated as x * exp(-x) * e^x * tail.
 */
bool testSynchrotronFHighFreq() {
  std::cout << "\n[TEST 2] Synchrotron F(x) - High Frequency Regime\n";
  std::cout << "==================================================\n";

  struct TestPoint {
    double x;
    double fRef;
  };
  constexpr TestPoint testPoints[] = {
      {.x = 10.92, .fRef = 7.9664430952276931e-5},
      {.x = 30.0, .fRef = 6.5807945577077005e-13},
      {.x = 100.0, .fRef = 4.6975936659221719e-43},
  };
  bool allPassed = true;

  for (const TestPoint &point : testPoints) {
    const double fX = synchrotronF(point.x);
    const double error = std::abs(fX - point.fRef) / point.fRef;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  x = " << point.x << "\n";
    std::cout << "    F(x) computed: " << fX << "\n";
    std::cout << "    F(x) expected: " << point.fRef << "\n";
    std::cout << "    Relative err:  " << error << "\n";

    bool const passed = error < 2.0e-15;
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
 * The log grid spans x = 1e-4 through x = 700.
 */
bool testPolarizationBounds() {
  std::cout << "\n[TEST 8] Polarization Degree Bounds\n";
  std::cout << "====================================\n";

  constexpr int pointCount = 257;
  const double logMinimum = std::log(1.0e-4);
  const double logMaximum = std::log(700.0);
  bool allPassed = true;

  std::cout << std::fixed << std::setprecision(6);

  for (int point = 0; point < pointCount; ++point) {
    const double fraction = static_cast<double>(point) / static_cast<double>(pointCount - 1);
    const double x = std::exp(logMinimum + (fraction * (logMaximum - logMinimum)));
    double const fVal = synchrotronF(x);
    double const gVal = synchrotronG(x);
    const double pol = gVal / fVal;

    // The physical polarization fraction is bounded by unity.
    bool const passed = (fVal > 0.0 && gVal >= 0.0 && pol >= 0.0 && pol <= 1.0);

    std::cout << "  x = " << x << ": Pol = " << pol;
    std::cout << " " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  // synchrotronPolarization forms G/F from the scaled kernel values, so it
  // agrees with the direct ratio where both are representable and tends to 1
  // (G/F = 1 - 2/(3x) + O(x^-2)) where F and G underflow.
  const double midRatio = synchrotronG(50.0) / synchrotronF(50.0);
  const bool midAgrees = std::abs(synchrotronPolarization(50.0) - midRatio) <= 1e-13 * midRatio;
  const double far = synchrotronPolarization(1.0e4);
  const bool farLimit = std::abs(far - (1.0 - (2.0 / 3.0e4))) < 1e-7;
  std::cout << "  Pol(50) matches G/F: " << (midAgrees ? "PASS" : "FAIL") << "\n";
  std::cout << "  Pol(1e4) = " << far << ": " << (farLimit ? "PASS" : "FAIL") << "\n";
  allPassed = allPassed && midAgrees && farLimit;

  std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";

  return allPassed;
}

/**
 * @brief Test 9: Synchrotron F(x) accuracy against Rybicki-Lightman Table A1
 *
 * WHY: The Bessel kernel evaluates the exact integral used by the reference.
 *
 * Reference values from Rybicki & Lightman (1979) Table A1, page 232.
 * Values confirmed by independent numerical integration.
 *
 * Tolerance: 1% for the three-significant-digit literature table.
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
  // The literature values are rounded to three significant figures.
  static const double rlTolerance = 0.01; // 1%

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

    std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";
    return allPassed;
}

/**
 * @brief Main test driver
 */
} // namespace

int main() try {
    std::cout << "\n"
              << "====================================================\n"
              << "SYNCHROTRON SPECTRUM VALIDATION TEST SUITE\n"
              << "Rybicki & Lightman (1979) Radiative Processes\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 10;

    if (testSynchrotronFLut()) {
      passed++;
    }

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
} catch (const std::exception &error) {
    std::cerr << "Synchrotron validation failed: " << error.what() << '\n';
    return 1;
}
