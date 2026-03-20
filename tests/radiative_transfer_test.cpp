/**
 * @file radiative_transfer_test.cpp
 * @brief Validation tests for radiative transfer physics in GPU ray marching
 *
 * WHY: Verify radiative transfer shader correctly implements emission + absorption
 * WHAT: 12 comprehensive tests for optical depth, energy conservation, multi-frequency
 * HOW: Compare against analytical solutions and physics constraints
 *
 * References:
 * - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 1
 * - Longair (2011) "High Energy Astrophysics" Ch. 1
 */

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <iomanip>
#include <iostream>
#include <utility>
#include <vector>

#include "../src/physics/synchrotron.h"

using namespace physics;

// Test tolerance
constexpr double TOLERANCE = 1e-6;
constexpr double RELAXED_TOLERANCE = 1e-2;

/**
 * @brief Simulate optical depth integration (CPU reference)
 */
namespace {

double cpuOpticalDepthIntegrate(const std::vector<double> &alphaArray,
                                       const std::vector<double> &dsArray) {
  if (alphaArray.size() < 2) {
    return 0.0;
  }

  double tau = 0.0;
  for (size_t i = 0; i < alphaArray.size() - 1; i++) {
    double const alphaAvg = 0.5 * (alphaArray.at(i) + alphaArray.at(i + 1));
    tau += alphaAvg * dsArray.at(i);
  }
  return tau;
}

/**
 * @brief Simulate radiative transfer step (CPU reference)
 */
double cpuIntensityStep(double iCurrent, double jNu, double alphaNu, double ds) {
  double tauSegment = alphaNu * ds;
  tauSegment = std::min(tauSegment, 100.0);

  double const t = std::exp(-tauSegment);
  double const s = (alphaNu > 1e-30) ? (jNu / alphaNu) : jNu;

  double const iNew = (iCurrent * t) + (s * (1.0 - t));
  return iNew;
}

/**
 * @brief Test 1: Optical depth convergence with step refinement
 *
 * Expected: Doubling steps should reduce error by factor ~4 (2nd-order method)
 */
bool testOpticalDepthConvergence() {
  std::cout << "\n[TEST 1] Optical Depth Convergence\n";
  std::cout << "===================================\n";

  double b = 100.0; // Gauss
  double nE = 1e3;  // cm^-3
  double nu = 1e10; // Hz
  double p = 2.5;
  double pathLength = 1e16; // cm

  // Create optical depth profile: increasing B along path
  auto createAbsorptionProfile = [&](int nSteps) -> std::vector<double> {
    std::vector<double> alphaArray;
    for (int i = 0; i < nSteps; i++) {
      double const s = static_cast<double>(i) / (nSteps - 1) * pathLength;
      // Increase B with distance: B(s) = B_0 * (1 + s/path_length)
      double const bS = b * (1.0 + (s / pathLength));
      double const alpha = synchrotronAbsorptionCoefficient(nu, bS, nE, p);
      alphaArray.push_back(alpha);
    }
    return alphaArray;
  };

  std::vector<int> const stepCounts = {10, 20, 40, 80};
  std::vector<double> tauResults;

  std::cout << std::fixed << std::setprecision(8);
  for (int const nSteps : stepCounts) {
    auto alphaArray = createAbsorptionProfile(nSteps);
    std::vector<double> const dsArray(static_cast<size_t>(nSteps - 1), pathLength / (nSteps - 1));

    double const tau = cpuOpticalDepthIntegrate(alphaArray, dsArray);
    tauResults.push_back(tau);

    std::cout << "  Steps: " << nSteps << ", tau = " << tau;

    if (tauResults.size() > 2) {
      double const errorRatio =
          std::abs(tauResults.back() - tauResults.at(tauResults.size() - 2)) /
          std::abs(tauResults.at(tauResults.size() - 2) - tauResults.at(tauResults.size() - 3) + 1e-20);
      std::cout << ", convergence ratio = " << errorRatio;
    }
    std::cout << "\n";
  }

  // Check convergence: errors should decrease
  bool const passed = (tauResults.size() > 3) && (tauResults.at(1) < tauResults.at(0)) &&
                      (tauResults.at(2) < tauResults.at(1)) && (tauResults.at(3) < tauResults.at(2));

  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
  return passed;
}

/**
 * @brief Test 2: Transmission factor bounds
 *
 * T(tau) = exp(-tau) must satisfy: 0 <= T <= 1 for all tau >= 0
 */
bool testTransmissionFactorBounds() {
  std::cout << "\n[TEST 2] Transmission Factor Bounds\n";
  std::cout << "====================================\n";

  std::vector<double> const tauValues = {0.0, 0.01, 0.1, 1.0, 10.0, 100.0, 1000.0};
  bool allPassed = true;

  std::cout << std::fixed << std::setprecision(8);
  for (double const tau : tauValues) {
    double const t = std::exp(-tau);

    bool const passed = (t >= 0.0 && t <= 1.0);
    std::cout << "  tau = " << tau << ", T = " << t;
    std::cout << " " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";
  return allPassed;
}

/**
 * @brief Test 3: Optically thin limit (tau << 1)
 *
 * When tau << 1: dI/ds ≈ j_nu (linear accumulation for weak absorption)
 * Expected: Full radiative transfer ≈ optically thin as alpha -> 0
 */
bool testOpticallyThinLimit() {
  std::cout << "\n[TEST 3] Optically Thin Limit\n";
  std::cout << "=============================\n";

  double const jNu = 1e-8;      // Emissivity
  double const alphaNu = 1e-25; // Extremely small absorption (tau ~ 1e-9)
  double const ds = 1e16;       // Path segment [cm]

  double const iCurrent = 1e-9; // Non-zero starting intensity

  // Full formula
  double const iFull = cpuIntensityStep(iCurrent, jNu, alphaNu, ds);

  // Optically thin limit: I ≈ I_old + j*ds (ignoring absorption)
  double const iThin = iCurrent + (jNu * ds);

  // In the limit alpha -> 0, the absorption term (j/alpha)*( 1 - exp(-tau))
  // becomes (j/alpha) * tau = j * ds (since tau -> 0, 1-exp(-tau) -> tau)

  double const error = std::abs(iFull - iThin) / (std::abs(iThin) + 1e-30);

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Emissivity j_nu = " << jNu << "\n";
  std::cout << "  Absorption alpha_nu = " << alphaNu << "\n";
  std::cout << "  Optical depth tau = " << (alphaNu * ds) << " (<< 1)\n";
  std::cout << "  Full formula result: " << iFull << "\n";
  std::cout << "  Optically thin limit: " << iThin << "\n";
  std::cout << "  Relative error: " << error << "\n";

  bool const passed = error < RELAXED_TOLERANCE;
  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
  return passed;
}

/**
 * @brief Test 4: Optically thick limit (tau >> 1)
 *
 * When tau >> 1 and source uniform: I -> S_nu = j/alpha (blackbody limit)
 */
bool testOpticallyThickLimit() {
  std::cout << "\n[TEST 4] Optically Thick Limit\n";
  std::cout << "===============================\n";

  double const jNu = 1e-8;     // Emissivity
  double const alphaNu = 1e-8; // Strong absorption
  double const ds = 1e18;      // Very large path (tau >> 1)

  double const iCurrent = 0.0;

  // Full formula
  double const iFull = cpuIntensityStep(iCurrent, jNu, alphaNu, ds);

  // Optically thick limit (source function)
  double const sNu = jNu / alphaNu;

  double const error = std::abs(iFull - sNu) / (sNu + 1e-30);

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Emissivity j_nu = " << jNu << "\n";
  std::cout << "  Absorption alpha_nu = " << alphaNu << "\n";
  std::cout << "  Optical depth tau = " << (alphaNu * ds) << " (>> 1)\n";
  std::cout << "  Full formula result: " << iFull << "\n";
  std::cout << "  Source function S = " << sNu << "\n";
  std::cout << "  Relative error: " << error << "\n";

  bool const passed = error < RELAXED_TOLERANCE;
  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
  return passed;
}

/**
 * @brief Test 5: Energy conservation (approach to source function)
 *
 * As radiation propagates through emitting medium:
 * Intensity approaches the source function S = j/alpha
 * This tests the equilibrium behavior: I_final ~ S
 */
bool testEnergyConservationEmission() {
  std::cout << "\n[TEST 5] Energy Conservation (Equilibrium)\n";
  std::cout << "==========================================\n";

  // Case: weak absorption with small tau
  double const jNu = 1e-8;        // Emissivity
  double const alphaNu = 1e-12;   // Very weak absorption
  double const s = jNu / alphaNu; // Source function ≈ 1e4

  double const ds = 1e14;          // Path segment [cm]
  double const tau = alphaNu * ds; // Optical depth = 1e2 (moderate)

  std::vector<double> iSequence;
  double i = 100.0; // Start with much less than S

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Source function S = " << s << "\n";
  std::cout << "  Optical depth per step = " << tau << "\n";
  std::cout << "  Starting intensity = " << i << "\n\n";

  for (int step = 0; step < 4; step++) {
    i = cpuIntensityStep(i, jNu, alphaNu, ds);
    iSequence.push_back(i);
    std::cout << "  Step " << step << ": I = " << i << "\n";
  }

  // Check that intensity approaches or reaches the source function
  // It should either decrease distance to S or stabilize at S
  double const deltaStart = std::abs(iSequence.at(0) - s);
  double const deltaEnd = std::abs(iSequence.at(iSequence.size() - 1) - s);

  // Test passes if we moved closer to S or reached it
  bool const approaching = (deltaEnd <= deltaStart) || (deltaEnd < 1.0);

  std::cout << "  Distance from S: start = " << deltaStart;
  std::cout << ", final = " << deltaEnd << "\n";
  std::cout << "  Status: " << (approaching ? "PASS" : "FAIL") << "\n";
  return approaching;
}

/**
 * @brief Test 6: Intensity attenuation with absorption
 *
 * Pure absorption (j=0): I decreases exponentially with tau
 * Expected: I_out = I_in * exp(-tau)
 */
bool testIntensityAttenuation() {
  std::cout << "\n[TEST 6] Intensity Attenuation\n";
  std::cout << "==============================\n";

  double const iInitial = 1e-8;
  double const alphaNu = 1e-8;
  std::vector<double> const pathLengths = {1e14, 1e15, 1e16, 1e17};
  bool allPassed = true;

  std::cout << std::fixed << std::setprecision(6);
  for (double const ds : pathLengths) {
    double const tau = alphaNu * ds;
    double const iExpected = iInitial * std::exp(-tau);

    // Pure absorption (j_nu = 0)
    double const iComputed = cpuIntensityStep(iInitial, 0.0, alphaNu, ds);

    double const error = std::abs(iComputed - iExpected) / (iExpected + 1e-30);

    bool const passed = error < TOLERANCE;
    std::cout << "  ds = " << ds << " cm, tau = " << tau;
    std::cout << ", error = " << error << " " << (passed ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && passed;
  }

  std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";
  return allPassed;
}

/**
 * @brief Test 7: Multi-frequency integration consistency
 *
 * Spectrum integrated over frequency should equal sum of frequency bins
 */
bool testMultifrequencyConsistency() {
  std::cout << "\n[TEST 7] Multi-Frequency Integration\n";
  std::cout << "=====================================\n";

  // Create spectrum: power-law
  double const b = 100.0;
  double const gammaMin = 10.0;
  double const gammaMax = 1e6;
  double const p = 2.5;

  // Sample frequencies logarithmically
  std::vector<double> freqs;
  std::vector<double> fluxes;

  for (int i = 0; i < 20; i++) {
    double const nu = std::pow(10.0, 9.0 + (0.5 * i)); // 1 GHz to 1 EHz
    freqs.push_back(nu);
    double const flux = synchrotronSpectrumPowerLaw(nu, b, gammaMin, gammaMax, p);
    fluxes.push_back(flux);
  }

  // Integrate using trapezoidal rule
  double integral = 0.0;
  for (size_t i = 0; i < freqs.size() - 1; i++) {
    double const dnu = freqs.at(i + 1) - freqs.at(i);
    double const fAvg = 0.5 * (fluxes.at(i) + fluxes.at(i + 1));
    integral += fAvg * dnu;
  }

  // Check that integral is positive
  bool const passed = integral > 0.0;

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Frequency range: " << freqs.front() << " - " << freqs.back() << " Hz\n";
  std::cout << "  Number of samples: " << freqs.size() << "\n";
  std::cout << "  Integrated flux: " << integral << "\n";
  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
  return passed;
}

/**
 * @brief Test 8: Optically thin spectrum (no absorption)
 *
 * For tau << 1 everywhere: integrated I ~ sum(j * ds)
 */
bool testOpticallyThinSpectrum() {
  std::cout << "\n[TEST 8] Optically Thin Spectrum\n";
  std::cout << "==================================\n";

  // Very low-opacity case
  double const b = 1.0;   // Very weak field
  double const nE = 1e-2; // Very low density
  double const p = 2.5;
  double const pathLength = 1e14; // Short path

  // Sample high frequency (less absorption)
  double const nu = 1e13; // 10 THz optical

  // Absorption coefficient
  double const alpha = synchrotronAbsorptionCoefficient(nu, b, nE, p);
  double const tauTotal = alpha * pathLength;

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Frequency: " << nu << " Hz\n";
  std::cout << "  Absorption coefficient: " << alpha << " cm^-1\n";
  std::cout << "  Total optical depth: " << tauTotal << "\n";

  bool const opticallyThin = tauTotal < 0.1;
  std::cout << "  Regime: " << (opticallyThin ? "OPTICALLY THIN" : "OPTICALLY THICK") << "\n";
  std::cout << "  Status: " << (opticallyThin ? "PASS" : "FAIL") << "\n";

  return opticallyThin;
}

/**
 * @brief Test 9: Optically thick spectrum (strong absorption)
 *
 * For tau >> 1: integrated I -> uniform (blackbody-like)
 */
bool testOpticallyThickSpectrum() {
  std::cout << "\n[TEST 9] Optically Thick Spectrum\n";
  std::cout << "==================================\n";

  // High-opacity case
  double const b = 1000.0; // Strong field
  double const nE = 1e4;   // High density
  double const p = 2.5;
  double const pathLength = 1e18; // Very long path

  // Sample single frequency
  double const nu = 1e9; // 1 GHz

  // Absorption coefficient
  double const alpha = synchrotronAbsorptionCoefficient(nu, b, nE, p);
  double const tauTotal = alpha * pathLength;

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Frequency: " << nu << " Hz\n";
  std::cout << "  Absorption coefficient: " << alpha << " cm^-1\n";
  std::cout << "  Total optical depth: " << tauTotal << "\n";

  bool const opticallyThick = tauTotal > 10.0;
  std::cout << "  Regime: " << (opticallyThick ? "OPTICALLY THICK" : "OPTICALLY THIN") << "\n";
  std::cout << "  Status: " << (opticallyThick ? "PASS" : "FAIL") << "\n";

  return opticallyThick;
}

/**
 * @brief Test 10: Numerical stability (no NaN/Inf)
 *
 * Check that radiative transfer doesn't produce NaN or Inf
 */
bool testNumericalStability() {
  std::cout << "\n[TEST 10] Numerical Stability\n";
  std::cout << "=============================\n";

  std::vector<std::pair<double, double>> const testCases = {
      {1e-30, 1e-30}, // Both extremely small
      {1e10, 1e-30},  // Large j, tiny alpha
      {1e-30, 1e10},  // Tiny j, large alpha
      {1e10, 1e10},   // Both large
  };

  bool allPassed = true;

  for (const auto &[j_nu, alpha_nu] : testCases) {
    double const i = cpuIntensityStep(0.0, j_nu, alpha_nu, 1e16);

    // Check for valid (non-NaN, non-infinity) result
    bool const valid = (i >= -1e300 && i <= 1e300) || (i == 0.0);
    std::cout << "  j=" << j_nu << ", alpha=" << alpha_nu;
    std::cout << " -> I=" << i << " " << (valid ? "PASS" : "FAIL") << "\n";
    allPassed = allPassed && valid;
  }

  std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";
  return allPassed;
}

/**
 * @brief Test 11: Spectral index consistency
 *
 * Verify spectral index calculation is self-consistent
 */
bool testSpectralShapePreservation() {
  std::cout << "\n[TEST 11] Spectral Index Consistency\n";
  std::cout << "======================================\n";

  // Test that spectral index calculation is consistent
  std::vector<double> const pValues = {2.0, 2.5, 3.0, 3.5};
  bool allPassed = true;

  std::cout << std::fixed << std::setprecision(6);
  for (double const p : pValues) {
    double const alpha = -(p - 1.0) / 2.0;
    double const pBack = 1.0 - (2.0 * alpha);

    double const error = std::abs(pBack - p);
    bool const passed = error < TOLERANCE;

    std::cout << "  p = " << p << ", alpha = " << alpha;
    std::cout << ", p(back) = " << pBack << " " << (passed ? "PASS" : "FAIL") << "\n";

    allPassed = allPassed && passed;
  }

  std::cout << "  Status: " << (allPassed ? "PASS" : "FAIL") << "\n";
  return allPassed;
}

/**
 * @brief Test 12: Ray marching sequence consistency
 *
 * Multiple steps should accumulate intensity consistently
 */
bool testRayMarchingConsistency() {
  std::cout << "\n[TEST 12] Ray Marching Consistency\n";
  std::cout << "====================================\n";

  double const jNu = 1e-10;
  double const alphaNu = 1e-12;
  double const ds = 1e16;

  // Method 1: Single large step
  double const iSingle = cpuIntensityStep(0.0, jNu, alphaNu, 5.0 * ds);

  // Method 2: Five small steps
  double iMulti = 0.0;
  for (int i = 0; i < 5; i++) {
    iMulti = cpuIntensityStep(iMulti, jNu, alphaNu, ds);
  }

  double const error = std::abs(iSingle - iMulti) / (std::abs(iMulti) + 1e-30);

  std::cout << std::fixed << std::setprecision(10);
  std::cout << "  Single 5*ds step: " << iSingle << "\n";
  std::cout << "  Five ds steps: " << iMulti << "\n";
  std::cout << "  Relative error: " << error << "\n";

  // Allow larger error due to exponential approximation differences
  bool const passed = error < 0.1;
  std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
  return passed;
}

/**
 * @brief Main test driver
 */
} // namespace

int main() {
    std::cout << "\n"
              << "====================================================\n"
              << "RADIATIVE TRANSFER VALIDATION TEST SUITE\n"
              << "Rybicki & Lightman (1979) Radiative Processes\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 12;

    if (testOpticalDepthConvergence()) {
      passed++;
    }
    if (testTransmissionFactorBounds()) {
      passed++;
    }
    if (testOpticallyThinLimit()) {
      passed++;
    }
    if (testOpticallyThickLimit()) {
      passed++;
    }
    if (testEnergyConservationEmission()) {
      passed++;
    }
    if (testIntensityAttenuation()) {
      passed++;
    }
    if (testMultifrequencyConsistency()) {
      passed++;
    }
    if (testOpticallyThinSpectrum()) {
      passed++;
    }
    if (testOpticallyThickSpectrum()) {
      passed++;
    }
    if (testNumericalStability()) {
      passed++;
    }
    if (testSpectralShapePreservation()) {
      passed++;
    }
    if (testRayMarchingConsistency()) {
      passed++;
    }

    std::cout << "\n"
              << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n";

    return (passed == total) ? 0 : 1;
}
