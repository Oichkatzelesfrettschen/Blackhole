/**
 * @file scattering_models_test.cpp
 * @brief Phase 7.1b: Scattering Models Validation
 *
 * Tests Thomson, Rayleigh, and Mie scattering across frequency range
 * and verifies albedo and asymmetry properties.
 */

#include <algorithm>
#include <cassert>
#include <cmath>
#include <cstddef>
#include <iomanip>
#include <iostream>
#include <vector>

// Import scattering models from Phase 7.1b
#include "../src/physics/scattering_models.h"

using namespace physics;

// Test 1: Thomson cross-section constant at low frequencies
namespace {

bool testThomsonFrequencyIndependence() {
  std::cout << "Test 1: Thomson Cross-Section Frequency Independence\n";

  // Test at radio and microwave frequencies where Thomson dominates
  std::vector<double> const frequencies = {1e9, 1e10, 1e11, 1e12, 1e13};
  double const sigmaT = thomsonCrossSection();

  bool independent = true;
  double maxDeviation = 0.0;
  std::cout << "  Low frequencies: ";
  for (double const nu : frequencies) {
    // Thomson should be approximately constant at low frequencies
    double const sigmaKn = thomsonCrossSectionCorrected(nu, 0.01); // Cool plasma
    double const deviation = std::abs(sigmaKn - sigmaT) / sigmaT;
    maxDeviation = std::max(maxDeviation, deviation);
    independent = independent && (deviation < 0.05); // 5% tolerance

    std::cout << std::scientific << nu << "Hz:" << sigmaKn << " ";
  }

  std::cout << "\n  Thomson constant: " << std::scientific << sigmaT << "\n"
            << "  Max deviation: " << maxDeviation << "\n"
            << "  Status: " << (independent ? "PASS" : "FAIL") << "\n\n";

  return independent;
}

// Test 2: Rayleigh scattering 1/nu^4 dependence
bool testRayleighFrequencyDependence() {
  std::cout << "Test 2: Rayleigh Scattering Frequency Dependence\n";

  double const grainRadius = 0.1e-4; // 0.1 micron
  double const nGrain = 1.5;         // Refractive index

  // Test at three frequencies
  double const nuLow = 1e10;  // 10 GHz
  double const nuMid = 1e14;  // Optical
  double const nuHigh = 1e18; // X-ray

  double const sigmaLow = rayleighScattering(nuLow, grainRadius, nGrain);
  double const sigmaMid = rayleighScattering(nuMid, grainRadius, nGrain);
  double const sigmaHigh = rayleighScattering(nuHigh, grainRadius, nGrain);

  // Ratio should follow 1/nu^4
  // sigma(100*nu) ~ sigma(nu) / 100^4 = sigma(nu) / 10^8
  double const ratio1 = sigmaLow / sigmaMid;
  double const ratio2 = sigmaMid / sigmaHigh;

  // Expected: (nu_low / nu_mid)^4 = (1e10 / 1e14)^4 = 1e-16
  // so ratio_1 ~ 1e-16
  bool const freqDepOk = (ratio1 > 1e-17 && ratio1 < 1e-15) && (ratio2 > 1e-17 && ratio2 < 1e-15);

  std::cout << std::scientific;
  std::cout << "  Low freq (1e10 Hz): sigma = " << sigmaLow << "\n"
            << "  Mid freq (1e14 Hz): sigma = " << sigmaMid << "\n"
            << "  High freq (1e18 Hz): sigma = " << sigmaHigh << "\n"
            << "  Ratio (low/mid): " << ratio1 << " (expect ~1e-16)\n"
            << "  Ratio (mid/high): " << ratio2 << " (expect ~1e-16)\n"
            << "  Status: " << (freqDepOk ? "PASS" : "FAIL") << "\n\n";

  return freqDepOk;
}

// Test 3: Mie scattering efficiency across size parameters
bool testMieScatteringEfficiency() {
  std::cout << "Test 3: Mie Scattering Efficiency\n";

  double const nu = 1e15; // Optical frequency

  // Test at various grain sizes
  std::vector<double> radii = {
      1e-5, // 0.01 micron (very small, Rayleigh limit)
      1e-4, // 0.1 micron (Rayleigh transition)
      1e-3, // 1 micron (Mie regime)
      1e-2, // 10 micron (large, geometric limit)
  };

  std::vector<const char *> labels = {
      "Very small",
      "Small",
      "Medium",
      "Large",
  };

  std::cout << "  Grain Size      | Q_sca    | Regime\n";
  std::cout << "  ---------------|---------|---------\n";

  bool efficiencyOk = true;
  for (size_t i = 0; i < radii.size(); i++) {
    double const q = mieScatteringEfficiency(nu, radii.at(i));
    std::cout << std::scientific << std::setprecision(2);
    std::cout << "  " << radii.at(i) << " cm | " << q << " | " << labels.at(i) << "\n";

    efficiencyOk = efficiencyOk && (q >= 0.0 && q <= 4.5);
  }

  std::cout << "  Status: " << (efficiencyOk ? "PASS" : "FAIL") << "\n\n";

  return efficiencyOk;
}

// Test 4: Single-scattering albedo
bool testSingleScatteringAlbedo() {
  std::cout << "Test 4: Single-Scattering Albedo\n";

  // Test cases
  double const sigmaSca1 = 1e-20; // Mostly scattering
  double const sigmaAbs1 = 1e-22;

  double const sigmaSca2 = 1e-22; // Mostly absorbing
  double const sigmaAbs2 = 1e-20;

  double const sigmaSca3 = 1e-20; // Equal scattering and absorption
  double const sigmaAbs3 = 1e-20;

  double const albedo1 = singleScatteringAlbedo(sigmaSca1, sigmaAbs1);
  double const albedo2 = singleScatteringAlbedo(sigmaSca2, sigmaAbs2);
  double const albedo3 = singleScatteringAlbedo(sigmaSca3, sigmaAbs3);

  bool const albedoOk = (albedo1 > 0.98 && albedo1 <= 1.0) && // Should scatter
                        (albedo2 < 0.02 && albedo2 >= 0.0) && // Should absorb
                        (albedo3 > 0.49 && albedo3 < 0.51);   // Should be ~0.5

  std::cout << "  Case 1 (scattering dominant): omega = " << albedo1 << " (expect ~1.0)\n"
            << "  Case 2 (absorption dominant): omega = " << albedo2 << " (expect ~0.0)\n"
            << "  Case 3 (equal): omega = " << albedo3 << " (expect ~0.5)\n"
            << "  Status: " << (albedoOk ? "PASS" : "FAIL") << "\n\n";

  return albedoOk;
}

// Test 5: Asymmetry parameter ranges
bool testAsymmetryParameter() {
  std::cout << "Test 5: Asymmetry Parameter\n";

  double const nu = 1e15; // Optical

  // Thomson scattering
  double const gThomson = asymmetryParameter(0, nu);

  // Rayleigh scattering
  double const gRayleigh = asymmetryParameter(1, nu);

  // Mie scattering (very small grain, Rayleigh-like)
  double const gMieSmall = asymmetryParameter(2, nu, 1e-7);

  // Mie scattering (large grain)
  double const gMieLarge = asymmetryParameter(2, nu, 1e-2);

  bool const paramOk = (gThomson > 0.1 && gThomson < 0.3) &&  // Thomson forward-peaked
                       (std::abs(gRayleigh) < 0.1) &&         // Rayleigh isotropic
                       (std::abs(gMieSmall) < 0.15) &&        // Very small Mie -> isotropic
                       (gMieLarge > 0.3 && gMieLarge < 0.99); // Large Mie -> forward

  std::cout << "  Thomson (forward-peaked): g = " << gThomson << " (expect 0.1-0.3)\n"
            << "  Rayleigh (isotropic): g = " << gRayleigh << " (expect ~0)\n"
            << "  Mie very small (Rayleigh-like): g = " << gMieSmall << " (expect ~0)\n"
            << "  Mie large (forward): g = " << gMieLarge << " (expect 0.3-0.99)\n"
            << "  Status: " << (paramOk ? "PASS" : "FAIL") << "\n\n";

  return paramOk;
}

// Test 6: Thomson opacity scaling with density
bool testThomsonOpacityScaling() {
  std::cout << "Test 6: Thomson Opacity Density Scaling\n";

  double const nELow = 1e3;  // cm^-3
  double const nEMid = 1e4;  // 10x higher
  double const nEHigh = 1e5; // 100x higher

  double const kappaLow = thomsonOpacity(nELow);
  double const kappaMid = thomsonOpacity(nEMid);
  double const kappaHigh = thomsonOpacity(nEHigh);

  // Opacity should scale linearly with density
  double const ratio1 = kappaMid / kappaLow;  // Should be ~10
  double const ratio2 = kappaHigh / kappaMid; // Should be ~10

  bool const scalingOk = (ratio1 > 9.9 && ratio1 < 10.1) && (ratio2 > 9.9 && ratio2 < 10.1);

  std::cout << std::scientific;
  std::cout << "  n_e = 1e3: kappa = " << kappaLow << "\n"
            << "  n_e = 1e4: kappa = " << kappaMid << " (ratio: " << ratio1 << ")\n"
            << "  n_e = 1e5: kappa = " << kappaHigh << " (ratio: " << ratio2 << ")\n"
            << "  Status: " << (scalingOk ? "PASS" : "FAIL") << "\n\n";

  return scalingOk;
}

// Test 7: Total scattering opacity combination
bool testTotalScatteringOpacity() {
  std::cout << "Test 7: Total Scattering Opacity\n";

  double const nu = 1e14;            // Optical
  double const nE = 1e3;             // cm^-3
  double const grainRadius = 1e-4;   // 0.1 micron
  double const grainDensity = 1e-12; // Very low density

  double const kappaTotal = totalScatteringOpacity(nu, nE, grainRadius, grainDensity);

  // Should be positive and real
  double const kappaT = thomsonOpacity(nE);
  double const kappaR = rayleighOpacity(nu, grainRadius, grainDensity, 1.5);
  double const kappaMie = mieOpacity(nu, grainRadius, grainDensity);

  double const expected = kappaT + kappaR + kappaMie;
  bool const totalOk = (std::abs(kappaTotal - expected) / expected < 1e-10);

  std::cout << std::scientific;
  std::cout << "  Thomson: " << kappaT << "\n"
            << "  Rayleigh: " << kappaR << "\n"
            << "  Mie: " << kappaMie << "\n"
            << "  Total: " << kappaTotal << "\n"
            << "  Expected: " << expected << "\n"
            << "  Status: " << (totalOk ? "PASS" : "FAIL") << "\n\n";

  return totalOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "SCATTERING MODELS VALIDATION\n"
              << "Phase 7.1b: Scattering Physics\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 7;

    if (testThomsonFrequencyIndependence()) {
      passed++;
    }
    if (testRayleighFrequencyDependence()) {
      passed++;
    }
    if (testMieScatteringEfficiency()) {
      passed++;
    }
    if (testSingleScatteringAlbedo()) {
      passed++;
    }
    if (testAsymmetryParameter()) {
      passed++;
    }
    if (testThomsonOpacityScaling()) {
      passed++;
    }
    if (testTotalScatteringOpacity()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
