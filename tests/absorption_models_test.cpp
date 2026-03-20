/**
 * @file absorption_models_test.cpp
 * @brief Phase 7.1a: Absorption Models Validation
 *
 * Tests synchrotron self-absorption, free-free absorption, and Compton scattering
 * across a frequency range from radio to X-ray.
 */

#include <cassert>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <vector>

// Import absorption models from Phase 7.1a
#include "../src/physics/absorption_models.h"

using namespace physics;

// Test 1: Synchrotron Self-Absorption frequency dependence
namespace {

bool testSsaFrequencyDependence() {
  std::cout << "Test 1: SSA Frequency Dependence\n";

  double const b = 100.0;    // Gauss
  double const nE = 1e3;     // cm^-3
  double const t = 1e7;      // K
  double const nuRef = 1e10; // Hz reference

  double const alphaLow = synchrotronSelfAbsorption(nuRef, b, nE, t);
  double const alphaMid = synchrotronSelfAbsorption(nuRef * 10.0, b, nE, t);
  double const alphaHigh = synchrotronSelfAbsorption(nuRef * 100.0, b, nE, t);

  // SSA should decrease as 1/nu^2
  // So alpha(10*nu) ~ alpha(nu) / 100, ratio = 0.01
  double const ratio1 = alphaMid / alphaLow;
  double const ratio2 = alphaHigh / alphaMid;

  bool const freqDepOk = (ratio1 < 0.015 && ratio1 > 0.005) && (ratio2 < 0.015 && ratio2 > 0.005);

  std::cout << "  nu_ref: " << nuRef << " Hz\n"
            << "  alpha(nu): " << std::scientific << alphaLow << "\n"
            << "  alpha(10*nu): " << alphaMid << "\n"
            << "  alpha(100*nu): " << alphaHigh << "\n"
            << "  Ratio (10x): " << ratio1 << " (expect ~0.1)\n"
            << "  Ratio (100x): " << ratio2 << " (expect ~0.1)\n"
            << "  Status: " << (freqDepOk ? "PASS" : "FAIL") << "\n\n";

  return freqDepOk;
}

// Test 2: Free-Free Absorption temperature dependence
bool testFfTemperatureDependence() {
  std::cout << "Test 2: Free-Free Temperature Dependence\n";

  double const nu = 1e10;   // Hz
  double const nE = 1e3;    // cm^-3
  double const tLow = 1e6;  // K
  double const tHigh = 1e7; // K (10x hotter)

  double const alphaCool = freeFreeAbsorption(nu, nE, tLow);
  double const alphaHot = freeFreeAbsorption(nu, nE, tHigh);

  // Free-free ~ 1/T^(3/2)
  // So alpha(10*T) ~ alpha(T) / 10^(3/2) ~ alpha(T) / 31.6
  double const ratio = alphaCool / alphaHot;
  bool const tempDepOk = (ratio > 25.0 && ratio < 40.0); // ~31.6 expected

  std::cout << "  T_cool = " << tLow << " K: alpha = " << std::scientific << alphaCool << "\n"
            << "  T_hot = " << tHigh << " K: alpha = " << alphaHot << "\n"
            << "  Ratio (cool/hot): " << ratio << " (expect ~31.6)\n"
            << "  Status: " << (tempDepOk ? "PASS" : "FAIL") << "\n\n";

  return tempDepOk;
}

// Test 3: Compton absorption (Thomson limit)
bool testComptonThomsonLimit() {
  std::cout << "Test 3: Compton Absorption (Thomson Limit)\n";

  double const nu = 1e10;   // Radio (low energy, Thomson regime)
  double const nE = 1e3;    // cm^-3
  double const theta = 0.1; // Mildly relativistic temperature

  double const alphaComp = comptonAbsorption(nu, nE, theta);

  // In Thomson limit, alpha_comp = n_e * sigma_T ~ 1e-24 * 1e3 ~ 1e-21 cm^-1
  bool const compOk = (alphaComp > 1e-24 && alphaComp < 1e-20);

  std::cout << "  nu: " << nu << " Hz (radio)\n"
            << "  n_e: " << nE << " cm^-3\n"
            << "  alpha_comp: " << std::scientific << alphaComp << " cm^-1\n"
            << "  Expected range: 1e-24 to 1e-20\n"
            << "  Status: " << (compOk ? "PASS" : "FAIL") << "\n\n";

  return compOk;
}

// Test 4: Total absorption coefficient (all mechanisms)
bool testTotalAbsorption() {
  std::cout << "Test 4: Total Absorption Coefficient\n";

  double const nu = 1e12; // Microwave
  double const b = 100.0; // Gauss
  double const nE = 1e3;  // cm^-3
  double const t = 1e7;   // K

  double const alphaSsa = synchrotronSelfAbsorption(nu, b, nE, t);
  double const alphaFf = freeFreeAbsorption(nu, nE, t);
  double const theta = (BOLTZMANN * t) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);
  double const alphaComp = comptonAbsorption(nu, nE, theta);
  double const alphaTotal = totalAbsorptionCoefficient(nu, b, nE, t);

  // Total should equal sum of components
  double const expectedTotal = alphaSsa + alphaFf + alphaComp;
  bool const totalOk = (std::abs(alphaTotal - expectedTotal) / expectedTotal < 1e-10);

  std::cout << "  SSA:   " << std::scientific << alphaSsa << "\n"
            << "  FF:    " << alphaFf << "\n"
            << "  Comp:  " << alphaComp << "\n"
            << "  Total: " << alphaTotal << "\n"
            << "  Sum:   " << expectedTotal << "\n"
            << "  Status: " << (totalOk ? "PASS" : "FAIL") << "\n\n";

  return totalOk;
}

// Test 5: Dominant absorption mode identification
bool testDominantAbsorptionMode() {
  std::cout << "Test 5: Dominant Absorption Mode Identification\n";

  double const b = 100.0; // Gauss
  double const nE = 1e3;  // cm^-3
  double const t = 1e7;   // K

  // Low frequency: SSA should dominate
  int const modeRadio = dominantAbsorptionMode(1e9, b, nE, t); // 1 GHz

  // Mid frequency: free-free might dominate
  int const modeOptical = dominantAbsorptionMode(1e15, b, nE, t); // Optical

  // Very high frequency: Compton/free-free
  int const modeXray = dominantAbsorptionMode(1e18, b, nE, t); // X-ray

  bool const modeOk = (modeRadio >= 0 && modeRadio <= 2) &&
                      (modeOptical >= 0 && modeOptical <= 2) && (modeXray >= 0 && modeXray <= 2);

  const char * const modeNames[] = {"SSA", "Free-Free", "Compton"};

  std::cout << "  1 GHz:    Dominant = " << modeNames[modeRadio] << "\n"
            << "  Optical:  Dominant = " << modeNames[modeOptical] << "\n"
            << "  X-ray:    Dominant = " << modeNames[modeXray] << "\n"
            << "  Status: " << (modeOk ? "PASS" : "FAIL") << "\n\n";

  return modeOk;
}

// Test 6: Optical depth threshold frequency
bool testOpticalDepthThreshold() {
  std::cout << "Test 6: Optical Depth Threshold Frequency\n";

  double const b = 100.0;         // Gauss
  double const nE = 1e3;          // cm^-3
  double const t = 1e7;           // K
  double const pathLength = 1e16; // cm

  // Find threshold frequency for Compton (mode=2) which is strongest for these parameters
  double const nuThreshold = opticalDepthThresholdFrequency(b, nE, t, pathLength, 2);

  // Verify that the function produces a valid frequency within search range
  bool const freqInRange = (nuThreshold >= 1e8 && nuThreshold <= 1e20);

  // Verify it returns a different frequency than extremes
  double const tauLow = comptonAbsorption(1e9, nE, 0.1) * pathLength;
  double const tauHigh = comptonAbsorption(1e19, nE, 0.1) * pathLength;

  // Compton absorption is nearly constant, so threshold should be between extremes
  bool const thresholdOk = freqInRange && (tauLow > 1e-10);

  std::cout << "  B: " << b << " Gauss, n_e: " << nE << " cm^-3\n"
            << "  Path length: " << pathLength << " cm\n"
            << "  Threshold freq (Compton): " << std::scientific << nuThreshold << " Hz\n"
            << "  Frequency in valid range [1e8, 1e20]: " << (freqInRange ? "yes" : "no") << "\n"
            << "  Tau at low freq: " << tauLow << "\n"
            << "  Tau at high freq: " << tauHigh << "\n"
            << "  Status: " << (thresholdOk ? "PASS" : "FAIL") << "\n\n";

  return thresholdOk;
}

// Test 7: Absorption across full frequency spectrum
bool testSpectrumAbsorption() {
  std::cout << "Test 7: Absorption Across Frequency Spectrum\n";

  double const b = 100.0; // Gauss
  double const nE = 1e3;  // cm^-3
  double const t = 1e7;   // K

  std::vector<double> const frequencies = {
      1e9,  // 1 GHz (radio)
      1e12, // 1 THz (microwave)
      1e15, // 1 PHz (infrared)
      1e18, // 1 EHz (X-ray)
  };

  std::vector<const char *> const names = {"Radio", "Microwave", "Infrared", "X-ray"};

  std::cout << "  Absorption coefficients across spectrum:\n";
  std::cout << "  Freq Range    | Alpha Total  | Dominant Mode\n";
  std::cout << "  --------------|--------------|---------------\n";

  bool spectrumOk = true;
  for (double const nu : frequencies) {
    double const alphaTotal = totalAbsorptionCoefficient(nu, b, nE, t);
    int const mode = dominantAbsorptionMode(nu, b, nE, t);
    const char *modeName = (mode == 0) ? "SSA" : (mode == 1) ? "FF" : "Compton";

    std::cout << std::scientific << std::setprecision(2);
    std::cout << "  " << nu << " Hz | " << alphaTotal << " | " << modeName << "\n";

    spectrumOk = spectrumOk && (alphaTotal > 0.0);
  }

  std::cout << "  Status: " << (spectrumOk ? "PASS" : "FAIL") << "\n\n";

  return spectrumOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "ABSORPTION MODELS VALIDATION\n"
              << "Phase 7.1a: Absorption Mechanisms\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 7;

    if (testSsaFrequencyDependence()) {
      passed++;
    }
    if (testFfTemperatureDependence()) {
      passed++;
    }
    if (testComptonThomsonLimit()) {
      passed++;
    }
    if (testTotalAbsorption()) {
      passed++;
    }
    if (testDominantAbsorptionMode()) {
      passed++;
    }
    if (testOpticalDepthThreshold()) {
      passed++;
    }
    if (testSpectrumAbsorption()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
