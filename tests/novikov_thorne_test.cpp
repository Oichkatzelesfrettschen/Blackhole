/**
 * @file novikov_thorne_test.cpp
 * @brief Validation tests for Novikov-Thorne disk model
 *
 * WHY: Verify physics correctness against analytical formulas and EHT data
 * WHAT: 8 comprehensive validation tests for radiative efficiency, temperature, flux
 * HOW: Compare against literature values (BPT 1972, Page & Thorne 1974, EHT M87*)
 */

#include "../src/physics/novikov_thorne.h"
#include "../src/physics/constants.h"
#include "../src/physics/page_thorne.h"
#include <iostream>
#include <cmath>
#include <iomanip>
#include <cassert>

using namespace blackhole::physics;

// Test tolerance
constexpr double RELAXED_TOLERANCE = 1e-4;

/**
 * @brief Test 1: Radiative efficiency for Schwarzschild black hole
 *
 * Expected: η = 0.0572 (5.72% efficiency for a=0)
 * Reference: Bardeen, Press, Teukolsky (1972), ApJ 178, 347
 */
namespace {

bool testEfficiencySchwarzschild() {
  std::cout << "\n[TEST 1] Schwarzschild Radiative Efficiency\n";
  std::cout << "============================================\n";

  const double aStar = 0.0;
  const double eta = NovikovThorneDisk::radiativeEfficiency(aStar);
  const double expected = 0.0572;

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Computed: η = " << eta << "\n";
  std::cout << "  Expected: η = " << expected << "\n";
  std::cout << "  Error:    " << std::abs(eta - expected) << "\n";

  const bool passed = std::abs(eta - expected) < RELAXED_TOLERANCE;
  std::cout << "  Status:   " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

  return passed;
}

/**
 * @brief Test 2: Radiative efficiency for near-extremal Kerr black hole
 *
 * Expected: eta = 1 - E_isco = 0.320994 (scripts/gen_page_thorne_reference.py)
 * Reference: BPT (1972)
 */
bool testEfficiencyKerrMaximal() {
  std::cout << "\n[TEST 2] Near-Extremal Kerr Radiative Efficiency\n";
  std::cout << "=================================================\n";

  const double aStar = 0.998;
  const double eta = NovikovThorneDisk::radiativeEfficiency(aStar);

  // E_isco = sqrt(1 - 2/(3 r_isco)) is exact at the ISCO for every spin.
  const double expected = 0.320994165616199;

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  Spin:     a* = " << aStar << "\n";
  std::cout << "  Computed: eta = " << eta << "\n";
  std::cout << "  Expected: eta = " << expected << "\n";

  const bool passed = std::abs(eta - expected) < 1e-5;
  std::cout << "  Status:   " << (passed ? "PASS" : "FAIL") << "\n";

  return passed;
}

/**
 * @brief Test 3: ISCO radius for Schwarzschild black hole
 *
 * Expected: r_ISCO = 6M
 * Reference: Standard result from Schwarzschild metric
 */
bool testIscoSchwarzschild() {
  std::cout << "\n[TEST 3] Schwarzschild ISCO Radius\n";
  std::cout << "===================================\n";

  const double aStar = 0.0;
  const double rIsco = NovikovThorneDisk::iscoRadius(aStar);
  const double expected = 6.0;

  std::cout << std::fixed << std::setprecision(10);
  std::cout << "  Computed: r_ISCO = " << rIsco << " M\n";
  std::cout << "  Expected: r_ISCO = " << expected << " M\n";
  std::cout << "  Error:    " << std::abs(rIsco - expected) << "\n";

  const bool passed = std::abs(rIsco - expected) < 1e-8;
  std::cout << "  Status:   " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

  return passed;
}

/**
 * @brief Test 4: ISCO radius for near-extremal Kerr black hole
 *
 * Expected: r_ISCO ≈ 1.24M (prograde orbit)
 * Reference: BPT (1972)
 */
bool testIscoKerrMaximal() {
  std::cout << "\n[TEST 4] Near-Extremal Kerr ISCO Radius\n";
  std::cout << "========================================\n";

  const double aStar = 0.998;
  const double rIsco = NovikovThorneDisk::iscoRadius(aStar);
  const double expected = 1.24; // Approximate

  std::cout << std::fixed << std::setprecision(10);
  std::cout << "  Spin:     a* = " << aStar << "\n";
  std::cout << "  Computed: r_ISCO = " << rIsco << " M\n";
  std::cout << "  Expected: r_ISCO ≈ " << expected << " M (±0.01)\n";
  std::cout << "  Error:    " << std::abs(rIsco - expected) << "\n";

  const bool passed = std::abs(rIsco - expected) < 0.01;
  std::cout << "  Status:   " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

  return passed;
}

/**
 * @brief Test 5: Temperature peak location
 *
 * Expected: T peaks at the continuous Page-Thorne flux maximum, 1.592 r_ISCO
 * (9.55 M) at a = 0 and 1.483 r_ISCO at a = 0.9
 * (scripts/gen_page_thorne_reference.py).
 * Reference: Page & Thorne (1974), ApJ 191, 499
 */
bool testTemperaturePeak() {
  std::cout << "\n[TEST 5] Temperature Peak Location\n";
  std::cout << "===================================\n";

  struct Case {
    double aStar;
    double ratio;
  };
  const Case cases[] = {{0.0, 1.5918213463}, {0.9, 1.4829887161}};
  bool allPassed = true;
  std::cout << std::fixed << std::setprecision(8);
  for (Case const &c : cases) {
    const double rPeak = NovikovThorneDisk::peakTemperatureRadius(c.aStar);
    const double rIsco = NovikovThorneDisk::iscoRadius(c.aStar);
    const double ratio = rPeak / rIsco;
    // The temperature maximum, located by scanning T itself, must sit there too.
    double tMax = 0.0;
    double rAtTMax = 0.0;
    for (int i = 0; i <= 20000; ++i) {
      const double r = rIsco * (1.0 + (1.5 * i / 20000.0));
      const double t = NovikovThorneDisk::diskTemperature(r, c.aStar, 0.1, 10.0);
      if (t > tMax) {
        tMax = t;
        rAtTMax = r;
      }
    }
    std::cout << "  a* = " << c.aStar << ": r_peak / r_ISCO = " << ratio << " (expected "
              << c.ratio << "), T scan peak at " << (rAtTMax / rIsco) << "\n";
    allPassed = allPassed && std::abs(ratio - c.ratio) < 1e-6 &&
                std::abs((rAtTMax / rIsco) - c.ratio) < 2e-4;
  }

  std::cout << "  Status:   " << (allPassed ? "PASS" : "FAIL") << "\n";

  return allPassed;
}

/**
 * @brief Test 6: Temperature vanishes inside ISCO
 *
 * Expected: T(r < r_ISCO) = 0 (no stable disk)
 */
bool testTemperatureInsideIsco() {
  std::cout << "\n[TEST 6] Temperature Inside ISCO\n";
  std::cout << "=================================\n";

  const double aStar = 0.0;
  const double rIsco = NovikovThorneDisk::iscoRadius(aStar);

  // Test points inside ISCO
  const double testRadii[] = {1.0, 2.0, 3.0, 5.0, 5.9};
  bool allPassed = true;

  std::cout << std::fixed << std::setprecision(10);
  std::cout << "  r_ISCO = " << rIsco << " M\n\n";

  for (double const r : testRadii) {
    if (r >= rIsco) {
      continue; // Skip if outside ISCO
    }

    const double t = NovikovThorneDisk::diskTemperature(r, aStar, 0.1, 4.0e6);
    const bool passed = (t == 0.0);

    std::cout << "  r = " << r << " M: T = " << t << " K ";
    std::cout << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    allPassed = allPassed && passed;
  }

  std::cout << "  Status:   " << (allPassed ? "PASS ✓" : "FAIL ✗") << "\n";

  return allPassed;
}

/**
 * @brief Test 7: Integrated luminosity consistency
 *
 * Expected: L = η * Mdot * c² (energy conservation)
 */
bool testIntegratedLuminosity() {
  std::cout << "\n[TEST 7] Integrated Luminosity\n";
  std::cout << "===============================\n";

  const double aStar = 0.5;
  const double mdotEdd = 0.1;
  const double massSolar = 4.0e6; // Sgr A*

  const double eta = NovikovThorneDisk::radiativeEfficiency(aStar);
  const double l = NovikovThorneDisk::integratedLuminosity(mdotEdd, aStar, massSolar);

  // Eddington luminosity
  const double lEdd = 1.26e38 * massSolar; // erg/s

  // Expected luminosity
  const double cCgs = ::physics::C; // cm/s
  const double mdotEddCgs = lEdd / (eta * cCgs * cCgs);
  const double expectedL = eta * mdotEdd * mdotEddCgs * cCgs * cCgs;

  std::cout << std::scientific << std::setprecision(6);
  std::cout << "  Spin:          a* = " << aStar << "\n";
  std::cout << "  Efficiency:    η = " << eta << "\n";
  std::cout << "  Accretion:     Mdot = " << mdotEdd << " * Mdot_Edd\n";
  std::cout << "  Mass:          M = " << massSolar << " M_sun\n\n";
  std::cout << "  Computed:      L = " << l << " erg/s\n";
  std::cout << "  Expected:      L = " << expectedL << " erg/s\n";
  std::cout << "  Relative err:  " << std::abs(l - expectedL) / expectedL << "\n";

  const bool passed = std::abs(l - expectedL) / expectedL < RELAXED_TOLERANCE;
  std::cout << "  Status:        " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

  return passed;
}

/**
 * @brief Test 8: Normalized flux peak location
 *
 * Expected: the normalized flux reaches 1 at the Page-Thorne peak, 1.592 r_ISCO
 * at a = 0 (sampled on a 0.01 M grid).
 */
bool testNormalizedFluxPeak() {
  std::cout << "\n[TEST 8] Normalized Flux Peak\n";
  std::cout << "==============================\n";

  const double aStar = 0.0;
  const double rIsco = NovikovThorneDisk::iscoRadius(aStar);

  // Sample flux at different radii
  double maxFlux = 0.0;
  double rAtMax = 0.0;

  const double radialStep = 0.01;
  const int radialIntervals = static_cast<int>((10.0 - rIsco) / radialStep);
  for (int sampleIndex = 0; sampleIndex <= radialIntervals; ++sampleIndex) {
    const double r = rIsco + (static_cast<double>(sampleIndex) * radialStep);
    const double flux = NovikovThorneDisk::normalizedFlux(r, aStar);
    if (flux > maxFlux) {
      maxFlux = flux;
      rAtMax = r;
    }
  }

  const double ratio = rAtMax / rIsco;

  std::cout << std::fixed << std::setprecision(8);
  std::cout << "  r_ISCO:      " << rIsco << " M\n";
  std::cout << "  r_peak_flux: " << rAtMax << " M\n";
  std::cout << "  Ratio:       " << ratio << "\n";
  std::cout << "  Expected:    1.5918 (+-0.002)\n";

  const bool passed = std::abs(ratio - 1.5918213463) < 0.002 && std::abs(maxFlux - 1.0) < 1e-6;
  std::cout << "  Status:      " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

  return passed;
}

/**
 * @brief Test 9: Temperature scale in CGS
 *
 * Expected: T^4 = 3 G M Mdot f / (8 pi sigma r^3) at r = 9 M, a = 0,
 * Mdot = 0.1 Mdot_Edd, M = 4e6 M_sun, with the Page-Thorne f(9 M) = 0.0822:
 * 1.565e5 K. physics::C is already in cm/s, so an extra factor 100 on c
 * inflates T by 100.
 */
bool testTemperatureScale() {
  std::cout << "\n[TEST 9] Temperature Scale (CGS)\n";
  std::cout << "=================================\n";

  const double aStar = 0.0;
  const double massSolar = 4.0e6;
  const double r = 9.0;
  const double t = NovikovThorneDisk::diskTemperature(r, aStar, 0.1, massSolar);

  const double c = ::physics::C;
  const double mass = massSolar * ::physics::M_SUN;
  const double eta = NovikovThorneDisk::radiativeEfficiency(aStar);
  const double mdot = 0.1 * 1.26e38 * massSolar / (eta * c * c);
  const double rCgs = r * ::physics::G * mass / (c * c);
  const double f = ::physics::pageThorneRelativisticFactor(r, aStar);
  const double expected = std::pow(3.0 * ::physics::G * mass * mdot * f /
                                       (8.0 * ::physics::PI * 5.67e-5 * rCgs * rCgs * rCgs),
                                   0.25);

  std::cout << std::scientific << std::setprecision(6);
  std::cout << "  Computed: T = " << t << " K\n";
  std::cout << "  Expected: T = " << expected << " K\n";

  const bool passed = std::abs(t / expected - 1.0) < 1e-9 && t > 1.0e5 && t < 1.0e6;
  std::cout << "  Status:   " << (passed ? "PASS" : "FAIL") << "\n";

  return passed;
}

/**
 * @brief Main test runner
 */
} // namespace

int main() {
    std::cout << "\n";
    std::cout << "========================================================\n";
    std::cout << "  Novikov-Thorne Disk Model Validation Tests\n";
    std::cout << "========================================================\n";

    int passed = 0;
    int const total = 9;

    // Run all tests
    if (testEfficiencySchwarzschild()) {
      passed++;
    }
    if (testEfficiencyKerrMaximal()) {
      passed++;
    }
    if (testIscoSchwarzschild()) {
      passed++;
    }
    if (testIscoKerrMaximal()) {
      passed++;
    }
    if (testTemperaturePeak()) {
      passed++;
    }
    if (testTemperatureInsideIsco()) {
      passed++;
    }
    if (testIntegratedLuminosity()) {
      passed++;
    }
    if (testNormalizedFluxPeak()) {
      passed++;
    }
    if (testTemperatureScale()) {
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
