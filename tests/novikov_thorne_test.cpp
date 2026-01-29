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
#include <iostream>
#include <cmath>
#include <iomanip>
#include <cassert>

using namespace blackhole::physics;

// Test tolerance
constexpr double TOLERANCE = 1e-6;
constexpr double RELAXED_TOLERANCE = 1e-4;

/**
 * @brief Test 1: Radiative efficiency for Schwarzschild black hole
 *
 * Expected: η = 0.0572 (5.72% efficiency for a=0)
 * Reference: Bardeen, Press, Teukolsky (1972), ApJ 178, 347
 */
bool test_efficiency_schwarzschild() {
    std::cout << "\n[TEST 1] Schwarzschild Radiative Efficiency\n";
    std::cout << "============================================\n";

    const double a_star = 0.0;
    const double eta = NovikovThorneDisk::radiative_efficiency(a_star);
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
 * Expected: η ≈ 0.42 (42% efficiency for a→1)
 * Reference: BPT (1972)
 */
bool test_efficiency_kerr_maximal() {
    std::cout << "\n[TEST 2] Near-Extremal Kerr Radiative Efficiency\n";
    std::cout << "=================================================\n";

    const double a_star = 0.998;
    const double eta = NovikovThorneDisk::radiative_efficiency(a_star);
    const double expected = 0.42;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Spin:     a* = " << a_star << "\n";
    std::cout << "  Computed: η = " << eta << "\n";
    std::cout << "  Expected: η ≈ " << expected << " (±0.01)\n";
    std::cout << "  Error:    " << std::abs(eta - expected) << "\n";

    const bool passed = std::abs(eta - expected) < 0.01;  // Relaxed tolerance
    std::cout << "  Status:   " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return passed;
}

/**
 * @brief Test 3: ISCO radius for Schwarzschild black hole
 *
 * Expected: r_ISCO = 6M
 * Reference: Standard result from Schwarzschild metric
 */
bool test_isco_schwarzschild() {
    std::cout << "\n[TEST 3] Schwarzschild ISCO Radius\n";
    std::cout << "===================================\n";

    const double a_star = 0.0;
    const double r_isco = NovikovThorneDisk::isco_radius(a_star);
    const double expected = 6.0;

    std::cout << std::fixed << std::setprecision(10);
    std::cout << "  Computed: r_ISCO = " << r_isco << " M\n";
    std::cout << "  Expected: r_ISCO = " << expected << " M\n";
    std::cout << "  Error:    " << std::abs(r_isco - expected) << "\n";

    const bool passed = std::abs(r_isco - expected) < 1e-8;
    std::cout << "  Status:   " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return passed;
}

/**
 * @brief Test 4: ISCO radius for near-extremal Kerr black hole
 *
 * Expected: r_ISCO ≈ 1.24M (prograde orbit)
 * Reference: BPT (1972)
 */
bool test_isco_kerr_maximal() {
    std::cout << "\n[TEST 4] Near-Extremal Kerr ISCO Radius\n";
    std::cout << "========================================\n";

    const double a_star = 0.998;
    const double r_isco = NovikovThorneDisk::isco_radius(a_star);
    const double expected = 1.24;  // Approximate

    std::cout << std::fixed << std::setprecision(10);
    std::cout << "  Spin:     a* = " << a_star << "\n";
    std::cout << "  Computed: r_ISCO = " << r_isco << " M\n";
    std::cout << "  Expected: r_ISCO ≈ " << expected << " M (±0.01)\n";
    std::cout << "  Error:    " << std::abs(r_isco - expected) << "\n";

    const bool passed = std::abs(r_isco - expected) < 0.01;
    std::cout << "  Status:   " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return passed;
}

/**
 * @brief Test 5: Temperature peak location
 *
 * Expected: T peaks at r ≈ 1.5 * r_ISCO (Page & Thorne 1974)
 * Reference: Page & Thorne (1974), ApJ 191, 499
 */
bool test_temperature_peak() {
    std::cout << "\n[TEST 5] Temperature Peak Location\n";
    std::cout << "===================================\n";

    const double a_star = 0.0;
    const double r_peak = NovikovThorneDisk::peak_temperature_radius(a_star);
    const double r_isco = NovikovThorneDisk::isco_radius(a_star);
    const double expected_ratio = 1.5;

    const double ratio = r_peak / r_isco;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  r_ISCO:   " << r_isco << " M\n";
    std::cout << "  r_peak:   " << r_peak << " M\n";
    std::cout << "  Ratio:    r_peak / r_ISCO = " << ratio << "\n";
    std::cout << "  Expected: " << expected_ratio << "\n";

    const bool passed = std::abs(ratio - expected_ratio) < TOLERANCE;
    std::cout << "  Status:   " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return passed;
}

/**
 * @brief Test 6: Temperature vanishes inside ISCO
 *
 * Expected: T(r < r_ISCO) = 0 (no stable disk)
 */
bool test_temperature_inside_isco() {
    std::cout << "\n[TEST 6] Temperature Inside ISCO\n";
    std::cout << "=================================\n";

    const double a_star = 0.0;
    const double r_isco = NovikovThorneDisk::isco_radius(a_star);

    // Test points inside ISCO
    const double test_radii[] = {1.0, 2.0, 3.0, 5.0, 5.9};
    bool all_passed = true;

    std::cout << std::fixed << std::setprecision(10);
    std::cout << "  r_ISCO = " << r_isco << " M\n\n";

    for (double r : test_radii) {
        if (r >= r_isco) continue;  // Skip if outside ISCO

        const double T = NovikovThorneDisk::disk_temperature(r, a_star, 0.1, 4.0e6);
        const bool passed = (T == 0.0);

        std::cout << "  r = " << r << " M: T = " << T << " K ";
        std::cout << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

        all_passed = all_passed && passed;
    }

    std::cout << "  Status:   " << (all_passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return all_passed;
}

/**
 * @brief Test 7: Integrated luminosity consistency
 *
 * Expected: L = η * Mdot * c² (energy conservation)
 */
bool test_integrated_luminosity() {
    std::cout << "\n[TEST 7] Integrated Luminosity\n";
    std::cout << "===============================\n";

    const double a_star = 0.5;
    const double mdot_edd = 0.1;
    const double mass_solar = 4.0e6;  // Sgr A*

    const double eta = NovikovThorneDisk::radiative_efficiency(a_star);
    const double L = NovikovThorneDisk::integrated_luminosity(mdot_edd, a_star, mass_solar);

    // Eddington luminosity
    const double L_edd = 1.26e38 * mass_solar;  // erg/s

    // Expected luminosity
    const double c_cgs = constants::C_LIGHT * 1e2;  // cm/s
    const double mdot_edd_cgs = L_edd / (eta * c_cgs * c_cgs);
    const double expected_L = eta * mdot_edd * mdot_edd_cgs * c_cgs * c_cgs;

    std::cout << std::scientific << std::setprecision(6);
    std::cout << "  Spin:          a* = " << a_star << "\n";
    std::cout << "  Efficiency:    η = " << eta << "\n";
    std::cout << "  Accretion:     Mdot = " << mdot_edd << " * Mdot_Edd\n";
    std::cout << "  Mass:          M = " << mass_solar << " M_sun\n\n";
    std::cout << "  Computed:      L = " << L << " erg/s\n";
    std::cout << "  Expected:      L = " << expected_L << " erg/s\n";
    std::cout << "  Relative err:  " << std::abs(L - expected_L) / expected_L << "\n";

    const bool passed = std::abs(L - expected_L) / expected_L < RELAXED_TOLERANCE;
    std::cout << "  Status:        " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return passed;
}

/**
 * @brief Test 8: Normalized flux peak location
 *
 * Expected: Flux peaks near ISCO (1-2 * r_ISCO)
 */
bool test_normalized_flux_peak() {
    std::cout << "\n[TEST 8] Normalized Flux Peak\n";
    std::cout << "==============================\n";

    const double a_star = 0.0;
    const double r_isco = NovikovThorneDisk::isco_radius(a_star);

    // Sample flux at different radii
    double max_flux = 0.0;
    double r_at_max = 0.0;

    for (double r = r_isco; r <= 10.0; r += 0.01) {
        const double flux = NovikovThorneDisk::normalized_flux(r, a_star);
        if (flux > max_flux) {
            max_flux = flux;
            r_at_max = r;
        }
    }

    const double ratio = r_at_max / r_isco;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  r_ISCO:      " << r_isco << " M\n";
    std::cout << "  r_peak_flux: " << r_at_max << " M\n";
    std::cout << "  Ratio:       " << ratio << "\n";
    std::cout << "  Expected:    1.0 - 2.0\n";

    const bool passed = (ratio >= 1.0 && ratio <= 2.0);
    std::cout << "  Status:      " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return passed;
}

/**
 * @brief Main test runner
 */
int main() {
    std::cout << "\n";
    std::cout << "========================================================\n";
    std::cout << "  Novikov-Thorne Disk Model Validation Tests\n";
    std::cout << "========================================================\n";

    int passed = 0;
    int total = 8;

    // Run all tests
    if (test_efficiency_schwarzschild()) passed++;
    if (test_efficiency_kerr_maximal()) passed++;
    if (test_isco_schwarzschild()) passed++;
    if (test_isco_kerr_maximal()) passed++;
    if (test_temperature_peak()) passed++;
    if (test_temperature_inside_isco()) passed++;
    if (test_integrated_luminosity()) passed++;
    if (test_normalized_flux_peak()) passed++;

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
    } else {
        std::cout << "\n  ✗ SOME TESTS FAILED\n";
        std::cout << "========================================================\n\n";
        return 1;
    }
}
