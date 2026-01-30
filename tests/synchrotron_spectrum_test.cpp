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

#include "../src/physics/synchrotron.h"
#include "../src/physics/constants.h"
#include <iostream>
#include <cmath>
#include <iomanip>
#include <cassert>
#include <vector>

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
bool test_synchrotron_f_low_freq() {
    std::cout << "\n[TEST 1] Synchrotron F(x) - Low Frequency Regime\n";
    std::cout << "=================================================\n";

    std::vector<double> test_vals = {1e-4, 1e-3, 5e-3};
    bool all_passed = true;

    for (double x : test_vals) {
        double F_x = synchrotron_F(x);
        double expected = 1.8084 * std::pow(x, 1.0/3.0);
        double error = std::abs(F_x - expected) / expected;

        std::cout << std::fixed << std::setprecision(8);
        std::cout << "  x = " << x << "\n";
        std::cout << "    F(x) computed: " << F_x << "\n";
        std::cout << "    F(x) expected: " << expected << "\n";
        std::cout << "    Relative err:  " << error << "\n";

        bool passed = error < TOLERANCE;  // Strict tolerance in pure low-freq regime
        std::cout << "    Status:        " << (passed ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && passed;
    }

    return all_passed;
}

/**
 * @brief Test 2: Synchrotron function F(x) - High frequency regime
 *
 * For x >> 1, F(x) ~= sqrt(pi/2) * sqrt(x) * exp(-x)
 * Note: Only test x >> 10 to avoid transition boundary
 */
bool test_synchrotron_f_high_freq() {
    std::cout << "\n[TEST 2] Synchrotron F(x) - High Frequency Regime\n";
    std::cout << "==================================================\n";

    std::vector<double> test_vals = {20.0, 50.0, 100.0};
    bool all_passed = true;

    for (double x : test_vals) {
        double F_x = synchrotron_F(x);
        double expected = std::sqrt(M_PI / 2.0) * std::sqrt(x) * std::exp(-x);
        double error = std::abs(F_x - expected) / expected;

        std::cout << std::fixed << std::setprecision(8);
        std::cout << "  x = " << x << "\n";
        std::cout << "    F(x) computed: " << F_x << "\n";
        std::cout << "    F(x) expected: " << expected << "\n";
        std::cout << "    Relative err:  " << error << "\n";

        bool passed = error < TOLERANCE;  // Strict tolerance in pure high-freq regime
        std::cout << "    Status:        " << (passed ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && passed;
    }

    return all_passed;
}

/**
 * @brief Test 3: Synchrotron function G(x) - Polarization degree
 *
 * G(x) represents circular polarization: Pol = G(x) / F(x)
 * Expected: G(x) < F(x) for all x (linear polarization always < 1)
 */
bool test_synchrotron_g_polarization() {
    std::cout << "\n[TEST 3] Synchrotron G(x) - Polarization Degree\n";
    std::cout << "================================================\n";

    std::vector<double> test_vals = {1e-3, 0.1, 1.0, 10.0, 100.0};
    bool all_passed = true;

    for (double x : test_vals) {
        double F_x = synchrotron_F(x);
        double G_x = synchrotron_G(x);
        double pol = G_x / F_x;

        std::cout << std::fixed << std::setprecision(8);
        std::cout << "  x = " << x << "\n";
        std::cout << "    F(x) = " << F_x << "\n";
        std::cout << "    G(x) = " << G_x << "\n";
        std::cout << "    Pol  = " << pol << "\n";

        // Polarization degree must be between 0 and 1
        bool passed = (pol >= 0.0 && pol <= 1.0);
        std::cout << "    Status: " << (passed ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && passed;
    }

    return all_passed;
}

/**
 * @brief Test 4: Power-law spectrum shape
 *
 * For power-law electron distribution N(gamma) ~ gamma^(-p):
 * F_nu ~ nu^(-(p-1)/2) in optically thin regime
 * Expected: spectral index alpha = -(p-1)/2
 */
bool test_power_law_spectrum() {
    std::cout << "\n[TEST 4] Power-Law Spectrum Shape\n";
    std::cout << "==================================\n";

    double B = 100.0;  // Gauss (typical AGN jet)
    double gamma_min = 1.0;
    double gamma_max = 1e6;
    double p = 2.5;    // Typical jet power-law index

    // Compute spectrum at three frequencies
    double nu1 = synchrotron_frequency_critical(gamma_min, B) * 10.0;
    double nu2 = nu1 * 100.0;
    double nu3 = nu2 * 100.0;

    double F1 = synchrotron_spectrum_power_law(nu1, B, gamma_min, gamma_max, p);
    double F2 = synchrotron_spectrum_power_law(nu2, B, gamma_min, gamma_max, p);
    double F3 = synchrotron_spectrum_power_law(nu3, B, gamma_min, gamma_max, p);

    // Compute spectral indices from ratios
    double alpha_12 = std::log(F1 / F2) / std::log(nu1 / nu2);
    double alpha_23 = std::log(F2 / F3) / std::log(nu2 / nu3);
    double expected_alpha = -(p - 1.0) / 2.0;

    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Power-law index: p = " << p << "\n";
    std::cout << "  Expected spectral index: alpha = " << expected_alpha << "\n";
    std::cout << "  Computed alpha (nu1-nu2): " << alpha_12 << "\n";
    std::cout << "  Computed alpha (nu2-nu3): " << alpha_23 << "\n";
    std::cout << "  Error: " << std::abs(alpha_12 - expected_alpha) << "\n";

    bool passed = (std::abs(alpha_12 - expected_alpha) < RELAXED_TOLERANCE &&
                   std::abs(alpha_23 - expected_alpha) < RELAXED_TOLERANCE);
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
bool test_self_absorption_transition() {
    std::cout << "\n[TEST 5] Self-Absorption Transition\n";
    std::cout << "====================================\n";

    double B = 100.0;
    double gamma_min = 10.0;
    double p = 2.5;
    double n_e = 1e3;   // Electron density [cm^-3]
    double R = 1e16;    // Source size [cm]

    double nu_a = synchrotron_self_absorption_frequency(B, n_e, R, p);
    double nu_min = synchrotron_frequency_critical(gamma_min, B);

    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  nu_min (critical freq): " << nu_min << " Hz\n";
    std::cout << "  nu_a (absorption freq): " << nu_a << " Hz\n";
    std::cout << "  Ratio nu_a / nu_min: " << (nu_a / nu_min) << "\n";

    // Self-absorption frequency should be < critical frequency
    bool passed = (nu_a > 0.0 && nu_a < nu_min);
    std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";

    return passed;
}

/**
 * @brief Test 6: Absorption coefficient frequency dependence
 *
 * For power-law electrons: alpha_nu ~ nu^(-(p+4)/2)
 * Expected: steep frequency dependence, strong suppression at high freq
 */
bool test_absorption_coefficient() {
    std::cout << "\n[TEST 6] Absorption Coefficient Frequency Dependence\n";
    std::cout << "======================================================\n";

    double B = 100.0;
    double n_e = 1e3;  // cm^-3 (typical AGN)
    double p = 2.5;

    double nu1 = 1e9;   // 1 GHz
    double nu2 = 1e10;  // 10 GHz (10x higher)
    double nu3 = 1e11;  // 100 GHz (100x higher)

    double alpha1 = synchrotron_absorption_coefficient(nu1, B, n_e, p);
    double alpha2 = synchrotron_absorption_coefficient(nu2, B, n_e, p);
    double alpha3 = synchrotron_absorption_coefficient(nu3, B, n_e, p);

    // Compute frequency dependence exponent
    double exp_12 = std::log(alpha1 / alpha2) / std::log(nu1 / nu2);
    double exp_23 = std::log(alpha2 / alpha3) / std::log(nu2 / nu3);
    double expected_exp = -(p + 4.0) / 2.0;

    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Expected exponent: " << expected_exp << "\n";
    std::cout << "  Computed exponent (nu1-nu2): " << exp_12 << "\n";
    std::cout << "  Computed exponent (nu2-nu3): " << exp_23 << "\n";
    std::cout << "  Error: " << std::abs(exp_12 - expected_exp) << "\n";

    bool passed = (std::abs(exp_12 - expected_exp) < RELAXED_TOLERANCE &&
                   std::abs(exp_23 - expected_exp) < RELAXED_TOLERANCE);
    std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";

    return passed;
}

/**
 * @brief Test 7: Spectral index calculation
 *
 * Spectral index α = -(p - 1)/2 and inverse: p = 1 - 2α
 * For typical jets p=2-3, giving α = -0.5 to -1.0
 */
bool test_spectral_index_calculation() {
    std::cout << "\n[TEST 7] Spectral Index Calculation\n";
    std::cout << "====================================\n";

    std::vector<double> p_values = {2.0, 2.5, 3.0, 3.5};
    bool all_passed = true;

    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Testing spectral index: alpha = -(p-1)/2\n\n";

    for (double p : p_values) {
        double alpha = synchrotron_spectral_index(p);
        double expected_alpha = -(p - 1.0) / 2.0;
        double p_back = electron_index_from_spectral(alpha);

        std::cout << "  p = " << p << "\n";
        std::cout << "    alpha = " << alpha << " (expected " << expected_alpha << ")\n";
        std::cout << "    p (from alpha) = " << p_back << " (expected " << p << ")\n";

        bool passed = (std::abs(alpha - expected_alpha) < TOLERANCE &&
                       std::abs(p_back - p) < TOLERANCE);
        std::cout << "    Status: " << (passed ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && passed;
    }

    return all_passed;
}

/**
 * @brief Test 8: Polarization degree bounds
 *
 * Verify pol = G(x)/F(x) stays in [0, 1] range
 * Note: Theory gives Pol_max = (p+1)/(p+7/3) for certain regimes
 * but computed max depends on approximation accuracy
 */
bool test_polarization_bounds() {
    std::cout << "\n[TEST 8] Polarization Degree Bounds\n";
    std::cout << "====================================\n";

    std::vector<double> test_x = {1e-3, 0.01, 0.1, 1.0, 5.0, 10.0, 50.0, 100.0};
    bool all_passed = true;

    std::cout << std::fixed << std::setprecision(6);

    for (double x : test_x) {
        double F_val = synchrotron_F(x);
        double G_val = synchrotron_G(x);
        double pol = (F_val > 1e-30) ? (G_val / F_val) : 0.0;

        // Polarization must be in [0, 1]
        bool passed = (pol >= 0.0 && pol <= 1.0);

        std::cout << "  x = " << x << ": Pol = " << pol;
        std::cout << " " << (passed ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && passed;
    }

    std::cout << "  Status: " << (all_passed ? "PASS" : "FAIL") << "\n";

    return all_passed;
}

/**
 * @brief Main test driver
 */
int main() {
    std::cout << "\n"
              << "====================================================\n"
              << "SYNCHROTRON SPECTRUM VALIDATION TEST SUITE\n"
              << "Rybicki & Lightman (1979) Radiative Processes\n"
              << "====================================================\n";

    int passed = 0;
    int total = 8;

    if (test_synchrotron_f_low_freq())      passed++;
    if (test_synchrotron_f_high_freq())     passed++;
    if (test_synchrotron_g_polarization())  passed++;
    if (test_power_law_spectrum())          passed++;
    if (test_self_absorption_transition())  passed++;
    if (test_absorption_coefficient())      passed++;
    if (test_spectral_index_calculation())  passed++;
    if (test_polarization_bounds())         passed++;

    std::cout << "\n"
              << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n";

    return (passed == total) ? 0 : 1;
}
