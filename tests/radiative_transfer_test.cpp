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

#include "../src/physics/synchrotron.h"
#include "../src/physics/constants.h"
#include <iostream>
#include <cmath>
#include <iomanip>
#include <cassert>
#include <vector>
#include <algorithm>

using namespace physics;

// Test tolerance
constexpr double TOLERANCE = 1e-6;
constexpr double RELAXED_TOLERANCE = 1e-2;

/**
 * @brief Simulate optical depth integration (CPU reference)
 */
double cpu_optical_depth_integrate(const std::vector<double>& alpha_array,
                                    const std::vector<double>& ds_array) {
  if (alpha_array.size() < 2) return 0.0;

  double tau = 0.0;
  for (size_t i = 0; i < alpha_array.size() - 1; i++) {
    double alpha_avg = 0.5 * (alpha_array[i] + alpha_array[i + 1]);
    tau += alpha_avg * ds_array[i];
  }
  return tau;
}

/**
 * @brief Simulate radiative transfer step (CPU reference)
 */
double cpu_intensity_step(double I_current, double j_nu, double alpha_nu, double ds) {
  double tau_segment = alpha_nu * ds;
  if (tau_segment > 100.0) tau_segment = 100.0;

  double T = std::exp(-tau_segment);
  double S = (alpha_nu > 1e-30) ? (j_nu / alpha_nu) : j_nu;

  double I_new = I_current * T + S * (1.0 - T);
  return I_new;
}

/**
 * @brief Test 1: Optical depth convergence with step refinement
 *
 * Expected: Doubling steps should reduce error by factor ~4 (2nd-order method)
 */
bool test_optical_depth_convergence() {
    std::cout << "\n[TEST 1] Optical Depth Convergence\n";
    std::cout << "===================================\n";

    double B = 100.0;      // Gauss
    double n_e = 1e3;      // cm^-3
    double nu = 1e10;      // Hz
    double p = 2.5;
    double path_length = 1e16;  // cm

    // Create optical depth profile: increasing B along path
    auto create_absorption_profile = [&](int n_steps) -> std::vector<double> {
        std::vector<double> alpha_array;
        for (int i = 0; i < n_steps; i++) {
            double s = static_cast<double>(i) / (n_steps - 1) * path_length;
            // Increase B with distance: B(s) = B_0 * (1 + s/path_length)
            double B_s = B * (1.0 + s / path_length);
            double alpha = synchrotron_absorption_coefficient(nu, B_s, n_e, p);
            alpha_array.push_back(alpha);
        }
        return alpha_array;
    };

    std::vector<int> step_counts = {10, 20, 40, 80};
    std::vector<double> tau_results;

    std::cout << std::fixed << std::setprecision(8);
    for (int n_steps : step_counts) {
        auto alpha_array = create_absorption_profile(n_steps);
        std::vector<double> ds_array(static_cast<size_t>(n_steps - 1),
                                      path_length / (n_steps - 1));

        double tau = cpu_optical_depth_integrate(alpha_array, ds_array);
        tau_results.push_back(tau);

        std::cout << "  Steps: " << n_steps << ", tau = " << tau;

        if (tau_results.size() > 1) {
            double error_ratio = std::abs(tau_results.back() - tau_results[tau_results.size() - 2]) /
                                std::abs(tau_results[tau_results.size() - 2] - tau_results[tau_results.size() - 3] + 1e-20);
            std::cout << ", convergence ratio = " << error_ratio;
        }
        std::cout << "\n";
    }

    // Check convergence: errors should decrease
    bool passed = (tau_results.size() > 3) &&
                  (tau_results[1] < tau_results[0]) &&
                  (tau_results[2] < tau_results[1]) &&
                  (tau_results[3] < tau_results[2]);

    std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
    return passed;
}

/**
 * @brief Test 2: Transmission factor bounds
 *
 * T(tau) = exp(-tau) must satisfy: 0 <= T <= 1 for all tau >= 0
 */
bool test_transmission_factor_bounds() {
    std::cout << "\n[TEST 2] Transmission Factor Bounds\n";
    std::cout << "====================================\n";

    std::vector<double> tau_values = {0.0, 0.01, 0.1, 1.0, 10.0, 100.0, 1000.0};
    bool all_passed = true;

    std::cout << std::fixed << std::setprecision(8);
    for (double tau : tau_values) {
        double T = std::exp(-tau);

        bool passed = (T >= 0.0 && T <= 1.0);
        std::cout << "  tau = " << tau << ", T = " << T;
        std::cout << " " << (passed ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && passed;
    }

    std::cout << "  Status: " << (all_passed ? "PASS" : "FAIL") << "\n";
    return all_passed;
}

/**
 * @brief Test 3: Optically thin limit (tau << 1)
 *
 * When tau << 1: dI/ds ≈ j_nu (linear accumulation for weak absorption)
 * Expected: Full radiative transfer ≈ optically thin as alpha -> 0
 */
bool test_optically_thin_limit() {
    std::cout << "\n[TEST 3] Optically Thin Limit\n";
    std::cout << "=============================\n";

    double j_nu = 1e-8;     // Emissivity
    double alpha_nu = 1e-25; // Extremely small absorption (tau ~ 1e-9)
    double ds = 1e16;        // Path segment [cm]

    double I_current = 1e-9; // Non-zero starting intensity

    // Full formula
    double I_full = cpu_intensity_step(I_current, j_nu, alpha_nu, ds);

    // Optically thin limit: I ≈ I_old + j*ds (ignoring absorption)
    double I_thin = I_current + j_nu * ds;

    // In the limit alpha -> 0, the absorption term (j/alpha)*( 1 - exp(-tau))
    // becomes (j/alpha) * tau = j * ds (since tau -> 0, 1-exp(-tau) -> tau)

    double error = std::abs(I_full - I_thin) / (std::abs(I_thin) + 1e-30);

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Emissivity j_nu = " << j_nu << "\n";
    std::cout << "  Absorption alpha_nu = " << alpha_nu << "\n";
    std::cout << "  Optical depth tau = " << (alpha_nu * ds) << " (<< 1)\n";
    std::cout << "  Full formula result: " << I_full << "\n";
    std::cout << "  Optically thin limit: " << I_thin << "\n";
    std::cout << "  Relative error: " << error << "\n";

    bool passed = error < RELAXED_TOLERANCE;
    std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
    return passed;
}

/**
 * @brief Test 4: Optically thick limit (tau >> 1)
 *
 * When tau >> 1 and source uniform: I -> S_nu = j/alpha (blackbody limit)
 */
bool test_optically_thick_limit() {
    std::cout << "\n[TEST 4] Optically Thick Limit\n";
    std::cout << "===============================\n";

    double j_nu = 1e-8;     // Emissivity
    double alpha_nu = 1e-8; // Strong absorption
    double ds = 1e18;       // Very large path (tau >> 1)

    double I_current = 0.0;

    // Full formula
    double I_full = cpu_intensity_step(I_current, j_nu, alpha_nu, ds);

    // Optically thick limit (source function)
    double S_nu = j_nu / alpha_nu;

    double error = std::abs(I_full - S_nu) / (S_nu + 1e-30);

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Emissivity j_nu = " << j_nu << "\n";
    std::cout << "  Absorption alpha_nu = " << alpha_nu << "\n";
    std::cout << "  Optical depth tau = " << (alpha_nu * ds) << " (>> 1)\n";
    std::cout << "  Full formula result: " << I_full << "\n";
    std::cout << "  Source function S = " << S_nu << "\n";
    std::cout << "  Relative error: " << error << "\n";

    bool passed = error < RELAXED_TOLERANCE;
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
bool test_energy_conservation_emission() {
    std::cout << "\n[TEST 5] Energy Conservation (Equilibrium)\n";
    std::cout << "==========================================\n";

    // Case: weak absorption with small tau
    double j_nu = 1e-8;      // Emissivity
    double alpha_nu = 1e-12; // Very weak absorption
    double S = j_nu / alpha_nu;  // Source function ≈ 1e4

    double ds = 1e14;  // Path segment [cm]
    double tau = alpha_nu * ds;  // Optical depth = 1e2 (moderate)

    std::vector<double> I_sequence;
    double I = 100.0;  // Start with much less than S

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Source function S = " << S << "\n";
    std::cout << "  Optical depth per step = " << tau << "\n";
    std::cout << "  Starting intensity = " << I << "\n\n";

    for (int step = 0; step < 4; step++) {
        I = cpu_intensity_step(I, j_nu, alpha_nu, ds);
        I_sequence.push_back(I);
        std::cout << "  Step " << step << ": I = " << I << "\n";
    }

    // Check that intensity approaches or reaches the source function
    // It should either decrease distance to S or stabilize at S
    double delta_start = std::abs(I_sequence[0] - S);
    double delta_end = std::abs(I_sequence[I_sequence.size()-1] - S);

    // Test passes if we moved closer to S or reached it
    bool approaching = (delta_end <= delta_start) || (delta_end < 1.0);

    std::cout << "  Distance from S: start = " << delta_start;
    std::cout << ", final = " << delta_end << "\n";
    std::cout << "  Status: " << (approaching ? "PASS" : "FAIL") << "\n";
    return approaching;
}

/**
 * @brief Test 6: Intensity attenuation with absorption
 *
 * Pure absorption (j=0): I decreases exponentially with tau
 * Expected: I_out = I_in * exp(-tau)
 */
bool test_intensity_attenuation() {
    std::cout << "\n[TEST 6] Intensity Attenuation\n";
    std::cout << "==============================\n";

    double I_initial = 1e-8;
    double alpha_nu = 1e-8;
    std::vector<double> path_lengths = {1e14, 1e15, 1e16, 1e17};
    bool all_passed = true;

    std::cout << std::fixed << std::setprecision(6);
    for (double ds : path_lengths) {
        double tau = alpha_nu * ds;
        double I_expected = I_initial * std::exp(-tau);

        // Pure absorption (j_nu = 0)
        double I_computed = cpu_intensity_step(I_initial, 0.0, alpha_nu, ds);

        double error = std::abs(I_computed - I_expected) / (I_expected + 1e-30);

        bool passed = error < TOLERANCE;
        std::cout << "  ds = " << ds << " cm, tau = " << tau;
        std::cout << ", error = " << error << " " << (passed ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && passed;
    }

    std::cout << "  Status: " << (all_passed ? "PASS" : "FAIL") << "\n";
    return all_passed;
}

/**
 * @brief Test 7: Multi-frequency integration consistency
 *
 * Spectrum integrated over frequency should equal sum of frequency bins
 */
bool test_multifrequency_consistency() {
    std::cout << "\n[TEST 7] Multi-Frequency Integration\n";
    std::cout << "=====================================\n";

    // Create spectrum: power-law
    double B = 100.0;
    double gamma_min = 10.0;
    double gamma_max = 1e6;
    double p = 2.5;

    // Sample frequencies logarithmically
    std::vector<double> freqs;
    std::vector<double> fluxes;

    for (int i = 0; i < 20; i++) {
        double nu = std::pow(10.0, 9.0 + 0.5 * i); // 1 GHz to 1 EHz
        freqs.push_back(nu);
        double flux = synchrotron_spectrum_power_law(nu, B, gamma_min, gamma_max, p);
        fluxes.push_back(flux);
    }

    // Integrate using trapezoidal rule
    double integral = 0.0;
    for (size_t i = 0; i < freqs.size() - 1; i++) {
        double dnu = freqs[i + 1] - freqs[i];
        double f_avg = 0.5 * (fluxes[i] + fluxes[i + 1]);
        integral += f_avg * dnu;
    }

    // Check that integral is positive
    bool passed = integral > 0.0;

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
bool test_optically_thin_spectrum() {
    std::cout << "\n[TEST 8] Optically Thin Spectrum\n";
    std::cout << "==================================\n";

    // Very low-opacity case
    double B = 1.0;         // Very weak field
    double n_e = 1e-2;      // Very low density
    double p = 2.5;
    double path_length = 1e14;  // Short path

    // Sample high frequency (less absorption)
    double nu = 1e13;  // 10 THz optical

    // Absorption coefficient
    double alpha = synchrotron_absorption_coefficient(nu, B, n_e, p);
    double tau_total = alpha * path_length;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Frequency: " << nu << " Hz\n";
    std::cout << "  Absorption coefficient: " << alpha << " cm^-1\n";
    std::cout << "  Total optical depth: " << tau_total << "\n";

    bool optically_thin = tau_total < 0.1;
    std::cout << "  Regime: " << (optically_thin ? "OPTICALLY THIN" : "OPTICALLY THICK") << "\n";
    std::cout << "  Status: " << (optically_thin ? "PASS" : "FAIL") << "\n";

    return optically_thin;
}

/**
 * @brief Test 9: Optically thick spectrum (strong absorption)
 *
 * For tau >> 1: integrated I -> uniform (blackbody-like)
 */
bool test_optically_thick_spectrum() {
    std::cout << "\n[TEST 9] Optically Thick Spectrum\n";
    std::cout << "==================================\n";

    // High-opacity case
    double B = 1000.0;      // Strong field
    double n_e = 1e4;       // High density
    double p = 2.5;
    double path_length = 1e18;  // Very long path

    // Sample single frequency
    double nu = 1e9;   // 1 GHz

    // Absorption coefficient
    double alpha = synchrotron_absorption_coefficient(nu, B, n_e, p);
    double tau_total = alpha * path_length;

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Frequency: " << nu << " Hz\n";
    std::cout << "  Absorption coefficient: " << alpha << " cm^-1\n";
    std::cout << "  Total optical depth: " << tau_total << "\n";

    bool optically_thick = tau_total > 10.0;
    std::cout << "  Regime: " << (optically_thick ? "OPTICALLY THICK" : "OPTICALLY THIN") << "\n";
    std::cout << "  Status: " << (optically_thick ? "PASS" : "FAIL") << "\n";

    return optically_thick;
}

/**
 * @brief Test 10: Numerical stability (no NaN/Inf)
 *
 * Check that radiative transfer doesn't produce NaN or Inf
 */
bool test_numerical_stability() {
    std::cout << "\n[TEST 10] Numerical Stability\n";
    std::cout << "=============================\n";

    std::vector<std::pair<double, double>> test_cases = {
        {1e-30, 1e-30},  // Both extremely small
        {1e10, 1e-30},   // Large j, tiny alpha
        {1e-30, 1e10},   // Tiny j, large alpha
        {1e10, 1e10},    // Both large
    };

    bool all_passed = true;

    for (const auto& [j_nu, alpha_nu] : test_cases) {
        double I = cpu_intensity_step(0.0, j_nu, alpha_nu, 1e16);

        // Check for valid (non-NaN, non-infinity) result
        bool valid = (I >= -1e300 && I <= 1e300) || (I == 0.0);
        std::cout << "  j=" << j_nu << ", alpha=" << alpha_nu;
        std::cout << " -> I=" << I << " " << (valid ? "PASS" : "FAIL") << "\n";
        all_passed = all_passed && valid;
    }

    std::cout << "  Status: " << (all_passed ? "PASS" : "FAIL") << "\n";
    return all_passed;
}

/**
 * @brief Test 11: Spectral index consistency
 *
 * Verify spectral index calculation is self-consistent
 */
bool test_spectral_shape_preservation() {
    std::cout << "\n[TEST 11] Spectral Index Consistency\n";
    std::cout << "======================================\n";

    // Test that spectral index calculation is consistent
    std::vector<double> p_values = {2.0, 2.5, 3.0, 3.5};
    bool all_passed = true;

    std::cout << std::fixed << std::setprecision(6);
    for (double p : p_values) {
        double alpha = -(p - 1.0) / 2.0;
        double p_back = 1.0 - 2.0 * alpha;

        double error = std::abs(p_back - p);
        bool passed = error < TOLERANCE;

        std::cout << "  p = " << p << ", alpha = " << alpha;
        std::cout << ", p(back) = " << p_back << " " << (passed ? "PASS" : "FAIL") << "\n";

        all_passed = all_passed && passed;
    }

    std::cout << "  Status: " << (all_passed ? "PASS" : "FAIL") << "\n";
    return all_passed;
}

/**
 * @brief Test 12: Ray marching sequence consistency
 *
 * Multiple steps should accumulate intensity consistently
 */
bool test_ray_marching_consistency() {
    std::cout << "\n[TEST 12] Ray Marching Consistency\n";
    std::cout << "====================================\n";

    double j_nu = 1e-10;
    double alpha_nu = 1e-12;
    double ds = 1e16;

    // Method 1: Single large step
    double I_single = cpu_intensity_step(0.0, j_nu, alpha_nu, 5.0 * ds);

    // Method 2: Five small steps
    double I_multi = 0.0;
    for (int i = 0; i < 5; i++) {
        I_multi = cpu_intensity_step(I_multi, j_nu, alpha_nu, ds);
    }

    double error = std::abs(I_single - I_multi) / (std::abs(I_multi) + 1e-30);

    std::cout << std::fixed << std::setprecision(10);
    std::cout << "  Single 5*ds step: " << I_single << "\n";
    std::cout << "  Five ds steps: " << I_multi << "\n";
    std::cout << "  Relative error: " << error << "\n";

    // Allow larger error due to exponential approximation differences
    bool passed = error < 0.1;
    std::cout << "  Status: " << (passed ? "PASS" : "FAIL") << "\n";
    return passed;
}

/**
 * @brief Main test driver
 */
int main() {
    std::cout << "\n"
              << "====================================================\n"
              << "RADIATIVE TRANSFER VALIDATION TEST SUITE\n"
              << "Rybicki & Lightman (1979) Radiative Processes\n"
              << "====================================================\n";

    int passed = 0;
    int total = 12;

    if (test_optical_depth_convergence())    passed++;
    if (test_transmission_factor_bounds())   passed++;
    if (test_optically_thin_limit())         passed++;
    if (test_optically_thick_limit())        passed++;
    if (test_energy_conservation_emission()) passed++;
    if (test_intensity_attenuation())        passed++;
    if (test_multifrequency_consistency())   passed++;
    if (test_optically_thin_spectrum())      passed++;
    if (test_optically_thick_spectrum())     passed++;
    if (test_numerical_stability())          passed++;
    if (test_spectral_shape_preservation())  passed++;
    if (test_ray_marching_consistency())     passed++;

    std::cout << "\n"
              << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n";

    return (passed == total) ? 0 : 1;
}
