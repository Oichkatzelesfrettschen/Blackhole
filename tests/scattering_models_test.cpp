/**
 * @file scattering_models_test.cpp
 * @brief Phase 7.1b: Scattering Models Validation
 *
 * Tests Thomson, Rayleigh, and Mie scattering across frequency range
 * and verifies albedo and asymmetry properties.
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

// Import scattering models from Phase 7.1b
#include "../src/physics/scattering_models.h"

using namespace physics;

// Test 1: Thomson cross-section constant at low frequencies
bool test_thomson_frequency_independence() {
    std::cout << "Test 1: Thomson Cross-Section Frequency Independence\n";

    // Test at radio and microwave frequencies where Thomson dominates
    std::vector<double> frequencies = {1e9, 1e10, 1e11, 1e12, 1e13};
    double sigma_T = thomson_cross_section();

    bool independent = true;
    double max_deviation = 0.0;
    std::cout << "  Low frequencies: ";
    for (double nu : frequencies) {
        // Thomson should be approximately constant at low frequencies
        double sigma_KN = thomson_cross_section_corrected(nu, 0.01);  // Cool plasma
        double deviation = std::abs(sigma_KN - sigma_T) / sigma_T;
        max_deviation = std::max(max_deviation, deviation);
        independent = independent && (deviation < 0.05);  // 5% tolerance

        std::cout << std::scientific << nu << "Hz:" << sigma_KN << " ";
    }

    std::cout << "\n  Thomson constant: " << std::scientific << sigma_T << "\n"
              << "  Max deviation: " << max_deviation << "\n"
              << "  Status: " << (independent ? "PASS" : "FAIL") << "\n\n";

    return independent;
}

// Test 2: Rayleigh scattering 1/nu^4 dependence
bool test_rayleigh_frequency_dependence() {
    std::cout << "Test 2: Rayleigh Scattering Frequency Dependence\n";

    double grain_radius = 0.1e-4;  // 0.1 micron
    double n_grain = 1.5;          // Refractive index

    // Test at three frequencies
    double nu_low = 1e10;   // 10 GHz
    double nu_mid = 1e14;   // Optical
    double nu_high = 1e18;  // X-ray

    double sigma_low = rayleigh_scattering(nu_low, grain_radius, n_grain);
    double sigma_mid = rayleigh_scattering(nu_mid, grain_radius, n_grain);
    double sigma_high = rayleigh_scattering(nu_high, grain_radius, n_grain);

    // Ratio should follow 1/nu^4
    // sigma(100*nu) ~ sigma(nu) / 100^4 = sigma(nu) / 10^8
    double ratio_1 = sigma_low / sigma_mid;
    double ratio_2 = sigma_mid / sigma_high;

    // Expected: (nu_low / nu_mid)^4 = (1e10 / 1e14)^4 = 1e-16
    // so ratio_1 ~ 1e-16
    bool freq_dep_ok = (ratio_1 > 1e-17 && ratio_1 < 1e-15) &&
                       (ratio_2 > 1e-17 && ratio_2 < 1e-15);

    std::cout << std::scientific;
    std::cout << "  Low freq (1e10 Hz): sigma = " << sigma_low << "\n"
              << "  Mid freq (1e14 Hz): sigma = " << sigma_mid << "\n"
              << "  High freq (1e18 Hz): sigma = " << sigma_high << "\n"
              << "  Ratio (low/mid): " << ratio_1 << " (expect ~1e-16)\n"
              << "  Ratio (mid/high): " << ratio_2 << " (expect ~1e-16)\n"
              << "  Status: " << (freq_dep_ok ? "PASS" : "FAIL") << "\n\n";

    return freq_dep_ok;
}

// Test 3: Mie scattering efficiency across size parameters
bool test_mie_scattering_efficiency() {
    std::cout << "Test 3: Mie Scattering Efficiency\n";

    double nu = 1e15;  // Optical frequency

    // Test at various grain sizes
    std::vector<double> radii = {
        1e-5,   // 0.01 micron (very small, Rayleigh limit)
        1e-4,   // 0.1 micron (Rayleigh transition)
        1e-3,   // 1 micron (Mie regime)
        1e-2,   // 10 micron (large, geometric limit)
    };

    std::vector<const char*> labels = {
        "Very small",
        "Small",
        "Medium",
        "Large",
    };

    std::cout << "  Grain Size      | Q_sca    | Regime\n";
    std::cout << "  ---------------|---------|---------\n";

    bool efficiency_ok = true;
    for (size_t i = 0; i < radii.size(); i++) {
        double Q = mie_scattering_efficiency(nu, radii[i]);
        std::cout << std::scientific << std::setprecision(2);
        std::cout << "  " << radii[i] << " cm | " << Q << " | " << labels[i] << "\n";

        efficiency_ok = efficiency_ok && (Q >= 0.0 && Q <= 4.5);
    }

    std::cout << "  Status: " << (efficiency_ok ? "PASS" : "FAIL") << "\n\n";

    return efficiency_ok;
}

// Test 4: Single-scattering albedo
bool test_single_scattering_albedo() {
    std::cout << "Test 4: Single-Scattering Albedo\n";

    // Test cases
    double sigma_sca_1 = 1e-20;  // Mostly scattering
    double sigma_abs_1 = 1e-22;

    double sigma_sca_2 = 1e-22;  // Mostly absorbing
    double sigma_abs_2 = 1e-20;

    double sigma_sca_3 = 1e-20;  // Equal scattering and absorption
    double sigma_abs_3 = 1e-20;

    double albedo_1 = single_scattering_albedo(sigma_sca_1, sigma_abs_1);
    double albedo_2 = single_scattering_albedo(sigma_sca_2, sigma_abs_2);
    double albedo_3 = single_scattering_albedo(sigma_sca_3, sigma_abs_3);

    bool albedo_ok = (albedo_1 > 0.98 && albedo_1 <= 1.0) &&  // Should scatter
                     (albedo_2 < 0.02 && albedo_2 >= 0.0) &&  // Should absorb
                     (albedo_3 > 0.49 && albedo_3 < 0.51);    // Should be ~0.5

    std::cout << "  Case 1 (scattering dominant): omega = " << albedo_1 << " (expect ~1.0)\n"
              << "  Case 2 (absorption dominant): omega = " << albedo_2 << " (expect ~0.0)\n"
              << "  Case 3 (equal): omega = " << albedo_3 << " (expect ~0.5)\n"
              << "  Status: " << (albedo_ok ? "PASS" : "FAIL") << "\n\n";

    return albedo_ok;
}

// Test 5: Asymmetry parameter ranges
bool test_asymmetry_parameter() {
    std::cout << "Test 5: Asymmetry Parameter\n";

    double nu = 1e15;  // Optical

    // Thomson scattering
    double g_thomson = asymmetry_parameter(0, nu);

    // Rayleigh scattering
    double g_rayleigh = asymmetry_parameter(1, nu);

    // Mie scattering (very small grain, Rayleigh-like)
    double g_mie_small = asymmetry_parameter(2, nu, 1e-7);

    // Mie scattering (large grain)
    double g_mie_large = asymmetry_parameter(2, nu, 1e-2);

    bool param_ok = (g_thomson > 0.1 && g_thomson < 0.3) &&    // Thomson forward-peaked
                    (std::abs(g_rayleigh) < 0.1) &&             // Rayleigh isotropic
                    (std::abs(g_mie_small) < 0.15) &&           // Very small Mie -> isotropic
                    (g_mie_large > 0.3 && g_mie_large < 0.99);  // Large Mie -> forward

    std::cout << "  Thomson (forward-peaked): g = " << g_thomson << " (expect 0.1-0.3)\n"
              << "  Rayleigh (isotropic): g = " << g_rayleigh << " (expect ~0)\n"
              << "  Mie very small (Rayleigh-like): g = " << g_mie_small << " (expect ~0)\n"
              << "  Mie large (forward): g = " << g_mie_large << " (expect 0.3-0.99)\n"
              << "  Status: " << (param_ok ? "PASS" : "FAIL") << "\n\n";

    return param_ok;
}

// Test 6: Thomson opacity scaling with density
bool test_thomson_opacity_scaling() {
    std::cout << "Test 6: Thomson Opacity Density Scaling\n";

    double n_e_low = 1e3;    // cm^-3
    double n_e_mid = 1e4;    // 10x higher
    double n_e_high = 1e5;   // 100x higher

    double kappa_low = thomson_opacity(n_e_low);
    double kappa_mid = thomson_opacity(n_e_mid);
    double kappa_high = thomson_opacity(n_e_high);

    // Opacity should scale linearly with density
    double ratio_1 = kappa_mid / kappa_low;  // Should be ~10
    double ratio_2 = kappa_high / kappa_mid; // Should be ~10

    bool scaling_ok = (ratio_1 > 9.9 && ratio_1 < 10.1) &&
                      (ratio_2 > 9.9 && ratio_2 < 10.1);

    std::cout << std::scientific;
    std::cout << "  n_e = 1e3: kappa = " << kappa_low << "\n"
              << "  n_e = 1e4: kappa = " << kappa_mid << " (ratio: " << ratio_1 << ")\n"
              << "  n_e = 1e5: kappa = " << kappa_high << " (ratio: " << ratio_2 << ")\n"
              << "  Status: " << (scaling_ok ? "PASS" : "FAIL") << "\n\n";

    return scaling_ok;
}

// Test 7: Total scattering opacity combination
bool test_total_scattering_opacity() {
    std::cout << "Test 7: Total Scattering Opacity\n";

    double nu = 1e14;         // Optical
    double n_e = 1e3;         // cm^-3
    double grain_radius = 1e-4;  // 0.1 micron
    double grain_density = 1e-12; // Very low density

    double kappa_total = total_scattering_opacity(nu, n_e, grain_radius, grain_density);

    // Should be positive and real
    double kappa_T = thomson_opacity(n_e);
    double kappa_R = rayleigh_opacity(nu, grain_radius, grain_density, 1.5);
    double kappa_Mie = mie_opacity(nu, grain_radius, grain_density);

    double expected = kappa_T + kappa_R + kappa_Mie;
    bool total_ok = (std::abs(kappa_total - expected) / expected < 1e-10);

    std::cout << std::scientific;
    std::cout << "  Thomson: " << kappa_T << "\n"
              << "  Rayleigh: " << kappa_R << "\n"
              << "  Mie: " << kappa_Mie << "\n"
              << "  Total: " << kappa_total << "\n"
              << "  Expected: " << expected << "\n"
              << "  Status: " << (total_ok ? "PASS" : "FAIL") << "\n\n";

    return total_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "SCATTERING MODELS VALIDATION\n"
              << "Phase 7.1b: Scattering Physics\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_thomson_frequency_independence())  passed++;
    if (test_rayleigh_frequency_dependence())   passed++;
    if (test_mie_scattering_efficiency())       passed++;
    if (test_single_scattering_albedo())        passed++;
    if (test_asymmetry_parameter())             passed++;
    if (test_thomson_opacity_scaling())         passed++;
    if (test_total_scattering_opacity())        passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
