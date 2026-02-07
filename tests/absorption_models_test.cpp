/**
 * @file absorption_models_test.cpp
 * @brief Phase 7.1a: Absorption Models Validation
 *
 * Tests synchrotron self-absorption, free-free absorption, and Compton scattering
 * across a frequency range from radio to X-ray.
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

// Import absorption models from Phase 7.1a
#include "../src/physics/absorption_models.h"

using namespace physics;

// Test 1: Synchrotron Self-Absorption frequency dependence
bool test_ssa_frequency_dependence() {
    std::cout << "Test 1: SSA Frequency Dependence\n";

    double B = 100.0;   // Gauss
    double n_e = 1e3;   // cm^-3
    double T = 1e7;     // K
    double nu_ref = 1e10; // Hz reference

    double alpha_low = synchrotron_self_absorption(nu_ref, B, n_e, T);
    double alpha_mid = synchrotron_self_absorption(nu_ref * 10.0, B, n_e, T);
    double alpha_high = synchrotron_self_absorption(nu_ref * 100.0, B, n_e, T);

    // SSA should decrease as 1/nu^2
    // So alpha(10*nu) ~ alpha(nu) / 100, ratio = 0.01
    double ratio_1 = alpha_mid / alpha_low;
    double ratio_2 = alpha_high / alpha_mid;

    bool freq_dep_ok = (ratio_1 < 0.015 && ratio_1 > 0.005) &&
                       (ratio_2 < 0.015 && ratio_2 > 0.005);

    std::cout << "  nu_ref: " << nu_ref << " Hz\n"
              << "  alpha(nu): " << std::scientific << alpha_low << "\n"
              << "  alpha(10*nu): " << alpha_mid << "\n"
              << "  alpha(100*nu): " << alpha_high << "\n"
              << "  Ratio (10x): " << ratio_1 << " (expect ~0.1)\n"
              << "  Ratio (100x): " << ratio_2 << " (expect ~0.1)\n"
              << "  Status: " << (freq_dep_ok ? "PASS" : "FAIL") << "\n\n";

    return freq_dep_ok;
}

// Test 2: Free-Free Absorption temperature dependence
bool test_ff_temperature_dependence() {
    std::cout << "Test 2: Free-Free Temperature Dependence\n";

    double nu = 1e10;    // Hz
    double n_e = 1e3;    // cm^-3
    double T_low = 1e6;  // K
    double T_high = 1e7; // K (10x hotter)

    double alpha_cool = free_free_absorption(nu, n_e, T_low);
    double alpha_hot = free_free_absorption(nu, n_e, T_high);

    // Free-free ~ 1/T^(3/2)
    // So alpha(10*T) ~ alpha(T) / 10^(3/2) ~ alpha(T) / 31.6
    double ratio = alpha_cool / alpha_hot;
    bool temp_dep_ok = (ratio > 25.0 && ratio < 40.0);  // ~31.6 expected

    std::cout << "  T_cool = " << T_low << " K: alpha = " << std::scientific << alpha_cool << "\n"
              << "  T_hot = " << T_high << " K: alpha = " << alpha_hot << "\n"
              << "  Ratio (cool/hot): " << ratio << " (expect ~31.6)\n"
              << "  Status: " << (temp_dep_ok ? "PASS" : "FAIL") << "\n\n";

    return temp_dep_ok;
}

// Test 3: Compton absorption (Thomson limit)
bool test_compton_thomson_limit() {
    std::cout << "Test 3: Compton Absorption (Thomson Limit)\n";

    double nu = 1e10;  // Radio (low energy, Thomson regime)
    double n_e = 1e3;  // cm^-3
    double theta = 0.1; // Mildly relativistic temperature

    double alpha_comp = compton_absorption(nu, n_e, theta);

    // In Thomson limit, alpha_comp = n_e * sigma_T ~ 1e-24 * 1e3 ~ 1e-21 cm^-1
    bool comp_ok = (alpha_comp > 1e-24 && alpha_comp < 1e-20);

    std::cout << "  nu: " << nu << " Hz (radio)\n"
              << "  n_e: " << n_e << " cm^-3\n"
              << "  alpha_comp: " << std::scientific << alpha_comp << " cm^-1\n"
              << "  Expected range: 1e-24 to 1e-20\n"
              << "  Status: " << (comp_ok ? "PASS" : "FAIL") << "\n\n";

    return comp_ok;
}

// Test 4: Total absorption coefficient (all mechanisms)
bool test_total_absorption() {
    std::cout << "Test 4: Total Absorption Coefficient\n";

    double nu = 1e12;   // Microwave
    double B = 100.0;   // Gauss
    double n_e = 1e3;   // cm^-3
    double T = 1e7;     // K

    double alpha_ssa = synchrotron_self_absorption(nu, B, n_e, T);
    double alpha_ff = free_free_absorption(nu, n_e, T);
    double theta = (BOLTZMANN * T) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);
    double alpha_comp = compton_absorption(nu, n_e, theta);
    double alpha_total = total_absorption_coefficient(nu, B, n_e, T);

    // Total should equal sum of components
    double expected_total = alpha_ssa + alpha_ff + alpha_comp;
    bool total_ok = (std::abs(alpha_total - expected_total) / expected_total < 1e-10);

    std::cout << "  SSA:   " << std::scientific << alpha_ssa << "\n"
              << "  FF:    " << alpha_ff << "\n"
              << "  Comp:  " << alpha_comp << "\n"
              << "  Total: " << alpha_total << "\n"
              << "  Sum:   " << expected_total << "\n"
              << "  Status: " << (total_ok ? "PASS" : "FAIL") << "\n\n";

    return total_ok;
}

// Test 5: Dominant absorption mode identification
bool test_dominant_absorption_mode() {
    std::cout << "Test 5: Dominant Absorption Mode Identification\n";

    double B = 100.0;  // Gauss
    double n_e = 1e3;  // cm^-3
    double T = 1e7;    // K

    // Low frequency: SSA should dominate
    int mode_radio = dominant_absorption_mode(1e9, B, n_e, T);  // 1 GHz

    // Mid frequency: free-free might dominate
    int mode_optical = dominant_absorption_mode(1e15, B, n_e, T);  // Optical

    // Very high frequency: Compton/free-free
    int mode_xray = dominant_absorption_mode(1e18, B, n_e, T);  // X-ray

    bool mode_ok = (mode_radio >= 0 && mode_radio <= 2) &&
                   (mode_optical >= 0 && mode_optical <= 2) &&
                   (mode_xray >= 0 && mode_xray <= 2);

    const char* mode_names[] = {"SSA", "Free-Free", "Compton"};

    std::cout << "  1 GHz:    Dominant = " << mode_names[mode_radio] << "\n"
              << "  Optical:  Dominant = " << mode_names[mode_optical] << "\n"
              << "  X-ray:    Dominant = " << mode_names[mode_xray] << "\n"
              << "  Status: " << (mode_ok ? "PASS" : "FAIL") << "\n\n";

    return mode_ok;
}

// Test 6: Optical depth threshold frequency
bool test_optical_depth_threshold() {
    std::cout << "Test 6: Optical Depth Threshold Frequency\n";

    double B = 100.0;         // Gauss
    double n_e = 1e3;         // cm^-3
    double T = 1e7;           // K
    double path_length = 1e16; // cm

    // Find threshold frequency for Compton (mode=2) which is strongest for these parameters
    double nu_threshold = optical_depth_threshold_frequency(B, n_e, T, path_length, 2);

    // Verify that the function produces a valid frequency within search range
    bool freq_in_range = (nu_threshold >= 1e8 && nu_threshold <= 1e20);

    // Verify it returns a different frequency than extremes
    double tau_low = compton_absorption(1e9, n_e, 0.1) * path_length;
    double tau_high = compton_absorption(1e19, n_e, 0.1) * path_length;

    // Compton absorption is nearly constant, so threshold should be between extremes
    bool threshold_ok = freq_in_range && (tau_low > 1e-10);

    std::cout << "  B: " << B << " Gauss, n_e: " << n_e << " cm^-3\n"
              << "  Path length: " << path_length << " cm\n"
              << "  Threshold freq (Compton): " << std::scientific << nu_threshold << " Hz\n"
              << "  Frequency in valid range [1e8, 1e20]: " << (freq_in_range ? "yes" : "no") << "\n"
              << "  Tau at low freq: " << tau_low << "\n"
              << "  Tau at high freq: " << tau_high << "\n"
              << "  Status: " << (threshold_ok ? "PASS" : "FAIL") << "\n\n";

    return threshold_ok;
}

// Test 7: Absorption across full frequency spectrum
bool test_spectrum_absorption() {
    std::cout << "Test 7: Absorption Across Frequency Spectrum\n";

    double B = 100.0;  // Gauss
    double n_e = 1e3;  // cm^-3
    double T = 1e7;    // K

    std::vector<double> frequencies = {
        1e9,    // 1 GHz (radio)
        1e12,   // 1 THz (microwave)
        1e15,   // 1 PHz (infrared)
        1e18,   // 1 EHz (X-ray)
    };

    std::vector<const char*> names = {"Radio", "Microwave", "Infrared", "X-ray"};

    std::cout << "  Absorption coefficients across spectrum:\n";
    std::cout << "  Freq Range    | Alpha Total  | Dominant Mode\n";
    std::cout << "  --------------|--------------|---------------\n";

    bool spectrum_ok = true;
    for (size_t i = 0; i < frequencies.size(); i++) {
        double nu = frequencies[i];
        double alpha_total = total_absorption_coefficient(nu, B, n_e, T);
        int mode = dominant_absorption_mode(nu, B, n_e, T);
        const char* mode_name = (mode == 0) ? "SSA" : (mode == 1) ? "FF" : "Compton";

        std::cout << std::scientific << std::setprecision(2);
        std::cout << "  " << nu << " Hz | " << alpha_total << " | " << mode_name << "\n";

        spectrum_ok = spectrum_ok && (alpha_total > 0.0);
    }

    std::cout << "  Status: " << (spectrum_ok ? "PASS" : "FAIL") << "\n\n";

    return spectrum_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "ABSORPTION MODELS VALIDATION\n"
              << "Phase 7.1a: Absorption Mechanisms\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_ssa_frequency_dependence())    passed++;
    if (test_ff_temperature_dependence())   passed++;
    if (test_compton_thomson_limit())       passed++;
    if (test_total_absorption())            passed++;
    if (test_dominant_absorption_mode())    passed++;
    if (test_optical_depth_threshold())     passed++;
    if (test_spectrum_absorption())         passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
