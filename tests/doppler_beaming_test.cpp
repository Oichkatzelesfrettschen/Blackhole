/**
 * @file doppler_beaming_test.cpp
 * @brief Validation tests for relativistic Doppler beaming in accretion disks
 *
 * WHY: Verify 10-1000x flux asymmetry from rotating disk material
 * WHAT: 7 validation tests across inclinations and radii
 * HOW: Test δ^(3+α) boost, inclination dependence, flux conservation
 *
 * Reference:
 *   Cunningham (1975) ApJ 202, 788
 *   Begelman, Blandford, Rees (1984) Rev. Mod. Phys. 56, 255
 */

#include "../src/physics/doppler.h"
#include <iostream>
#include <cmath>
#include <iomanip>

// Constants
constexpr double M_PI_VAL = 3.14159265358979323846;

/**
 * @brief Test 1: Face-on disk (i=0) symmetric boost
 */
bool test_face_on_no_boost() {
    std::cout << "\n[TEST 1] Face-On Disk Symmetric Boost\n";
    std::cout << "======================================\n";

    const double r = 6.0;      // ISCO
    const double a_star = 0.0;
    const double inclination = 0.0;  // Face-on
    const double phi_approaching = 0.0;
    const double phi_receding = M_PI_VAL;

    const double boost_app = physics::disk_doppler_boost(r, a_star, phi_approaching, inclination);
    const double boost_rec = physics::disk_doppler_boost(r, a_star, phi_receding, inclination);

    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Inclination: i = 0° (face-on)\n";
    std::cout << "  Boost (approaching): " << boost_app << "\n";
    std::cout << "  Boost (receding):    " << boost_rec << "\n";
    std::cout << "  Asymmetry:           " << boost_app / boost_rec << "x\n";

    // For face-on, boost is symmetric (transverse Doppler = time dilation only)
    // Expect boost < 1.0 due to γ^(-3) redshift
    const bool passed = (std::abs(boost_app - boost_rec) < 0.01) && (boost_app < 1.0);
    std::cout << "  Status:              " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:                Transverse Doppler redshift (time dilation)\n";

    return passed;
}

/**
 * @brief Test 2: Edge-on disk (i=90°) maximum asymmetry
 */
bool test_edge_on_maximum_asymmetry() {
    std::cout << "\n[TEST 2] Edge-On Disk Maximum Asymmetry\n";
    std::cout << "========================================\n";
    
    const double r = 6.0;      // ISCO
    const double a_star = 0.0;
    const double inclination = M_PI_VAL / 2.0;  // Edge-on
    const double phi_approaching = 0.0;
    const double phi_receding = M_PI_VAL;
    
    const double boost_app = physics::disk_doppler_boost(r, a_star, phi_approaching, inclination);
    const double boost_rec = physics::disk_doppler_boost(r, a_star, phi_receding, inclination);
    const double asymmetry = boost_app / boost_rec;
    
    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Inclination: i = 90° (edge-on)\n";
    std::cout << "  Radius:      r = " << r << " M\n";
    std::cout << "  Boost (approaching): " << boost_app << "\n";
    std::cout << "  Boost (receding):    " << boost_rec << "\n";
    std::cout << "  Asymmetry:           " << asymmetry << "x\n";
    
    // Expected: ~10-100x for edge-on at ISCO
    const bool passed = (asymmetry > 10.0) && (asymmetry < 200.0);
    std::cout << "  Status:              " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Expected:            10-200x (literature range)\n";
    
    return passed;
}

/**
 * @brief Test 3: Inclination sweep (0° to 90°)
 */
bool test_inclination_sweep() {
    std::cout << "\n[TEST 3] Inclination Sweep\n";
    std::cout << "==========================\n";
    
    const double r = 6.0;
    const double a_star = 0.0;
    const double phi_approaching = 0.0;
    const double phi_receding = M_PI_VAL;
    
    std::cout << std::fixed << std::setprecision(4);
    std::cout << "  Radius: r = " << r << " M\n\n";
    std::cout << "  Incl (deg)  Approaching  Receding  Asymmetry\n";
    std::cout << "  ----------  -----------  --------  ---------\n";
    
    bool all_passed = true;
    double prev_asymmetry = 1.0;
    
    for (int i_deg = 0; i_deg <= 90; i_deg += 15) {
        const double incl = i_deg * M_PI_VAL / 180.0;
        const double boost_app = physics::disk_doppler_boost(r, a_star, phi_approaching, incl);
        const double boost_rec = physics::disk_doppler_boost(r, a_star, phi_receding, incl);
        const double asymmetry = boost_app / boost_rec;
        
        std::cout << "      " << std::setw(3) << i_deg << "       "
                  << std::setw(7) << boost_app << "      "
                  << std::setw(7) << boost_rec << "     "
                  << std::setw(7) << asymmetry << "x\n";
        
        // Asymmetry should monotonically increase with inclination
        if (asymmetry < prev_asymmetry - 0.01) {  // Allow small numerical noise
            all_passed = false;
        }
        prev_asymmetry = asymmetry;
    }
    
    std::cout << "\n  Status: " << (all_passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:   Asymmetry increases monotonically with inclination\n";
    
    return all_passed;
}

/**
 * @brief Test 4: Inner disk (smaller r) higher boost
 */
bool test_inner_disk_higher_boost() {
    std::cout << "\n[TEST 4] Inner Disk Higher Boost\n";
    std::cout << "=================================\n";
    
    const double a_star = 0.0;
    const double inclination = M_PI_VAL / 2.0;  // Edge-on
    const double phi_approaching = 0.0;
    
    const double r_inner = 6.0;   // ISCO
    const double r_outer = 20.0;
    
    const double boost_inner = physics::disk_doppler_boost(r_inner, a_star, phi_approaching, inclination);
    const double boost_outer = physics::disk_doppler_boost(r_outer, a_star, phi_approaching, inclination);
    
    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Inclination: i = 90° (edge-on)\n";
    std::cout << "  Boost (r=6M):  " << boost_inner << "\n";
    std::cout << "  Boost (r=20M): " << boost_outer << "\n";
    std::cout << "  Ratio:         " << boost_inner / boost_outer << "x\n";
    
    const bool passed = boost_inner > boost_outer * 2.0;
    std::cout << "  Status:        " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:          Higher velocity at inner radius\n";
    
    return passed;
}

/**
 * @brief Test 5: Spectral index affects boost exponent
 */
bool test_spectral_index_effect() {
    std::cout << "\n[TEST 5] Spectral Index Effect\n";
    std::cout << "===============================\n";
    
    const double r = 6.0;
    const double a_star = 0.0;
    const double inclination = M_PI_VAL / 2.0;
    const double phi_approaching = 0.0;
    
    const double boost_blackbody = physics::disk_doppler_boost(r, a_star, phi_approaching, inclination, 0.0);
    const double boost_powerlaw = physics::disk_doppler_boost(r, a_star, phi_approaching, inclination, 1.0);
    
    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Radius:      r = " << r << " M\n";
    std::cout << "  Inclination: i = 90°\n";
    std::cout << "  Boost (α=0, blackbody): " << boost_blackbody << "\n";
    std::cout << "  Boost (α=1, power-law): " << boost_powerlaw << "\n";
    std::cout << "  Ratio:                  " << boost_powerlaw / boost_blackbody << "x\n";
    
    const bool passed = boost_powerlaw > boost_blackbody * 1.5;
    std::cout << "  Status:                 " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:                   δ^(3+α) increases with α\n";
    
    return passed;
}

/**
 * @brief Test 6: Kerr vs Schwarzschild at safe radius
 */
bool test_kerr_spin_enhancement() {
    std::cout << "\n[TEST 6] Kerr Spin Formula Validation\n";
    std::cout << "======================================\n";

    // Use r=10M where both Schwarzschild and Kerr have stable orbits
    const double r = 10.0;
    const double inclination = M_PI_VAL / 2.0;
    const double phi_approaching = 0.0;

    const double boost_schwarzschild = physics::disk_doppler_boost(r, 0.0, phi_approaching, inclination);
    const double boost_kerr_retrograde = physics::disk_doppler_boost(r, -0.5, phi_approaching, inclination);
    const double boost_kerr_prograde = physics::disk_doppler_boost(r, 0.5, phi_approaching, inclination);

    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Radius:         r = " << r << " M\n";
    std::cout << "  Inclination:    i = 90°\n";
    std::cout << "  Boost (a=0):      " << boost_schwarzschild << "\n";
    std::cout << "  Boost (a=-0.5):   " << boost_kerr_retrograde << "\n";
    std::cout << "  Boost (a=+0.5):   " << boost_kerr_prograde << "\n";

    // Spin affects orbital velocity (subtle GR effect at large radii)
    const bool passed = (boost_kerr_prograde != boost_schwarzschild) &&
                        (boost_kerr_retrograde != boost_schwarzschild) &&
                        (boost_kerr_prograde != boost_kerr_retrograde);
    std::cout << "  Status:         " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:           Spin parameter modifies orbital velocity\n";

    return passed;
}

/**
 * @brief Test 7: Boost clamped to reasonable range
 */
bool test_boost_clamping() {
    std::cout << "\n[TEST 7] Boost Clamping\n";
    std::cout << "========================\n";
    
    const double r = 6.0;
    const double a_star = 0.998;  // Near-extremal
    const double inclination = M_PI_VAL / 2.0;
    const double phi_approaching = 0.0;
    const double phi_receding = M_PI_VAL;
    
    const double boost_app = physics::disk_doppler_boost(r, a_star, phi_approaching, inclination, 2.0);
    const double boost_rec = physics::disk_doppler_boost(r, a_star, phi_receding, inclination, 2.0);
    
    std::cout << std::fixed << std::setprecision(6);
    std::cout << "  Spin:         a* = " << a_star << "\n";
    std::cout << "  Spectral idx: α = 2.0\n";
    std::cout << "  Boost (approaching): " << boost_app << "\n";
    std::cout << "  Boost (receding):    " << boost_rec << "\n";
    
    const bool passed = (boost_app <= 1000.0) && (boost_rec >= 0.01);
    std::cout << "  Status:              " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:                Clamped to [0.01, 1000.0] range\n";
    
    return passed;
}

/**
 * @brief Main test runner
 */
int main() {
    std::cout << "\n";
    std::cout << "========================================================\n";
    std::cout << "  Doppler Beaming Validation Tests\n";
    std::cout << "========================================================\n";
    
    int passed = 0;
    int total = 7;
    
    // Run all tests
    if (test_face_on_no_boost()) passed++;
    if (test_edge_on_maximum_asymmetry()) passed++;
    if (test_inclination_sweep()) passed++;
    if (test_inner_disk_higher_boost()) passed++;
    if (test_spectral_index_effect()) passed++;
    if (test_kerr_spin_enhancement()) passed++;
    if (test_boost_clamping()) passed++;
    
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
