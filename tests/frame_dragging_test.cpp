/**
 * @file frame_dragging_test.cpp
 * @brief Validation tests for frame dragging and ergosphere calculations
 *
 * WHY: Verify physics correctness of ZAMO angular velocity and ergosphere boundary
 * WHAT: 6 validation tests against BPT 1972 formulas
 * HOW: Test Ω_ZAMO, r_ergo, and frame dragging effects for various spin parameters
 */

#include <iostream>
#include <cmath>
#include <iomanip>
#include <cassert>

// Constants
constexpr double M_PI_VAL = 3.14159265358979323846;

// Test tolerance
constexpr double TOLERANCE = 1e-6;

/**
 * @brief Compute event horizon radius r_+
 *
 * r_+ = M + √(M² - a²)
 */
double event_horizon(double a_star) {
    a_star = std::clamp(a_star, -0.9999, 0.9999);
    double a_sqr = a_star * a_star;
    return 1.0 + std::sqrt(1.0 - a_sqr);
}

/**
 * @brief Compute ergosphere outer boundary radius
 *
 * r_ergo = M + √(M² - a² cos²θ)
 */
double ergosphere(double a_star, double theta) {
    a_star = std::clamp(a_star, -0.9999, 0.9999);
    double cos_theta = std::cos(theta);
    double a_sqr_cos_sqr = a_star * a_star * cos_theta * cos_theta;
    return 1.0 + std::sqrt(1.0 - a_sqr_cos_sqr);
}

/**
 * @brief Compute ZAMO angular velocity (frame dragging frequency)
 *
 * Ω = 2Mar / (r³ + a²r + 2Ma²) where M=1
 */
double frame_dragging_omega(double r, double a_star) {
    a_star = std::clamp(a_star, -0.9999, 0.9999);
    double a_sqr = a_star * a_star;
    
    double numerator = 2.0 * a_star * r;
    double denominator = r * r * r + a_sqr * r + 2.0 * a_sqr;
    
    if (denominator < 1e-10) {
        return 0.0;
    }
    
    return numerator / denominator;
}

/**
 * @brief Test 1: Schwarzschild (a=0) has no ergosphere
 */
bool test_schwarzschild_no_ergosphere() {
    std::cout << "\n[TEST 1] Schwarzschild No Ergosphere\n";
    std::cout << "=====================================\n";
    
    const double a_star = 0.0;
    const double r_plus = event_horizon(a_star);
    const double r_ergo = ergosphere(a_star, M_PI_VAL / 2.0);  // Equator
    
    std::cout << std::fixed << std::setprecision(10);
    std::cout << "  r_+:     " << r_plus << " M\n";
    std::cout << "  r_ergo:  " << r_ergo << " M\n";
    std::cout << "  Diff:    " << std::abs(r_plus - r_ergo) << "\n";
    
    const bool passed = std::abs(r_plus - r_ergo) < TOLERANCE;
    std::cout << "  Status:  " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:    Ergosphere coincides with horizon for a=0\n";
    
    return passed;
}

/**
 * @brief Test 2: Near-extremal Kerr (a=0.998) ergosphere size
 */
bool test_kerr_ergosphere_size() {
    std::cout << "\n[TEST 2] Near-Extremal Kerr Ergosphere\n";
    std::cout << "=======================================\n";
    
    const double a_star = 0.998;
    const double r_plus = event_horizon(a_star);
    const double r_ergo_equator = ergosphere(a_star, M_PI_VAL / 2.0);
    const double r_ergo_pole = ergosphere(a_star, 0.0);
    
    std::cout << std::fixed << std::setprecision(10);
    std::cout << "  Spin:         a* = " << a_star << "\n";
    std::cout << "  r_+:          " << r_plus << " M\n";
    std::cout << "  r_ergo (θ=π/2): " << r_ergo_equator << " M\n";
    std::cout << "  r_ergo (θ=0):   " << r_ergo_pole << " M\n";
    std::cout << "  Thickness:    " << (r_ergo_equator - r_plus) << " M\n";
    
    // Expected: r_+ ≈ 1.06, r_ergo ≈ 2.0 at equator
    const bool passed = (r_plus < 1.1) && (r_ergo_equator > 1.9) && (r_ergo_equator < 2.1);
    std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    
    return passed;
}

/**
 * @brief Test 3: Frame dragging Ω vanishes at infinity
 */
bool test_omega_vanishes_at_infinity() {
    std::cout << "\n[TEST 3] Frame Dragging Vanishes at Infinity\n";
    std::cout << "=============================================\n";
    
    const double a_star = 0.9;
    const double r_large = 1000.0;
    const double omega = frame_dragging_omega(r_large, a_star);
    
    std::cout << std::scientific << std::setprecision(6);
    std::cout << "  Spin:    a* = " << a_star << "\n";
    std::cout << "  Radius:  r = " << r_large << " M\n";
    std::cout << "  Ω_ZAMO:  " << omega << " rad/M\n";
    
    // Expected: Ω ~ 1/r³ for large r
    const double expected_order = 1.0 / (r_large * r_large * r_large);
    std::cout << "  Expected order: ~" << expected_order << "\n";
    
    const bool passed = std::abs(omega) < 1e-5;  // ~2e-6 for a=0.9, r=1000
    std::cout << "  Status:  " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";

    return passed;
}

/**
 * @brief Test 4: Frame dragging maximum near horizon
 */
bool test_omega_maximum_near_horizon() {
    std::cout << "\n[TEST 4] Frame Dragging Maximum Near Horizon\n";
    std::cout << "=============================================\n";
    
    const double a_star = 0.9;
    const double r_plus = event_horizon(a_star);
    const double r_test = r_plus + 0.01;
    
    const double omega_near = frame_dragging_omega(r_test, a_star);
    const double omega_far = frame_dragging_omega(10.0, a_star);
    
    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Spin:         a* = " << a_star << "\n";
    std::cout << "  r_+:          " << r_plus << " M\n";
    std::cout << "  Ω (r=r_++0.01): " << omega_near << " rad/M\n";
    std::cout << "  Ω (r=10M):    " << omega_far << " rad/M\n";
    std::cout << "  Ratio:        " << omega_near / omega_far << "x\n";
    
    const bool passed = omega_near > omega_far * 10.0;  // ~25x for a=0.9
    std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:         Frame dragging strongest near horizon\n";
    
    return passed;
}

/**
 * @brief Test 5: Ergosphere oblate shape (wider at equator)
 */
bool test_ergosphere_oblate() {
    std::cout << "\n[TEST 5] Ergosphere Oblate Shape\n";
    std::cout << "=================================\n";
    
    const double a_star = 0.9;
    const double r_ergo_equator = ergosphere(a_star, M_PI_VAL / 2.0);
    const double r_ergo_pole = ergosphere(a_star, 0.0);
    
    std::cout << std::fixed << std::setprecision(10);
    std::cout << "  Spin:         a* = " << a_star << "\n";
    std::cout << "  r_ergo (equator): " << r_ergo_equator << " M\n";
    std::cout << "  r_ergo (pole):    " << r_ergo_pole << " M\n";
    std::cout << "  Ratio:        " << r_ergo_equator / r_ergo_pole << "\n";
    
    const bool passed = r_ergo_equator > r_ergo_pole;
    std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:         Ergosphere bulges at equator\n";
    
    return passed;
}

/**
 * @brief Test 6: Frame dragging sign matches spin direction
 */
bool test_omega_sign() {
    std::cout << "\n[TEST 6] Frame Dragging Sign\n";
    std::cout << "=============================\n";
    
    const double r = 3.0;
    const double a_pos = 0.5;
    const double a_neg = -0.5;
    
    const double omega_pos = frame_dragging_omega(r, a_pos);
    const double omega_neg = frame_dragging_omega(r, a_neg);
    
    std::cout << std::fixed << std::setprecision(8);
    std::cout << "  Radius:       r = " << r << " M\n";
    std::cout << "  Ω (a=+0.5):   " << omega_pos << " rad/M\n";
    std::cout << "  Ω (a=-0.5):   " << omega_neg << " rad/M\n";
    
    const bool passed = (omega_pos > 0.0) && (omega_neg < 0.0) && 
                        (std::abs(omega_pos + omega_neg) < TOLERANCE);
    std::cout << "  Status:       " << (passed ? "PASS ✓" : "FAIL ✗") << "\n";
    std::cout << "  Note:         Ω changes sign with spin direction\n";
    
    return passed;
}

/**
 * @brief Main test runner
 */
int main() {
    std::cout << "\n";
    std::cout << "========================================================\n";
    std::cout << "  Frame Dragging & Ergosphere Validation Tests\n";
    std::cout << "========================================================\n";
    
    int passed = 0;
    int total = 6;
    
    // Run all tests
    if (test_schwarzschild_no_ergosphere()) passed++;
    if (test_kerr_ergosphere_size()) passed++;
    if (test_omega_vanishes_at_infinity()) passed++;
    if (test_omega_maximum_near_horizon()) passed++;
    if (test_ergosphere_oblate()) passed++;
    if (test_omega_sign()) passed++;
    
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
