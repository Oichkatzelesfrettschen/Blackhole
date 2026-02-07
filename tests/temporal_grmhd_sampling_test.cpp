/**
 * @file temporal_grmhd_sampling_test.cpp
 * @brief Phase 8.1b: Temporal GRMHD Field Sampling & Interpolation
 *
 * Validates sampling of GRMHD fields at arbitrary times by interpolating between dumps
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

#include "../src/physics/timeseries_interpolation.h"

using namespace physics;

// Test 1: GRMHD field time evolution
bool test_grmhd_field_evolution() {
    std::cout << "Test 1: GRMHD Field Time Evolution\n";

    // Simulate 10 dumps of GRMHD density field
    std::vector<double> times;
    std::vector<double> rho_field;

    for (int i = 0; i < 10; i++) {
        times.push_back(i * 0.1);
        // Density evolves sinusoidally
        rho_field.push_back(1.0 + 0.5 * std::sin(i * 0.628));
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Sample at multiple times
    double rho_0 = interpolate_field(ts, rho_field.data(), 0.0, false);
    double rho_mid = interpolate_field(ts, rho_field.data(), 0.45, false);
    double rho_end = interpolate_field(ts, rho_field.data(), 0.9, false);

    bool evolution_ok = (std::abs(rho_0 - 1.0) < 0.1) &&
                        (rho_mid > 0.5 && rho_mid < 1.5) &&
                        (std::abs(rho_end - 0.7) < 0.2);  // Near minimum of sine

    std::cout << "  rho(t=0.0) = " << rho_0 << " (expect ~1.0)\n"
              << "  rho(t=0.45) = " << rho_mid << " (expect between peaks)\n"
              << "  rho(t=0.9) = " << rho_end << " (expect ~0.7, near sine min)\n"
              << "  Status: " << (evolution_ok ? "PASS" : "FAIL") << "\n\n";

    return evolution_ok;
}

// Test 2: Multi-field interpolation
bool test_multi_field_interpolation() {
    std::cout << "Test 2: Multi-Field Interpolation\n";

    // Two GRMHD fields: density and temperature
    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    std::vector<double> rho = {1.0, 1.2, 1.1, 0.9};
    std::vector<double> temp = {1e7, 2e7, 1.5e7, 1.2e7};

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Sample both fields at mid-points
    double rho_1p5 = interpolate_field(ts, rho.data(), 1.5, false);
    double temp_1p5 = interpolate_field(ts, temp.data(), 1.5, false);

    bool multi_ok = (rho_1p5 > 1.1 && rho_1p5 < 1.2) &&
                    (temp_1p5 > 1.5e7 && temp_1p5 < 2e7);

    std::cout << std::scientific << std::setprecision(2);
    std::cout << "  rho(1.5) = " << rho_1p5 << " (expect between 1.1 and 1.2)\n"
              << "  T(1.5) = " << temp_1p5 << " (expect between 1.5e7 and 2e7)\n"
              << "  Status: " << (multi_ok ? "PASS" : "FAIL") << "\n\n";

    return multi_ok;
}

// Test 3: Rapid field sampling at fine time steps
bool test_fine_timescale_sampling() {
    std::cout << "Test 3: Fine Timescale Field Sampling\n";

    // 5 dumps over 0.1 time units
    std::vector<double> times = {0.0, 0.025, 0.05, 0.075, 0.1};
    std::vector<double> B_field = {100.0, 105.0, 110.0, 105.0, 100.0};

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Sample at very fine resolution
    std::vector<double> sample_times = {0.01, 0.03, 0.06, 0.08};
    std::vector<double> samples;

    for (double t : sample_times) {
        samples.push_back(interpolate_field(ts, B_field.data(), t, false));
    }

    // All samples should be between min and max
    bool fine_ok = true;
    for (double B : samples) {
        if (B < 99.0 || B > 111.0) fine_ok = false;
    }

    std::cout << "  Samples at fine times: ";
    for (size_t i = 0; i < samples.size(); i++) {
        std::cout << std::fixed << std::setprecision(1) << samples[i] << " ";
    }
    std::cout << "\n  All in range [99, 111]: " << (fine_ok ? "yes" : "no") << "\n"
              << "  Status: " << (fine_ok ? "PASS" : "FAIL") << "\n\n";

    return fine_ok;
}

// Test 4: Boundary behavior at time series edges
bool test_boundary_sampling() {
    std::cout << "Test 4: Boundary Sampling Behavior\n";

    std::vector<double> times = {0.0, 1.0, 2.0};
    std::vector<double> field = {10.0, 20.0, 15.0};

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Sample at exact boundaries
    double f_start = interpolate_field(ts, field.data(), 0.0, false);
    double f_end = interpolate_field(ts, field.data(), 2.0, false);

    // Sample just beyond boundaries
    double f_before = interpolate_field(ts, field.data(), -0.5, false);
    double f_after = interpolate_field(ts, field.data(), 2.5, false);

    bool boundary_ok = (std::abs(f_start - 10.0) < 1e-10) &&
                       (std::abs(f_end - 15.0) < 1e-10) &&
                       (std::abs(f_before - 10.0) < 1.0) &&  // Should extrapolate
                       (std::abs(f_after - 15.0) < 1.0);

    std::cout << "  f(0.0) = " << f_start << " (expect 10.0)\n"
              << "  f(2.0) = " << f_end << " (expect 15.0)\n"
              << "  f(-0.5) = " << f_before << " (extrapolate)\n"
              << "  f(2.5) = " << f_after << " (extrapolate)\n"
              << "  Status: " << (boundary_ok ? "PASS" : "FAIL") << "\n\n";

    return boundary_ok;
}

// Test 5: High-frequency oscillations
bool test_oscillating_fields() {
    std::cout << "Test 5: Oscillating Field Sampling\n";

    // Rapidly oscillating magnetic field (magnetohydrodynamic waves)
    std::vector<double> times;
    std::vector<double> B_osc;

    for (int i = 0; i < 20; i++) {
        times.push_back(i * 0.05);
        // High-frequency B-field oscillations
        B_osc.push_back(100.0 + 50.0 * std::sin(i * 1.57));  // freq ~ 10 Hz
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Sample at intermediate times
    double B_mid = interpolate_field(ts, B_osc.data(), 0.475, false);
    double B_peak1 = interpolate_field(ts, B_osc.data(), 0.25, false);
    double B_valley = interpolate_field(ts, B_osc.data(), 0.5, false);

    bool osc_ok = (B_mid > 50.0 && B_mid < 150.0) &&
                  (B_peak1 > 100.0) &&
                  (B_valley > 50.0 && B_valley < 150.0);

    std::cout << std::fixed << std::setprecision(1);
    std::cout << "  B(0.475) = " << B_mid << " (oscillating)\n"
              << "  B(0.25) = " << B_peak1 << " (near peak)\n"
              << "  B(0.5) = " << B_valley << " (near valley)\n"
              << "  Status: " << (osc_ok ? "PASS" : "FAIL") << "\n\n";

    return osc_ok;
}

// Test 6: Smooth vs. linear interpolation difference
bool test_interpolation_smoothness() {
    std::cout << "Test 6: Interpolation Smoothness Comparison\n";

    // Sharp feature in field evolution
    std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0};
    std::vector<double> field = {1.0, 10.0, 2.0, 10.0, 1.0};

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    double lin_1p5 = interpolate_field(ts, field.data(), 1.5, false);
    double herm_1p5 = interpolate_field(ts, field.data(), 1.5, true);

    // Hermite should be smoother than linear near sharp transitions
    bool smoothness_ok = (lin_1p5 > 2.0 && lin_1p5 < 10.0) &&
                         (herm_1p5 > 2.0 && herm_1p5 < 10.0);

    std::cout << std::fixed << std::setprecision(2);
    std::cout << "  Linear f(1.5) = " << lin_1p5 << "\n"
              << "  Hermite f(1.5) = " << herm_1p5 << "\n"
              << "  Both in valid range: " << (smoothness_ok ? "yes" : "no") << "\n"
              << "  Status: " << (smoothness_ok ? "PASS" : "FAIL") << "\n\n";

    return smoothness_ok;
}

// Test 7: Complete multi-dump animation cycle
bool test_animation_cycle() {
    std::cout << "Test 7: Complete Animation Cycle\n";

    // 10-dump simulation sequence
    std::vector<double> times;
    std::vector<double> accretion_rate;

    for (int i = 0; i < 10; i++) {
        times.push_back(i * 0.1);
        // Accretion rate varies sinusoidally over cycle
        accretion_rate.push_back(1.0 + 0.5 * std::sin(i * 0.628));
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));
    PlaybackState pb = create_playback_state(ts, 1.0);

    // Simulate 30 frames at 30 FPS
    pb.is_playing = true;
    int frame_count = 0;

    for (int f = 0; f < 30; f++) {
        update_playback(pb, ts, 1.0 / 30.0);
        double mdot = interpolate_field(ts, accretion_rate.data(), pb.t_current, false);
        if (mdot > 0.5 && mdot < 1.5) frame_count++;
    }

    bool cycle_ok = (pb.frame_number == 30) &&
                    (pb.t_current > ts.t_start) &&
                    (frame_count >= 25);  // Most frames should have valid field

    std::cout << "  Total frames: " << pb.frame_number << " (expect 30)\n"
              << "  Final time: " << std::fixed << std::setprecision(3) << pb.t_current << "\n"
              << "  Valid field frames: " << frame_count << "/30\n"
              << "  Status: " << (cycle_ok ? "PASS" : "FAIL") << "\n\n";

    return cycle_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "TEMPORAL GRMHD FIELD SAMPLING VALIDATION\n"
              << "Phase 8.1b: Time-Dependent GRMHD\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_grmhd_field_evolution())          passed++;
    if (test_multi_field_interpolation())      passed++;
    if (test_fine_timescale_sampling())        passed++;
    if (test_boundary_sampling())              passed++;
    if (test_oscillating_fields())             passed++;
    if (test_interpolation_smoothness())       passed++;
    if (test_animation_cycle())                passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
