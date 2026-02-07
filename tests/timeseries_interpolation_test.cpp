/**
 * @file timeseries_interpolation_test.cpp
 * @brief Phase 8.1a: Time Series Metadata & Interpolation Validation
 *
 * Tests temporal interpolation, playback control, and multi-dump evolution
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

#include "../src/physics/timeseries_interpolation.h"

using namespace physics;

// Test 1: Time series metadata construction
bool test_timeseries_metadata_construction() {
    std::cout << "Test 1: Time Series Metadata Construction\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0};
    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    bool metadata_ok = (ts.n_dumps == 6) &&
                      (ts.t_start == 0.0) &&
                      (ts.t_end == 5.0) &&
                      (ts.frequency > 0.0);

    std::cout << "  Dumps: " << ts.n_dumps << "\n"
              << "  Time range: [" << ts.t_start << ", " << ts.t_end << "]\n"
              << "  Frequency: " << std::fixed << std::setprecision(3) << ts.frequency << " Hz\n"
              << "  First dt: " << ts.dumps[0].dt << " (expect 1.0)\n"
              << "  Status: " << (metadata_ok ? "PASS" : "FAIL") << "\n\n";

    return metadata_ok;
}

// Test 2: Interpolation state finding
bool test_interpolation_state_finding() {
    std::cout << "Test 2: Interpolation State Finding\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Test at various times
    InterpolationState s1 = get_interpolation_state(ts, 0.5);  // Between 0 and 1
    InterpolationState s2 = get_interpolation_state(ts, 1.5);  // Between 1 and 2
    InterpolationState s3 = get_interpolation_state(ts, 3.5);  // Past end (clamp to last)
    InterpolationState s4 = get_interpolation_state(ts, -0.5); // Before start (clamp to first)

    // When out of bounds, should extrapolate (dump_left=0, dump_right=1)
    bool state_ok = (s1.dump_left == 0 && s1.dump_right == 1 && std::abs(s1.alpha - 0.5) < 1e-10) &&
                    (s2.dump_left == 1 && s2.dump_right == 2 && std::abs(s2.alpha - 0.5) < 1e-10) &&
                    (s3.dump_left == 0 && s3.dump_right == 1 && s3.alpha == 0.0) &&  // Out of bounds
                    (s4.dump_left == 0 && s4.dump_right == 1 && s4.alpha == 0.0);    // Out of bounds

    std::cout << "  t=0.5 (middle): [" << s1.dump_left << "," << s1.dump_right << "] alpha=" << std::fixed << std::setprecision(2) << s1.alpha << "\n"
              << "  t=1.5 (middle): [" << s2.dump_left << "," << s2.dump_right << "] alpha=" << s2.alpha << "\n"
              << "  t=3.5 (past): [" << s3.dump_left << "," << s3.dump_right << "] alpha=" << s3.alpha << " (out of bounds)\n"
              << "  t=-0.5 (before): [" << s4.dump_left << "," << s4.dump_right << "] alpha=" << s4.alpha << " (out of bounds)\n"
              << "  Status: " << (state_ok ? "PASS" : "FAIL") << "\n\n";

    return state_ok;
}

// Test 3: Linear interpolation
bool test_linear_interpolation() {
    std::cout << "Test 3: Linear Interpolation\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    std::vector<double> field = {0.0, 10.0, 20.0, 30.0};
    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    double val_0 = interpolate_field(ts, field.data(), 0.0, false);
    double val_0p5 = interpolate_field(ts, field.data(), 0.5, false);
    double val_1p5 = interpolate_field(ts, field.data(), 1.5, false);
    double val_3 = interpolate_field(ts, field.data(), 3.0, false);

    bool interp_ok = (std::abs(val_0 - 0.0) < 1e-10) &&
                     (std::abs(val_0p5 - 5.0) < 1e-10) &&
                     (std::abs(val_1p5 - 15.0) < 1e-10) &&
                     (std::abs(val_3 - 30.0) < 1e-10);

    std::cout << std::scientific << std::setprecision(2);
    std::cout << "  f(0.0) = " << val_0 << " (expect 0)\n"
              << "  f(0.5) = " << val_0p5 << " (expect 5)\n"
              << "  f(1.5) = " << val_1p5 << " (expect 15)\n"
              << "  f(3.0) = " << val_3 << " (expect 30)\n"
              << "  Status: " << (interp_ok ? "PASS" : "FAIL") << "\n\n";

    return interp_ok;
}

// Test 4: Hermite spline interpolation smoothness
bool test_hermite_interpolation() {
    std::cout << "Test 4: Hermite Spline Interpolation\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0};
    std::vector<double> field = {0.0, 10.0, 5.0, 15.0, 20.0};
    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Hermite should give continuous and smooth interpolation
    double val_1p0 = interpolate_field(ts, field.data(), 1.0, true);
    double val_1p5 = interpolate_field(ts, field.data(), 1.5, true);
    double val_2p0 = interpolate_field(ts, field.data(), 2.0, true);

    // At exact dump times, should match field value
    bool hermite_ok = (std::abs(val_1p0 - 10.0) < 0.1) &&
                      (std::abs(val_2p0 - 5.0) < 0.1) &&
                      (val_1p5 > 5.0 && val_1p5 < 10.0);  // Should be between endpoints

    std::cout << std::fixed << std::setprecision(2);
    std::cout << "  f(1.0) = " << val_1p0 << " (expect ~10)\n"
              << "  f(1.5) = " << val_1p5 << " (between 5 and 10: " << (val_1p5 > 5.0 && val_1p5 < 10.0 ? "yes" : "no") << ")\n"
              << "  f(2.0) = " << val_2p0 << " (expect ~5)\n"
              << "  Status: " << (hermite_ok ? "PASS" : "FAIL") << "\n\n";

    return hermite_ok;
}

// Test 5: Time advancement and looping
bool test_time_advancement() {
    std::cout << "Test 5: Time Advancement & Looping\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    double t0 = 2.5;
    double t1 = advance_time(ts, t0, 0.3, true);   // Forward within range
    double t2 = advance_time(ts, 2.9, 0.2, true);  // Wraps around
    double t3 = advance_time(ts, 2.9, 0.2, false); // Clamps at end

    bool advance_ok = (std::abs(t1 - 2.8) < 1e-10) &&
                      (t2 < ts.t_end) &&  // Should wrap
                      (std::abs(t3 - 3.0) < 1e-10);  // Should clamp

    std::cout << std::fixed << std::setprecision(3);
    std::cout << "  advance_time(2.5, 0.3, wrap): " << t1 << " (expect 2.800)\n"
              << "  advance_time(2.9, 0.2, wrap): " << t2 << " (should loop back)\n"
              << "  advance_time(2.9, 0.2, clamp): " << t3 << " (expect 3.000)\n"
              << "  Status: " << (advance_ok ? "PASS" : "FAIL") << "\n\n";

    return advance_ok;
}

// Test 6: Playback state management
bool test_playback_state() {
    std::cout << "Test 6: Playback State Management\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    PlaybackState ps = create_playback_state(ts, 0.5);  // 0.5x speed

    bool creation_ok = (ps.t_current == ts.t_start) &&
                      (std::abs(ps.playback_speed - 0.5) < 1e-10) &&
                      (!ps.is_playing) &&
                      (ps.loop) &&
                      (ps.frame_number == 0);

    // Simulate 10 frames at 60 FPS
    ps.is_playing = true;
    for (int i = 0; i < 10; i++) {
        update_playback(ps, ts, 1.0 / 60.0);  // 60 FPS
    }

    bool playback_ok = creation_ok &&
                      (ps.is_playing) &&
                      (ps.frame_number == 10) &&
                      (ps.t_current > ts.t_start);

    std::cout << "  Initial state: t=" << ts.t_start << ", speed=" << ps.playback_speed << ", playing=" << ps.is_playing << "\n"
              << "  After 10 frames: t=" << ps.t_current << ", frame=" << ps.frame_number << "\n"
              << "  Status: " << (playback_ok ? "PASS" : "FAIL") << "\n\n";

    return playback_ok;
}

// Test 7: Full multi-dump time series
bool test_multi_dump_timeseries() {
    std::cout << "Test 7: Multi-Dump Time Series\n";

    // Simulate 20-dump GRMHD sequence
    std::vector<double> times;
    std::vector<double> rho_field, B_field;  // Two fields to track

    for (int i = 0; i < 20; i++) {
        times.push_back(i * 0.1);  // 0.0 to 1.9 in steps of 0.1
        rho_field.push_back(1.0 + 0.1 * std::sin(i * 0.314));  // Oscillating density
        B_field.push_back(100.0 + 10.0 * std::cos(i * 0.314)); // Oscillating field
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(), static_cast<uint32_t>(times.size()));

    // Sample at mid-point
    double rho_mid = interpolate_field(ts, rho_field.data(), 0.95, false);
    double B_mid = interpolate_field(ts, B_field.data(), 0.95, false);

    bool ts_ok = (ts.n_dumps == 20) &&
                 (std::abs(ts.t_start - 0.0) < 1e-10) &&
                 (std::abs(ts.t_end - 1.9) < 1e-10) &&
                 (rho_mid > 0.0 && rho_mid < 2.0) &&
                 (B_mid > 85.0 && B_mid < 115.0);

    std::cout << "  Total dumps: " << ts.n_dumps << "\n"
              << "  Time range: [" << std::fixed << std::setprecision(2) << ts.t_start << ", " << ts.t_end << "]\n"
              << "  Sample at t=0.95: rho=" << rho_mid << " (expect ~1.0-1.1)\n"
              << "  Sample at t=0.95: B=" << B_mid << " (expect ~100)\n"
              << "  Status: " << (ts_ok ? "PASS" : "FAIL") << "\n\n";

    return ts_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "TIME SERIES INTERPOLATION VALIDATION\n"
              << "Phase 8.1a: Temporal Dynamics\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_timeseries_metadata_construction())  passed++;
    if (test_interpolation_state_finding())       passed++;
    if (test_linear_interpolation())              passed++;
    if (test_hermite_interpolation())             passed++;
    if (test_time_advancement())                  passed++;
    if (test_playback_state())                    passed++;
    if (test_multi_dump_timeseries())             passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
