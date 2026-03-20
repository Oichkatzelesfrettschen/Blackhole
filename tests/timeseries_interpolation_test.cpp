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
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    bool metadata_ok = (ts.nDumps == 6) &&
                      (ts.tStart == 0.0) &&
                      (ts.tEnd == 5.0) &&
                      (ts.frequency > 0.0);

    std::cout << "  Dumps: " << ts.nDumps << "\n"
              << "  Time range: [" << ts.tStart << ", " << ts.tEnd << "]\n"
              << "  Frequency: " << std::fixed << std::setprecision(3) << ts.frequency << " Hz\n"
              << "  First dt: " << ts.dumps[0].dt << " (expect 1.0)\n"
              << "  Status: " << (metadata_ok ? "PASS" : "FAIL") << "\n\n";

    return metadata_ok;
}

// Test 2: Interpolation state finding
bool test_interpolation_state_finding() {
    std::cout << "Test 2: Interpolation State Finding\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    // Test at various times
    InterpolationState s1 = getInterpolationState(ts, 0.5);  // Between 0 and 1
    InterpolationState s2 = getInterpolationState(ts, 1.5);  // Between 1 and 2
    InterpolationState s3 = getInterpolationState(ts, 3.5);  // Past end (clamp to last)
    InterpolationState s4 = getInterpolationState(ts, -0.5); // Before start (clamp to first)

    // Out of bounds: implementation clamps to nearest boundary dump
    bool state_ok = (s1.dumpLeft == 0 && s1.dumpRight == 1 && std::abs(s1.alpha - 0.5) < 1e-10) &&
                    (s2.dumpLeft == 1 && s2.dumpRight == 2 && std::abs(s2.alpha - 0.5) < 1e-10) &&
                    (s3.dumpLeft == 3 && s3.dumpRight == 3 && s3.alpha == 1.0) &&  // Past end: hold last
                    (s4.dumpLeft == 0 && s4.dumpRight == 0 && s4.alpha == 0.0);    // Before start: hold first

    std::cout << "  t=0.5 (middle): [" << s1.dumpLeft << "," << s1.dumpRight << "] alpha=" << std::fixed << std::setprecision(2) << s1.alpha << "\n"
              << "  t=1.5 (middle): [" << s2.dumpLeft << "," << s2.dumpRight << "] alpha=" << s2.alpha << "\n"
              << "  t=3.5 (past): [" << s3.dumpLeft << "," << s3.dumpRight << "] alpha=" << s3.alpha << " (out of bounds)\n"
              << "  t=-0.5 (before): [" << s4.dumpLeft << "," << s4.dumpRight << "] alpha=" << s4.alpha << " (out of bounds)\n"
              << "  Status: " << (state_ok ? "PASS" : "FAIL") << "\n\n";

    return state_ok;
}

// Test 3: Linear interpolation
bool test_linear_interpolation() {
    std::cout << "Test 3: Linear Interpolation\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    std::vector<double> field = {0.0, 10.0, 20.0, 30.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    double val_0 = interpolateField(ts, field.data(), 0.0, false);
    double val_0p5 = interpolateField(ts, field.data(), 0.5, false);
    double val_1p5 = interpolateField(ts, field.data(), 1.5, false);
    double val_3 = interpolateField(ts, field.data(), 3.0, false);

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
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    // Hermite should give continuous and smooth interpolation
    double val_1p0 = interpolateField(ts, field.data(), 1.0, true);
    double val_1p5 = interpolateField(ts, field.data(), 1.5, true);
    double val_2p0 = interpolateField(ts, field.data(), 2.0, true);

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
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    double t0 = 2.5;
    double t1 = advanceTime(ts, t0, 0.3, true);   // Forward within range
    double t2 = advanceTime(ts, 2.9, 0.2, true);  // Wraps around
    double t3 = advanceTime(ts, 2.9, 0.2, false); // Clamps at end

    bool advance_ok = (std::abs(t1 - 2.8) < 1e-10) &&
                      (t2 < ts.tEnd) &&  // Should wrap
                      (std::abs(t3 - 3.0) < 1e-10);  // Should clamp

    std::cout << std::fixed << std::setprecision(3);
    std::cout << "  advanceTime(2.5, 0.3, wrap): " << t1 << " (expect 2.800)\n"
              << "  advanceTime(2.9, 0.2, wrap): " << t2 << " (should loop back)\n"
              << "  advanceTime(2.9, 0.2, clamp): " << t3 << " (expect 3.000)\n"
              << "  Status: " << (advance_ok ? "PASS" : "FAIL") << "\n\n";

    return advance_ok;
}

// Test 6: Playback state management
bool test_playback_state() {
    std::cout << "Test 6: Playback State Management\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    PlaybackState ps = createPlaybackState(ts, 0.5);  // 0.5x speed

    bool creation_ok = (ps.tCurrent == ts.tStart) &&
                      (std::abs(ps.playbackSpeed - 0.5) < 1e-10) &&
                      (!ps.isPlaying) &&
                      (ps.loop) &&
                      (ps.frameNumber == 0);

    // Simulate 10 frames at 60 FPS
    ps.isPlaying = true;
    for (int i = 0; i < 10; i++) {
        updatePlayback(ps, ts, 1.0 / 60.0);  // 60 FPS
    }

    bool playback_ok = creation_ok &&
                      (ps.isPlaying) &&
                      (ps.frameNumber == 10) &&
                      (ps.tCurrent > ts.tStart);

    std::cout << "  Initial state: t=" << ts.tStart << ", speed=" << ps.playbackSpeed << ", playing=" << ps.isPlaying << "\n"
              << "  After 10 frames: t=" << ps.tCurrent << ", frame=" << ps.frameNumber << "\n"
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

    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    // Sample at mid-point
    double rho_mid = interpolateField(ts, rho_field.data(), 0.95, false);
    double B_mid = interpolateField(ts, B_field.data(), 0.95, false);

    bool ts_ok = (ts.nDumps == 20) &&
                 (std::abs(ts.tStart - 0.0) < 1e-10) &&
                 (std::abs(ts.tEnd - 1.9) < 1e-10) &&
                 (rho_mid > 0.0 && rho_mid < 2.0) &&
                 (B_mid > 85.0 && B_mid < 115.0);

    std::cout << "  Total dumps: " << ts.nDumps << "\n"
              << "  Time range: [" << std::fixed << std::setprecision(2) << ts.tStart << ", " << ts.tEnd << "]\n"
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
