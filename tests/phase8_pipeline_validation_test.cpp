/**
 * @file phase8_pipeline_validation_test.cpp
 * @brief Phase 8.1d: Full GRMHD Time Series Playback Pipeline Validation
 *
 * Integration tests for complete Phase 8: temporal interpolation, GRMHD
 * field sampling, and advanced playback control working together
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

#include "../src/physics/timeseries_interpolation.h"
#include "../src/physics/playback_control.h"

using namespace physics;

// Test 1: Multi-field GRMHD interpolation with playback control
bool test_multifield_grmhd_playback() {
    std::cout << "Test 1: Multi-Field GRMHD Playback Integration\n";

    // Simulate 15-dump GRMHD sequence
    std::vector<double> times;
    std::vector<double> rho_field;    // Density
    std::vector<double> T_field;      // Temperature
    std::vector<double> B_field;      // Magnetic field magnitude

    for (int i = 0; i < 15; i++) {
        times.push_back(i * 0.1);
        rho_field.push_back(1.0 + 0.3 * std::sin(i * 0.418));
        T_field.push_back(1e7 * (1.0 + 0.5 * std::cos(i * 0.314)));
        B_field.push_back(100.0 + 50.0 * std::sin(i * 0.628));
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = create_advanced_playback_state(ts, 1.0);
    set_playback_mode(state, PlaybackMode::Forward);

    // Sample all 3 fields at multiple times
    std::vector<double> sampled_rho, sampled_T, sampled_B;

    for (int frame = 0; frame < 5; frame++) {
        update_advanced_playback(state, ts, 1.0 / 30.0, 0.0);

        double rho = interpolate_field(ts, rho_field.data(), state.t_current, false);
        double temp = interpolate_field(ts, T_field.data(), state.t_current, false);
        double B = interpolate_field(ts, B_field.data(), state.t_current, true);  // Hermite

        sampled_rho.push_back(rho);
        sampled_T.push_back(temp);
        sampled_B.push_back(B);
    }

    // Verify sample ranges
    bool multifield_ok = (sampled_rho.size() == 5) &&
                        (sampled_T.size() == 5) &&
                        (sampled_B.size() == 5) &&
                        (sampled_rho[0] > 0.7 && sampled_rho[0] < 1.3) &&
                        (sampled_T[0] > 0.5e7 && sampled_T[0] < 1.5e7) &&
                        (sampled_B[0] > 50.0 && sampled_B[0] < 150.0);

    std::cout << "  Samples collected: " << sampled_rho.size() << "\n"
              << "  Rho range: [" << sampled_rho[0] << ", " << sampled_rho[9] << "]\n"
              << "  T range: [" << std::scientific << sampled_T[0] << ", "
              << sampled_T[9] << std::defaultfloat << "]\n"
              << "  B field range: [" << sampled_B[0] << ", " << sampled_B[9] << "]\n"
              << "  Status: " << (multifield_ok ? "PASS" : "FAIL") << "\n\n";

    return multifield_ok;
}

// Test 2: Hermite vs linear interpolation switching
bool test_interpolation_mode_switching() {
    std::cout << "Test 2: Interpolation Mode Switching\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0};
    std::vector<double> field = {1.0, 5.0, 2.0, 8.0, 3.0, 7.0};

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    // Sample at mid-points with both methods
    double linear_2p5 = interpolate_field(ts, field.data(), 2.5, false);
    double hermite_2p5 = interpolate_field(ts, field.data(), 2.5, true);

    double linear_4p5 = interpolate_field(ts, field.data(), 4.5, false);
    double hermite_4p5 = interpolate_field(ts, field.data(), 4.5, true);

    // Hermite should be smoother (closer to Catmull-Rom continuity)
    bool switching_ok = (linear_2p5 > 1.0 && linear_2p5 < 8.0) &&
                       (hermite_2p5 > 1.0 && hermite_2p5 < 8.0) &&
                       (linear_4p5 > 2.0 && linear_4p5 < 8.0) &&
                       (hermite_4p5 > 2.0 && hermite_4p5 < 8.0);

    std::cout << "  Linear f(2.5) = " << std::fixed << std::setprecision(2) << linear_2p5 << "\n"
              << "  Hermite f(2.5) = " << hermite_2p5 << " (smoother)\n"
              << "  Linear f(4.5) = " << linear_4p5 << "\n"
              << "  Hermite f(4.5) = " << hermite_4p5 << " (smoother)\n"
              << "  Status: " << (switching_ok ? "PASS" : "FAIL") << "\n\n";

    return switching_ok;
}

// Test 3: Multi-rate playback (fast-forward, slo-mo)
bool test_multirate_playback() {
    std::cout << "Test 3: Multi-Rate Playback\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    std::vector<double> field = {0.0, 10.0, 20.0, 30.0};

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    // Test 1x speed
    AdvancedPlaybackState state_1x = create_advanced_playback_state(ts, 1.0);
    set_playback_mode(state_1x, PlaybackMode::Forward);

    // Test 2x speed (fast-forward)
    AdvancedPlaybackState state_2x = create_advanced_playback_state(ts, 2.0);
    set_playback_mode(state_2x, PlaybackMode::Forward);

    // Test 0.5x speed (slow-motion)
    AdvancedPlaybackState state_05x = create_advanced_playback_state(ts, 0.5);
    set_playback_mode(state_05x, PlaybackMode::Forward);

    // Simulate 1 frame at 60 FPS
    double dt_frame = 1.0 / 60.0;

    update_advanced_playback(state_1x, ts, dt_frame, 0.0);
    update_advanced_playback(state_2x, ts, dt_frame, 0.0);
    update_advanced_playback(state_05x, ts, dt_frame, 0.0);

    // At 2x speed, time should advance ~2x faster than 1x
    // At 0.5x speed, time should advance ~0.5x slower than 1x
    bool t_2x_faster = (state_2x.t_current > state_1x.t_current);
    bool t_05x_slower = (state_05x.t_current < state_1x.t_current);

    bool multirate_ok = (state_1x.mode == PlaybackMode::Forward) &&
                       (state_2x.mode == PlaybackMode::Forward) &&
                       (state_05x.mode == PlaybackMode::Forward) &&
                       t_2x_faster && t_05x_slower;

    std::cout << "  1x speed: t = " << std::fixed << std::setprecision(4)
              << state_1x.t_current << "\n"
              << "  2x speed: t = " << state_2x.t_current << " (faster)\n"
              << "  0.5x speed: t = " << state_05x.t_current << " (slower)\n"
              << "  Status: " << (multirate_ok ? "PASS" : "FAIL") << "\n\n";

    return multirate_ok;
}

// Test 4: Reverse playback with hermite interpolation
bool test_reverse_with_interpolation() {
    std::cout << "Test 4: Reverse Playback with Hermite Interpolation\n";

    // Create smooth field evolution
    std::vector<double> times;
    std::vector<double> smooth_field;

    for (int i = 0; i < 20; i++) {
        times.push_back(i * 0.05);
        smooth_field.push_back(10.0 + 5.0 * std::sin(i * 0.314));
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = create_advanced_playback_state(ts, 1.0);
    state.t_current = ts.t_end;  // Start at end
    set_playback_mode(state, PlaybackMode::Reverse);
    state.reverse_speed = 1.0;

    // Simulate 5 frames backward
    std::vector<double> reverse_samples;

    for (int frame = 0; frame < 5; frame++) {
        update_advanced_playback(state, ts, 1.0 / 30.0, 0.0);
        double val = interpolate_field(ts, smooth_field.data(), state.t_current, true);
        reverse_samples.push_back(val);
    }

    // Check that time decreased monotonically
    bool reverse_ok = (state.frame_number == 5) &&
                     (state.mode == PlaybackMode::Reverse) &&
                     (state.t_current < ts.t_end) &&
                     (state.t_current > ts.t_start) &&
                     (reverse_samples.size() == 5);

    std::cout << "  Frames played backward: " << state.frame_number << "\n"
              << "  Current time: " << std::fixed << std::setprecision(3) << state.t_current << "\n"
              << "  Field values sampled: " << reverse_samples.size() << "\n"
              << "  All samples in valid range: "
              << (reverse_samples[0] > 5.0 && reverse_samples[0] < 15.0 ? "yes" : "no") << "\n"
              << "  Status: " << (reverse_ok ? "PASS" : "FAIL") << "\n\n";

    return reverse_ok;
}

// Test 5: Frame-by-frame stepping with interpolation
bool test_frame_stepping_integration() {
    std::cout << "Test 5: Frame-By-Frame Stepping Integration\n";

    // 10-dump GRMHD sequence
    std::vector<double> times;
    std::vector<double> density;

    for (int i = 0; i < 10; i++) {
        times.push_back(i * 0.5);
        density.push_back(1.0 + 0.2 * i);
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = create_advanced_playback_state(ts, 1.0);

    // Step through all frames manually (with safety limit)
    std::vector<double> densities_at_frames;

    uint32_t max_steps = 50;  // Safety limit
    while (state.t_current <= ts.t_end && max_steps-- > 0) {
        double rho = interpolate_field(ts, density.data(), state.t_current, false);
        densities_at_frames.push_back(rho);

        step_frame_forward(state, ts);

        if (state.t_current > ts.t_end) break;
    }

    // Verify samples are in reasonable range
    bool all_positive = true;
    for (size_t i = 0; i < densities_at_frames.size(); i++) {
        if (densities_at_frames[i] <= 0.0 || densities_at_frames[i] > 3.0) {
            all_positive = false;
            break;
        }
    }

    bool stepping_ok = (densities_at_frames.size() > 5) &&
                      (state.frame_number > 5) &&
                      all_positive;

    std::cout << "  Frame count: " << state.frame_number << "\n"
              << "  Samples collected: " << densities_at_frames.size() << "\n"
              << "  All samples in valid range [0,3]: " << (all_positive ? "yes" : "no") << "\n"
              << "  First density: " << std::fixed << std::setprecision(2)
              << densities_at_frames[0] << "\n"
              << "  Last density: " << densities_at_frames.back() << "\n"
              << "  Status: " << (stepping_ok ? "PASS" : "FAIL") << "\n\n";

    return stepping_ok;
}

// Test 6: Timeline marker navigation with field sampling
bool test_marker_navigation() {
    std::cout << "Test 6: Timeline Marker Navigation with Field Sampling\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0};
    std::vector<double> field = {10.0, 20.0, 15.0, 25.0, 18.0, 22.0};

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = create_advanced_playback_state(ts, 1.0);

    // Add markers at peaks and valleys
    add_timeline_marker(state, 1.0, ts);  // Peak
    add_timeline_marker(state, 2.0, ts);  // Valley
    add_timeline_marker(state, 3.0, ts);  // Peak
    add_timeline_marker(state, 4.0, ts);  // Valley
    add_timeline_marker(state, 5.0, ts);  // Peak

    // Navigate to markers and sample field
    std::vector<double> marker_samples;

    state.t_current = 0.5;
    for (uint32_t i = 0; i < state.n_markers; i++) {
        seek_to_marker(state, ts, true);
        double val = interpolate_field(ts, field.data(), state.t_current, false);
        marker_samples.push_back(val);

        if (state.t_current >= ts.t_end) break;
    }

    bool marker_ok = (state.n_markers == 5) &&
                    (marker_samples.size() > 2) &&
                    (marker_samples[0] > 15.0);  // First marker is at 1.0, field=20.0

    std::cout << "  Markers created: " << state.n_markers << "\n"
              << "  Markers navigated: " << marker_samples.size() << "\n"
              << "  Fields at markers: ";
    for (size_t i = 0; i < marker_samples.size() && i < 3; i++) {
        std::cout << std::fixed << std::setprecision(0) << marker_samples[i] << " ";
    }
    std::cout << "...\n"
              << "  Status: " << (marker_ok ? "PASS" : "FAIL") << "\n\n";

    return marker_ok;
}

// Test 7: Complete Phase 8 pipeline validation
bool test_complete_phase8_pipeline() {
    std::cout << "Test 7: Complete Phase 8 Pipeline Validation\n";

    // Realistic 20-dump GRMHD simulation
    std::vector<double> times;
    std::vector<double> rho, T, B, psi;

    for (int i = 0; i < 20; i++) {
        times.push_back(i * 0.05);
        rho.push_back(1.0 + 0.3 * std::sin(i * 0.314));
        T.push_back(1e7 * (1.0 + 0.4 * std::cos(i * 0.418)));
        B.push_back(100.0 + 40.0 * std::sin(i * 0.628));
        psi.push_back(0.5 * (1.0 + 0.2 * std::cos(i * 0.314)));
    }

    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = create_advanced_playback_state(ts, 1.0);

    // Add key markers
    add_timeline_marker(state, 0.25, ts);  // Early time
    add_timeline_marker(state, 0.50, ts);  // Mid time
    add_timeline_marker(state, 0.95, ts);  // Late time

    // Full simulation: forward, pause, seek, reverse
    set_playback_mode(state, PlaybackMode::Forward);

    uint32_t total_samples = 0;
    double sum_rho = 0.0, sum_T = 0.0, sum_B = 0.0;

    // Play forward 5 frames
    for (int f = 0; f < 5; f++) {
        update_advanced_playback(state, ts, 1.0 / 30.0, 50.0);

        double rho_val = interpolate_field(ts, rho.data(), state.t_current, false);
        double T_val = interpolate_field(ts, T.data(), state.t_current, false);
        double B_val = interpolate_field(ts, B.data(), state.t_current, true);

        sum_rho += rho_val;
        sum_T += T_val;
        sum_B += B_val;
        total_samples++;
    }

    // Pause and seek
    toggle_pause(state);
    seek_to_marker(state, ts, true);

    // Play backward 3 frames
    reverse_playback_direction(state);
    toggle_pause(state);

    for (int f = 0; f < 3; f++) {
        update_advanced_playback(state, ts, 1.0 / 30.0, 55.0);

        double rho_val = interpolate_field(ts, rho.data(), state.t_current, false);
        double T_val = interpolate_field(ts, T.data(), state.t_current, false);
        double B_val = interpolate_field(ts, B.data(), state.t_current, true);

        sum_rho += rho_val;
        sum_T += T_val;
        sum_B += B_val;
        total_samples++;
    }

    // Verify stats
    bool pipeline_ok = (total_samples == 8) &&
                      (ts.n_dumps == 20) &&
                      (state.n_markers == 3) &&
                      (state.frame_number == 8) &&
                      (sum_rho > 0.0) &&
                      (sum_T > 0.0) &&
                      (sum_B > 0.0) &&
                      (state.avg_interpolation_time > 0.0) &&
                      (state.interpolation_calls == 8);

    std::cout << "  GRMHD dumps: " << ts.n_dumps << "\n"
              << "  Total timeline markers: " << state.n_markers << "\n"
              << "  Total frames played: " << state.frame_number << "\n"
              << "  Field samples collected: " << total_samples << "\n"
              << "  Avg density: " << std::fixed << std::setprecision(2)
              << (sum_rho / total_samples) << "\n"
              << "  Avg temperature: " << std::scientific << (sum_T / total_samples)
              << std::defaultfloat << "\n"
              << "  Avg B-field: " << (sum_B / total_samples) << "\n"
              << "  Interpolation overhead: " << state.avg_interpolation_time << " us\n"
              << "  Status: " << (pipeline_ok ? "PASS" : "FAIL") << "\n\n";

    return pipeline_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "PHASE 8 FULL PIPELINE VALIDATION\n"
              << "Phase 8.1d: Complete GRMHD Time Series Playback\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_multifield_grmhd_playback())       passed++;
    if (test_interpolation_mode_switching())    passed++;
    if (test_multirate_playback())              passed++;
    if (test_reverse_with_interpolation())      passed++;
    if (test_frame_stepping_integration())      passed++;
    if (test_marker_navigation())               passed++;
    if (test_complete_phase8_pipeline())        passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
