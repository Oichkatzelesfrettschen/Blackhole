/**
 * @file parameter_adjustment_test.cpp
 * @brief Phase 9.1: Real-time Parameter Adjustment & Multi-Sequence Sync
 *
 * Tests live field modification, global scaling, and synchronized playback
 * across multiple GRMHD sequences
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

#include "../src/physics/parameter_adjustment.h"

using namespace physics;

// Test 1: Field modifier application
bool test_field_modifier_application() {
    std::cout << "Test 1: Field Modifier Application\n";

    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Set density modifier: scale by 2.0, offset by 0.5
    set_density_modifier(state, 2.0, 0.5, 0.0, 10.0);

    // Test with various raw values
    double raw_1 = 1.0;
    double raw_5 = 5.0;
    double raw_10 = 10.0;

    double adj_1 = adjust_density(raw_1, state);  // 1.0 * 2.0 + 0.5 = 2.5
    double adj_5 = adjust_density(raw_5, state);  // 5.0 * 2.0 + 0.5 = 10.5 -> clamped to 10.0
    double adj_10 = adjust_density(raw_10, state); // 10.0 * 2.0 + 0.5 = 20.5 -> clamped to 10.0

    bool modifier_ok = (std::abs(adj_1 - 2.5) < 1e-10) &&
                      (std::abs(adj_5 - 10.0) < 1e-10) &&
                      (std::abs(adj_10 - 10.0) < 1e-10);

    std::cout << "  Input 1.0 -> " << std::fixed << std::setprecision(2) << adj_1 << " (expect 2.5)\n"
              << "  Input 5.0 -> " << adj_5 << " (expect 10.0, clamped)\n"
              << "  Input 10.0 -> " << adj_10 << " (expect 10.0, clamped)\n"
              << "  Status: " << (modifier_ok ? "PASS" : "FAIL") << "\n\n";

    return modifier_ok;
}

// Test 2: Global field scaling
bool test_global_field_scaling() {
    std::cout << "Test 2: Global Field Scaling\n";

    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Set global density and temperature scales
    set_global_density_scale(state, 0.5);      // 50% density
    set_global_temperature_scale(state, 2.0);  // 2x temperature

    // Test adjustment without per-field modifiers
    double raw_density = 10.0;
    double raw_temp = 1e7;

    double adj_density = adjust_density(raw_density, state);   // 10.0 * 0.5 = 5.0
    double adj_temp = adjust_temperature(raw_temp, state);     // 1e7 * 2.0 = 2e7

    bool scaling_ok = (std::abs(adj_density - 5.0) < 1e-10) &&
                     (std::abs(adj_temp - 2e7) < 1e-5);

    std::cout << "  Density 10.0 with 0.5 scale -> " << std::fixed << std::setprecision(1)
              << adj_density << " (expect 5.0)\n"
              << "  Temp 1e7 with 2.0 scale -> " << std::scientific << adj_temp
              << std::defaultfloat << " (expect 2e7)\n"
              << "  Status: " << (scaling_ok ? "PASS" : "FAIL") << "\n\n";

    return scaling_ok;
}

// Test 3: Multi-field adjustment with independent modifiers
bool test_multifield_adjustment() {
    std::cout << "Test 3: Multi-Field Adjustment\n";

    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Set different modifiers for each field
    set_density_modifier(state, 1.5, 0.1);           // 1.5x + 0.1
    set_temperature_modifier(state, 0.8, 1e6);       // 0.8x + 1e6
    set_magnetic_field_modifier(state, 2.0, -10.0);  // 2.0x - 10.0

    // Adjust global scales too
    set_global_density_scale(state, 1.0);      // No global scale
    set_global_temperature_scale(state, 1.0);

    // Test each field independently
    double rho = adjust_density(1.0, state);        // 1.0 * 1.0 * 1.5 + 0.1 = 1.6
    double T = adjust_temperature(1e7, state);      // 1e7 * 1.0 * 0.8 + 1e6 = 9e6
    double B = adjust_magnetic_field(50.0, state);  // 50.0 * 2.0 - 10.0 = 90.0

    bool multifield_ok = (std::abs(rho - 1.6) < 1e-10) &&
                        (std::abs(T - 9e6) < 1e2) &&
                        (std::abs(B - 90.0) < 1e-10);

    std::cout << "  Density (1.0 input): " << std::fixed << std::setprecision(2) << rho << " (expect 1.6)\n"
              << "  Temperature (1e7 input): " << std::scientific << T << std::defaultfloat
              << " (expect 9e6)\n"
              << "  B-field (50.0 input): " << B << " (expect 90.0)\n"
              << "  Status: " << (multifield_ok ? "PASS" : "FAIL") << "\n\n";

    return multifield_ok;
}

// Test 4: Clamping and bounds checking
bool test_clamping_bounds() {
    std::cout << "Test 4: Clamping and Bounds Checking\n";

    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Set modifier with aggressive clamping
    set_density_modifier(state, 3.0, -1.0, 0.5, 2.0);  // Scale 3x, offset -1, clamp [0.5, 2.0]

    double val1 = adjust_density(0.1, state);  // 0.1 * 3.0 - 1.0 = -0.7 -> clamped to 0.5
    double val2 = adjust_density(0.5, state);  // 0.5 * 3.0 - 1.0 = 0.5 (in range)
    double val3 = adjust_density(1.5, state);  // 1.5 * 3.0 - 1.0 = 3.5 -> clamped to 2.0

    bool clamp_ok = (std::abs(val1 - 0.5) < 1e-10) &&
                   (std::abs(val2 - 0.5) < 1e-10) &&
                   (std::abs(val3 - 2.0) < 1e-10);

    std::cout << "  Input 0.1 -> " << std::fixed << std::setprecision(2) << val1
              << " (expect 0.5, min clamp)\n"
              << "  Input 0.5 -> " << val2 << " (expect 0.5, in range)\n"
              << "  Input 1.5 -> " << val3 << " (expect 2.0, max clamp)\n"
              << "  Status: " << (clamp_ok ? "PASS" : "FAIL") << "\n\n";

    return clamp_ok;
}

// Test 5: Parameter adjustments enable/disable
bool test_adjustment_enable_disable() {
    std::cout << "Test 5: Adjustment Enable/Disable\n";

    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Set modifiers
    set_density_modifier(state, 2.0, 0.0);

    double raw = 5.0;

    // Adjustments enabled
    set_adjustments_enabled(state, true);
    double adj_enabled = adjust_density(raw, state);  // 5.0 * 2.0 = 10.0

    // Adjustments disabled
    set_adjustments_enabled(state, false);
    double adj_disabled = adjust_density(raw, state);  // Should return raw value

    bool enable_ok = (std::abs(adj_enabled - 10.0) < 1e-10) &&
                    (std::abs(adj_disabled - 5.0) < 1e-10);

    std::cout << "  With adjustments enabled: " << std::fixed << std::setprecision(1)
              << adj_enabled << " (expect 10.0)\n"
              << "  With adjustments disabled: " << adj_disabled << " (expect 5.0)\n"
              << "  Status: " << (enable_ok ? "PASS" : "FAIL") << "\n\n";

    return enable_ok;
}

// Test 6: Multi-sequence synchronization
bool test_multisequence_sync() {
    std::cout << "Test 6: Multi-Sequence Synchronization\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = build_timeseries_metadata(times.data(),
                                                      static_cast<uint32_t>(times.size()));

    // Create 3 playback states for 3 sequences
    AdvancedPlaybackState state1 = create_advanced_playback_state(ts, 1.0);
    AdvancedPlaybackState state2 = create_advanced_playback_state(ts, 1.0);
    AdvancedPlaybackState state3 = create_advanced_playback_state(ts, 1.0);

    // Create sync group
    SynchronizedPlaybackGroup group = create_sync_group();
    add_to_sync_group(group, &state1);
    add_to_sync_group(group, &state2);
    add_to_sync_group(group, &state3);

    // Set all to forward mode
    set_playback_mode(state1, PlaybackMode::Forward);
    set_playback_mode(state2, PlaybackMode::Forward);
    set_playback_mode(state3, PlaybackMode::Forward);

    // Sync all to t=1.5
    sync_seek_all(group, ts, 1.5);

    // Verify all are at same time
    bool sync_ok = (std::abs(state1.t_current - 1.5) < 1e-10) &&
                  (std::abs(state2.t_current - 1.5) < 1e-10) &&
                  (std::abs(state3.t_current - 1.5) < 1e-10) &&
                  (group.n_sequences == 3) &&
                  (std::abs(group.master_time - 1.5) < 1e-10);

    std::cout << "  Synchronized " << group.n_sequences << " sequences\n"
              << "  State 1 at t=" << std::fixed << std::setprecision(2) << state1.t_current << "\n"
              << "  State 2 at t=" << state2.t_current << "\n"
              << "  State 3 at t=" << state3.t_current << "\n"
              << "  Master time: " << group.master_time << "\n"
              << "  Status: " << (sync_ok ? "PASS" : "FAIL") << "\n\n";

    return sync_ok;
}

// Test 7: Complete parameter adjustment session
bool test_complete_adjustment_session() {
    std::cout << "Test 7: Complete Parameter Adjustment Session\n";

    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Session: adjust fields progressively
    set_global_density_scale(state, 1.0);
    set_global_temperature_scale(state, 1.0);

    // Step 1: Double density
    set_density_modifier(state, 2.0, 0.0);
    double rho_1 = adjust_density(1.0, state);  // 2.0

    // Step 2: Increase temperature by 50%
    set_temperature_modifier(state, 1.5, 0.0);
    double T_1 = adjust_temperature(1e7, state);  // 1.5e7

    // Step 3: Reduce B-field by 20%
    set_magnetic_field_modifier(state, 0.8, 0.0);
    double B_1 = adjust_magnetic_field(100.0, state);  // 80.0

    // Step 4: Add constraints
    set_density_modifier(state, 2.0, 0.0, 1.0, 3.0);

    // Step 5: Global scale on top
    set_global_density_scale(state, 0.5);
    double rho_2 = adjust_density(1.0, state);  // 1.0 * 0.5 * 2.0 = 1.0

    // Step 6: Disable all adjustments
    set_adjustments_enabled(state, false);
    double rho_3 = adjust_density(1.0, state);  // Returns raw 1.0

    bool session_ok = (std::abs(rho_1 - 2.0) < 1e-10) &&
                     (std::abs(T_1 - 1.5e7) < 1e4) &&
                     (std::abs(B_1 - 80.0) < 1e-10) &&
                     (std::abs(rho_2 - 1.0) < 1e-10) &&
                     (std::abs(rho_3 - 1.0) < 1e-10);

    std::cout << "  Step 1 - Double density: " << std::fixed << std::setprecision(1) << rho_1 << " (expect 2.0)\n"
              << "  Step 2 - 1.5x temperature: " << std::scientific << T_1 << std::defaultfloat
              << " (expect 1.5e7)\n"
              << "  Step 3 - 0.8x B-field: " << B_1 << " (expect 80.0)\n"
              << "  Step 4+5 - With global scale: " << rho_2 << " (expect 1.0)\n"
              << "  Step 6 - Disabled: " << rho_3 << " (expect 1.0)\n"
              << "  Status: " << (session_ok ? "PASS" : "FAIL") << "\n\n";

    return session_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "REAL-TIME PARAMETER ADJUSTMENT VALIDATION\n"
              << "Phase 9.1: Parameter Adjustment & Multi-Sequence Sync\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_field_modifier_application())   passed++;
    if (test_global_field_scaling())         passed++;
    if (test_multifield_adjustment())        passed++;
    if (test_clamping_bounds())              passed++;
    if (test_adjustment_enable_disable())    passed++;
    if (test_multisequence_sync())           passed++;
    if (test_complete_adjustment_session())  passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
