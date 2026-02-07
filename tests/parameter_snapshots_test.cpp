/**
 * @file parameter_snapshots_test.cpp
 * @brief Phase 9.2: Snapshot Management & Parameter History
 *
 * Tests parameter state snapshots, temporal interpolation, and history navigation
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

#include "../src/physics/parameter_snapshots.h"

using namespace physics;

// Test 1: Snapshot creation and restoration
bool test_snapshot_creation_restore() {
    std::cout << "Test 1: Snapshot Creation & Restoration\n";

    SnapshotHistory history = create_snapshot_history();
    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Create first snapshot
    set_global_density_scale(state, 1.0);
    set_global_temperature_scale(state, 1.0);
    uint32_t snap1 = create_snapshot(history, state, 0.0, 0);

    // Modify and create second snapshot
    set_global_density_scale(state, 2.0);
    set_global_temperature_scale(state, 0.5);
    uint32_t snap2 = create_snapshot(history, state, 1.0, 30);

    // Verify snapshot count
    bool creation_ok = (get_snapshot_count(history) == 2) &&
                      (snap1 == 0) && (snap2 == 1);

    // Restore first snapshot
    ParameterAdjustmentState restored;
    restore_snapshot(history, 0, restored);

    bool restore_ok = (std::abs(restored.density_scale - 1.0) < 1e-10) &&
                     (std::abs(restored.temperature_scale - 1.0) < 1e-10);

    bool snapshot_ok = creation_ok && restore_ok;

    std::cout << "  Snapshots created: " << get_snapshot_count(history) << " (expect 2)\n"
              << "  Snapshot 1 index: " << snap1 << "\n"
              << "  Snapshot 2 index: " << snap2 << "\n"
              << "  Restored density scale: " << std::fixed << std::setprecision(2)
              << restored.density_scale << " (expect 1.0)\n"
              << "  Status: " << (snapshot_ok ? "PASS" : "FAIL") << "\n\n";

    return snapshot_ok;
}

// Test 2: Field modifier interpolation
bool test_modifier_interpolation() {
    std::cout << "Test 2: Field Modifier Interpolation\n";

    FieldModifier mod_a = {1.0, 0.0, -1.0, -1.0};
    FieldModifier mod_b = {3.0, 1.0, -1.0, -1.0};

    // Interpolate at alpha=0.5 (midpoint)
    FieldModifier mid = interpolate_modifier(mod_a, mod_b, 0.5);

    // At alpha=0.0 should be mod_a
    FieldModifier at_a = interpolate_modifier(mod_a, mod_b, 0.0);

    // At alpha=1.0 should be mod_b
    FieldModifier at_b = interpolate_modifier(mod_a, mod_b, 1.0);

    bool interp_ok = (std::abs(mid.scale - 2.0) < 1e-10) &&
                    (std::abs(mid.offset - 0.5) < 1e-10) &&
                    (std::abs(at_a.scale - 1.0) < 1e-10) &&
                    (std::abs(at_b.scale - 3.0) < 1e-10);

    std::cout << "  Alpha=0.0: scale=" << std::fixed << std::setprecision(1) << at_a.scale
              << " (expect 1.0)\n"
              << "  Alpha=0.5: scale=" << mid.scale << " (expect 2.0)\n"
              << "  Alpha=1.0: scale=" << at_b.scale << " (expect 3.0)\n"
              << "  Offset at 0.5: " << mid.offset << " (expect 0.5)\n"
              << "  Status: " << (interp_ok ? "PASS" : "FAIL") << "\n\n";

    return interp_ok;
}

// Test 3: Snapshot interpolation between two states
bool test_snapshot_interpolation() {
    std::cout << "Test 3: Snapshot Interpolation\n";

    // Create two snapshots with different parameters
    ParameterSnapshot snap_a;
    snap_a.timestamp = 0.0;
    snap_a.frame_number = 0;
    snap_a.state = create_parameter_adjustment_state();
    set_global_density_scale(snap_a.state, 1.0);

    ParameterSnapshot snap_b;
    snap_b.timestamp = 2.0;
    snap_b.frame_number = 60;
    snap_b.state = create_parameter_adjustment_state();
    set_global_density_scale(snap_b.state, 3.0);

    // Interpolate at t=1.0 (midpoint)
    ParameterAdjustmentState interp = interpolate_snapshots(snap_a, snap_b, 1.0);

    // Should have density_scale = (1.0 + 3.0) / 2 = 2.0
    bool snap_interp_ok = (std::abs(interp.density_scale - 2.0) < 1e-10);

    std::cout << "  Snap A density scale: " << std::fixed << std::setprecision(1)
              << snap_a.state.density_scale << " at t=0.0\n"
              << "  Snap B density scale: " << snap_b.state.density_scale << " at t=2.0\n"
              << "  Interpolated at t=1.0: " << interp.density_scale << " (expect 2.0)\n"
              << "  Status: " << (snap_interp_ok ? "PASS" : "FAIL") << "\n\n";

    return snap_interp_ok;
}

// Test 4: History-based interpolation at arbitrary time
bool test_history_time_interpolation() {
    std::cout << "Test 4: History-Based Time Interpolation\n";

    SnapshotHistory history = create_snapshot_history();

    // Create 3 snapshots
    ParameterAdjustmentState state1 = create_parameter_adjustment_state();
    set_global_density_scale(state1, 1.0);
    create_snapshot(history, state1, 0.0, 0);

    ParameterAdjustmentState state2 = create_parameter_adjustment_state();
    set_global_density_scale(state2, 2.0);
    create_snapshot(history, state2, 1.0, 30);

    ParameterAdjustmentState state3 = create_parameter_adjustment_state();
    set_global_density_scale(state3, 3.0);
    create_snapshot(history, state3, 2.0, 60);

    // Query at times between snapshots
    ParameterAdjustmentState at_0p5, at_1p5;
    get_interpolated_state_at_time(history, 0.5, at_0p5);
    get_interpolated_state_at_time(history, 1.5, at_1p5);

    // at t=0.5: should be 1.5 (midway between 1.0 and 2.0)
    // at t=1.5: should be 2.5 (midway between 2.0 and 3.0)
    bool history_ok = (std::abs(at_0p5.density_scale - 1.5) < 1e-10) &&
                     (std::abs(at_1p5.density_scale - 2.5) < 1e-10);

    std::cout << "  Query at t=0.5: density_scale=" << std::fixed << std::setprecision(1)
              << at_0p5.density_scale << " (expect 1.5)\n"
              << "  Query at t=1.5: density_scale=" << at_1p5.density_scale
              << " (expect 2.5)\n"
              << "  Status: " << (history_ok ? "PASS" : "FAIL") << "\n\n";

    return history_ok;
}

// Test 5: Snapshot navigation (next/previous)
bool test_snapshot_navigation() {
    std::cout << "Test 5: Snapshot Navigation\n";

    SnapshotHistory history = create_snapshot_history();
    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Create 5 snapshots
    for (uint32_t i = 0; i < 5; i++) {
        set_global_density_scale(state, 1.0 + i);
        create_snapshot(history, state, i * 1.0, i * 30);
    }

    // Start at snapshot 2
    history.current_snapshot_idx = 2;

    // Navigate forward
    bool next_ok = go_to_next_snapshot(history, state);
    bool at_3 = (history.current_snapshot_idx == 3);

    // Navigate backward
    bool prev_ok = go_to_previous_snapshot(history, state);
    bool back_at_2 = (history.current_snapshot_idx == 2);

    bool nav_ok = next_ok && prev_ok && at_3 && back_at_2;

    std::cout << "  Total snapshots: " << get_snapshot_count(history) << "\n"
              << "  Started at index: 2\n"
              << "  After next(): " << history.current_snapshot_idx << " (expect 3)\n"
              << "  After previous(): " << history.current_snapshot_idx << " (expect 2)\n"
              << "  Status: " << (nav_ok ? "PASS" : "FAIL") << "\n\n";

    return nav_ok;
}

// Test 6: Find nearest snapshot by time
bool test_find_nearest_snapshot() {
    std::cout << "Test 6: Find Nearest Snapshot\n";

    SnapshotHistory history = create_snapshot_history();
    ParameterAdjustmentState state = create_parameter_adjustment_state();

    // Create snapshots at t = 0.0, 1.0, 2.0, 3.0
    for (uint32_t i = 0; i < 4; i++) {
        create_snapshot(history, state, i * 1.0, i * 30);
    }

    // Query times and find nearest
    uint32_t nearest_0p5 = find_nearest_snapshot(history, 0.5);   // Should be 0 or 1
    uint32_t nearest_1p5 = find_nearest_snapshot(history, 1.5);   // Should be 1 or 2
    uint32_t nearest_2p9 = find_nearest_snapshot(history, 2.9);   // Should be 3

    bool find_ok = (nearest_0p5 <= 1) &&  // Within 0.5 of correct snap
                  (nearest_1p5 >= 1 && nearest_1p5 <= 2) &&
                  (nearest_2p9 == 3);

    std::cout << "  Nearest to t=0.5: snapshot " << nearest_0p5
              << " at t=" << std::fixed << std::setprecision(1)
              << get_snapshot_timestamp(history, nearest_0p5) << "\n"
              << "  Nearest to t=1.5: snapshot " << nearest_1p5
              << " at t=" << get_snapshot_timestamp(history, nearest_1p5) << "\n"
              << "  Nearest to t=2.9: snapshot " << nearest_2p9
              << " at t=" << get_snapshot_timestamp(history, nearest_2p9) << "\n"
              << "  Status: " << (find_ok ? "PASS" : "FAIL") << "\n\n";

    return find_ok;
}

// Test 7: Complete snapshot workflow with history
bool test_complete_snapshot_workflow() {
    std::cout << "Test 7: Complete Snapshot Workflow\n";

    SnapshotHistory history = create_snapshot_history(10.0);  // Max 10 seconds
    ParameterAdjustmentState state = create_parameter_adjustment_state();

    uint32_t snap_count = 0;

    // Simulate interactive session: adjust parameters and save snapshots
    set_global_density_scale(state, 1.0);
    create_snapshot(history, state, 0.0, 0);
    snap_count++;

    // Double density
    set_global_density_scale(state, 2.0);
    create_snapshot(history, state, 1.0, 30);
    snap_count++;

    // Increase temperature
    set_global_temperature_scale(state, 1.5);
    create_snapshot(history, state, 2.0, 60);
    snap_count++;

    // Triple density
    set_global_density_scale(state, 3.0);
    create_snapshot(history, state, 3.0, 90);
    snap_count++;

    // Navigation: go to snap 1, then forward to snap 2
    restore_snapshot(history, 1, state);
    double scale_at_1 = state.density_scale;

    go_to_next_snapshot(history, state);
    double scale_at_2 = state.density_scale;

    // Query interpolated value at t=1.5
    ParameterAdjustmentState at_mid;
    get_interpolated_state_at_time(history, 1.5, at_mid);

    bool workflow_ok = (snap_count == 4) &&
                      (std::abs(scale_at_1 - 2.0) < 1e-10) &&
                      (std::abs(scale_at_2 - 2.0) < 1e-10) &&
                      (std::abs(at_mid.density_scale - 2.0) < 1e-10 ||
                       std::abs(at_mid.density_scale - 2.5) < 1e-10);  // Either 2.0 or interpolated

    std::cout << "  Total snapshots: " << get_snapshot_count(history) << " (expect 4)\n"
              << "  Scale at snapshot 1: " << std::fixed << std::setprecision(1)
              << scale_at_1 << " (expect 2.0)\n"
              << "  Scale at snapshot 2: " << scale_at_2 << " (expect 2.0)\n"
              << "  Interpolated at t=1.5: " << at_mid.density_scale << "\n"
              << "  Status: " << (workflow_ok ? "PASS" : "FAIL") << "\n\n";

    return workflow_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "PARAMETER SNAPSHOT & HISTORY VALIDATION\n"
              << "Phase 9.2: Snapshot Management & Parameter History\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_snapshot_creation_restore())    passed++;
    if (test_modifier_interpolation())       passed++;
    if (test_snapshot_interpolation())       passed++;
    if (test_history_time_interpolation())   passed++;
    if (test_snapshot_navigation())          passed++;
    if (test_find_nearest_snapshot())        passed++;
    if (test_complete_snapshot_workflow())   passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
