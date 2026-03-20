/**
 * @file parameter_snapshots_test.cpp
 * @brief Phase 9.2: Snapshot Management & Parameter History
 *
 * Tests parameter state snapshots, temporal interpolation, and history navigation
 */

#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>

#include "../src/physics/parameter_snapshots.h"
#include "parameter_adjustment.h"
#include "physics/parameter_adjustment.h"

using namespace physics;

// Test 1: Snapshot creation and restoration
namespace {

bool testSnapshotCreationRestore() {
  std::cout << "Test 1: Snapshot Creation & Restoration\n";

  SnapshotHistory history = createSnapshotHistory();
  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Create first snapshot
  setGlobalDensityScale(state, 1.0);
  setGlobalTemperatureScale(state, 1.0);
  uint32_t const snap1 = createSnapshot(history, state, 0.0, 0);

  // Modify and create second snapshot
  setGlobalDensityScale(state, 2.0);
  setGlobalTemperatureScale(state, 0.5);
  uint32_t const snap2 = createSnapshot(history, state, 1.0, 30);

  // Verify snapshot count
  bool const creationOk = (getSnapshotCount(history) == 2) && (snap1 == 0) && (snap2 == 1);

  // Restore first snapshot
  ParameterAdjustmentState restored;
  (void)restoreSnapshot(history, 0, restored);

  bool const restoreOk = (std::abs(restored.densityScale - 1.0) < 1e-10) &&
                         (std::abs(restored.temperatureScale - 1.0) < 1e-10);

  bool const snapshotOk = creationOk && restoreOk;

  std::cout << "  Snapshots created: " << getSnapshotCount(history) << " (expect 2)\n"
            << "  Snapshot 1 index: " << snap1 << "\n"
            << "  Snapshot 2 index: " << snap2 << "\n"
            << "  Restored density scale: " << std::fixed << std::setprecision(2)
            << restored.densityScale << " (expect 1.0)\n"
            << "  Status: " << (snapshotOk ? "PASS" : "FAIL") << "\n\n";

  return snapshotOk;
}

// Test 2: Field modifier interpolation
bool testModifierInterpolation() {
  std::cout << "Test 2: Field Modifier Interpolation\n";

  FieldModifier const modA = {.scale = 1.0, .offset = 0.0, .clampMin = -1.0, .clampMax = -1.0};
  FieldModifier const modB = {.scale = 3.0, .offset = 1.0, .clampMin = -1.0, .clampMax = -1.0};

  // Interpolate at alpha=0.5 (midpoint)
  FieldModifier const mid = interpolateModifier(modA, modB, 0.5);

  // At alpha=0.0 should be mod_a
  FieldModifier const atA = interpolateModifier(modA, modB, 0.0);

  // At alpha=1.0 should be mod_b
  FieldModifier const atB = interpolateModifier(modA, modB, 1.0);

  bool const interpOk = (std::abs(mid.scale - 2.0) < 1e-10) &&
                        (std::abs(mid.offset - 0.5) < 1e-10) &&
                        (std::abs(atA.scale - 1.0) < 1e-10) && (std::abs(atB.scale - 3.0) < 1e-10);

  std::cout << "  Alpha=0.0: scale=" << std::fixed << std::setprecision(1) << atA.scale
            << " (expect 1.0)\n"
            << "  Alpha=0.5: scale=" << mid.scale << " (expect 2.0)\n"
            << "  Alpha=1.0: scale=" << atB.scale << " (expect 3.0)\n"
            << "  Offset at 0.5: " << mid.offset << " (expect 0.5)\n"
            << "  Status: " << (interpOk ? "PASS" : "FAIL") << "\n\n";

  return interpOk;
}

// Test 3: Snapshot interpolation between two states
bool testSnapshotInterpolation() {
  std::cout << "Test 3: Snapshot Interpolation\n";

  // Create two snapshots with different parameters
  ParameterSnapshot snapA;
  snapA.timestamp = 0.0;
  snapA.frameNumber = 0;
  snapA.state = createParameterAdjustmentState();
  setGlobalDensityScale(snapA.state, 1.0);

  ParameterSnapshot snapB;
  snapB.timestamp = 2.0;
  snapB.frameNumber = 60;
  snapB.state = createParameterAdjustmentState();
  setGlobalDensityScale(snapB.state, 3.0);

  // Interpolate at t=1.0 (midpoint)
  ParameterAdjustmentState const interp = interpolateSnapshots(snapA, snapB, 1.0);

  // Should have density_scale = (1.0 + 3.0) / 2 = 2.0
  bool const snapInterpOk = (std::abs(interp.densityScale - 2.0) < 1e-10);

  std::cout << "  Snap A density scale: " << std::fixed << std::setprecision(1)
            << snapA.state.densityScale << " at t=0.0\n"
            << "  Snap B density scale: " << snapB.state.densityScale << " at t=2.0\n"
            << "  Interpolated at t=1.0: " << interp.densityScale << " (expect 2.0)\n"
            << "  Status: " << (snapInterpOk ? "PASS" : "FAIL") << "\n\n";

  return snapInterpOk;
}

// Test 4: History-based interpolation at arbitrary time
bool testHistoryTimeInterpolation() {
  std::cout << "Test 4: History-Based Time Interpolation\n";

  SnapshotHistory history = createSnapshotHistory();

  // Create 3 snapshots
  ParameterAdjustmentState state1 = createParameterAdjustmentState();
  setGlobalDensityScale(state1, 1.0);
  (void)createSnapshot(history, state1, 0.0, 0);

  ParameterAdjustmentState state2 = createParameterAdjustmentState();
  setGlobalDensityScale(state2, 2.0);
  (void)createSnapshot(history, state2, 1.0, 30);

  ParameterAdjustmentState state3 = createParameterAdjustmentState();
  setGlobalDensityScale(state3, 3.0);
  (void)createSnapshot(history, state3, 2.0, 60);

  // Query at times between snapshots
  ParameterAdjustmentState at0p5;
  ParameterAdjustmentState at1p5;
  (void)getInterpolatedStateAtTime(history, 0.5, at0p5);
  (void)getInterpolatedStateAtTime(history, 1.5, at1p5);

  // at t=0.5: should be 1.5 (midway between 1.0 and 2.0)
  // at t=1.5: should be 2.5 (midway between 2.0 and 3.0)
  bool const historyOk =
      (std::abs(at0p5.densityScale - 1.5) < 1e-10) && (std::abs(at1p5.densityScale - 2.5) < 1e-10);

  std::cout << "  Query at t=0.5: density_scale=" << std::fixed << std::setprecision(1)
            << at0p5.densityScale << " (expect 1.5)\n"
            << "  Query at t=1.5: density_scale=" << at1p5.densityScale << " (expect 2.5)\n"
            << "  Status: " << (historyOk ? "PASS" : "FAIL") << "\n\n";

  return historyOk;
}

// Test 5: Snapshot navigation (next/previous)
bool testSnapshotNavigation() {
  std::cout << "Test 5: Snapshot Navigation\n";

  SnapshotHistory history = createSnapshotHistory();
  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Create 5 snapshots
  for (uint32_t i = 0; i < 5; i++) {
    setGlobalDensityScale(state, 1.0 + i);
    (void)createSnapshot(history, state, i * 1.0, i * 30);
  }

  // Start at snapshot 2
  history.currentSnapshotIdx = 2;

  // Navigate forward
  bool const nextOk = goToNextSnapshot(history, state);
  bool const at3 = (history.currentSnapshotIdx == 3);

  // Navigate backward
  bool const prevOk = goToPreviousSnapshot(history, state);
  bool const backAt2 = (history.currentSnapshotIdx == 2);

  bool const navOk = nextOk && prevOk && at3 && backAt2;

  std::cout << "  Total snapshots: " << getSnapshotCount(history) << "\n"
            << "  Started at index: 2\n"
            << "  After next(): " << history.currentSnapshotIdx << " (expect 3)\n"
            << "  After previous(): " << history.currentSnapshotIdx << " (expect 2)\n"
            << "  Status: " << (navOk ? "PASS" : "FAIL") << "\n\n";

  return navOk;
}

// Test 6: Find nearest snapshot by time
bool testFindNearestSnapshot() {
  std::cout << "Test 6: Find Nearest Snapshot\n";

  SnapshotHistory history = createSnapshotHistory();
  ParameterAdjustmentState const state = createParameterAdjustmentState();

  // Create snapshots at t = 0.0, 1.0, 2.0, 3.0
  for (uint32_t i = 0; i < 4; i++) {
    (void)createSnapshot(history, state, i * 1.0, i * 30);
  }

  // Query times and find nearest
  uint32_t const nearest0p5 = findNearestSnapshot(history, 0.5); // Should be 0 or 1
  uint32_t const nearest1p5 = findNearestSnapshot(history, 1.5); // Should be 1 or 2
  uint32_t const nearest2p9 = findNearestSnapshot(history, 2.9); // Should be 3

  bool const findOk = (nearest0p5 <= 1) && // Within 0.5 of correct snap
                      (nearest1p5 >= 1 && nearest1p5 <= 2) && (nearest2p9 == 3);

  std::cout << "  Nearest to t=0.5: snapshot " << nearest0p5 << " at t=" << std::fixed
            << std::setprecision(1) << getSnapshotTimestamp(history, nearest0p5) << "\n"
            << "  Nearest to t=1.5: snapshot " << nearest1p5
            << " at t=" << getSnapshotTimestamp(history, nearest1p5) << "\n"
            << "  Nearest to t=2.9: snapshot " << nearest2p9
            << " at t=" << getSnapshotTimestamp(history, nearest2p9) << "\n"
            << "  Status: " << (findOk ? "PASS" : "FAIL") << "\n\n";

  return findOk;
}

// Test 7: Complete snapshot workflow with history
bool testCompleteSnapshotWorkflow() {
  std::cout << "Test 7: Complete Snapshot Workflow\n";

  SnapshotHistory history = createSnapshotHistory(10.0); // Max 10 seconds
  ParameterAdjustmentState state = createParameterAdjustmentState();

  uint32_t snapCount = 0;

  // Simulate interactive session: adjust parameters and save snapshots
  setGlobalDensityScale(state, 1.0);
  (void)createSnapshot(history, state, 0.0, 0);
  snapCount++;

  // Double density
  setGlobalDensityScale(state, 2.0);
  (void)createSnapshot(history, state, 1.0, 30);
  snapCount++;

  // Increase temperature
  setGlobalTemperatureScale(state, 1.5);
  (void)createSnapshot(history, state, 2.0, 60);
  snapCount++;

  // Triple density
  setGlobalDensityScale(state, 3.0);
  (void)createSnapshot(history, state, 3.0, 90);
  snapCount++;

  // Navigation: go to snap 1, then forward to snap 2
  (void)restoreSnapshot(history, 1, state);
  double const scaleAt1 = state.densityScale;

  (void)goToNextSnapshot(history, state);
  const double scaleAt2 = state.densityScale;

  // Query interpolated value at t=1.5
  ParameterAdjustmentState atMid;
  (void)getInterpolatedStateAtTime(history, 1.5, atMid);

  bool const workflowOk =
      (snapCount == 4) && (std::abs(scaleAt1 - 2.0) < 1e-10) &&
      (std::abs(scaleAt2 - 2.0) < 1e-10) &&
      (std::abs(atMid.densityScale - 2.0) < 1e-10 ||
       std::abs(atMid.densityScale - 2.5) < 1e-10); // Either 2.0 or interpolated

  std::cout << "  Total snapshots: " << getSnapshotCount(history) << " (expect 4)\n"
            << "  Scale at snapshot 1: " << std::fixed << std::setprecision(1) << scaleAt1
            << " (expect 2.0)\n"
            << "  Scale at snapshot 2: " << scaleAt2 << " (expect 2.0)\n"
            << "  Interpolated at t=1.5: " << atMid.densityScale << "\n"
            << "  Status: " << (workflowOk ? "PASS" : "FAIL") << "\n\n";

  return workflowOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "PARAMETER SNAPSHOT & HISTORY VALIDATION\n"
              << "Phase 9.2: Snapshot Management & Parameter History\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 7;

    if (testSnapshotCreationRestore()) {
      passed++;
    }
    if (testModifierInterpolation()) {
      passed++;
    }
    if (testSnapshotInterpolation()) {
      passed++;
    }
    if (testHistoryTimeInterpolation()) {
      passed++;
    }
    if (testSnapshotNavigation()) {
      passed++;
    }
    if (testFindNearestSnapshot()) {
      passed++;
    }
    if (testCompleteSnapshotWorkflow()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
