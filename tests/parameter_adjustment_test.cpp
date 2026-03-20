/**
 * @file parameter_adjustment_test.cpp
 * @brief Phase 9.1: Real-time Parameter Adjustment & Multi-Sequence Sync
 *
 * Tests live field modification, global scaling, and synchronized playback
 * across multiple GRMHD sequences
 */

#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>

#include "../src/physics/parameter_adjustment.h"
#include "physics/playback_control.h"
#include "physics/timeseries_interpolation.h"
#include "playback_control.h"
#include "timeseries_interpolation.h"

using namespace physics;

// Test 1: Field modifier application
namespace {

bool testFieldModifierApplication() {
  std::cout << "Test 1: Field Modifier Application\n";

  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Set density modifier: scale by 2.0, offset by 0.5
  setDensityModifier(state, 2.0, 0.5, 0.0, 10.0);

  // Test with various raw values
  double const raw1 = 1.0;
  double const raw5 = 5.0;
  double const raw10 = 10.0;

  double const adj1 = adjustDensity(raw1, state);   // 1.0 * 2.0 + 0.5 = 2.5
  double const adj5 = adjustDensity(raw5, state);   // 5.0 * 2.0 + 0.5 = 10.5 -> clamped to 10.0
  double const adj10 = adjustDensity(raw10, state); // 10.0 * 2.0 + 0.5 = 20.5 -> clamped to 10.0

  bool const modifierOk = (std::abs(adj1 - 2.5) < 1e-10) && (std::abs(adj5 - 10.0) < 1e-10) &&
                          (std::abs(adj10 - 10.0) < 1e-10);

  std::cout << "  Input 1.0 -> " << std::fixed << std::setprecision(2) << adj1 << " (expect 2.5)\n"
            << "  Input 5.0 -> " << adj5 << " (expect 10.0, clamped)\n"
            << "  Input 10.0 -> " << adj10 << " (expect 10.0, clamped)\n"
            << "  Status: " << (modifierOk ? "PASS" : "FAIL") << "\n\n";

  return modifierOk;
}

// Test 2: Global field scaling
bool testGlobalFieldScaling() {
  std::cout << "Test 2: Global Field Scaling\n";

  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Set global density and temperature scales
  setGlobalDensityScale(state, 0.5);     // 50% density
  setGlobalTemperatureScale(state, 2.0); // 2x temperature

  // Test adjustment without per-field modifiers
  double const rawDensity = 10.0;
  double const rawTemp = 1e7;

  double const adjDensity = adjustDensity(rawDensity, state); // 10.0 * 0.5 = 5.0
  double const adjTemp = adjustTemperature(rawTemp, state);   // 1e7 * 2.0 = 2e7

  bool const scalingOk = (std::abs(adjDensity - 5.0) < 1e-10) && (std::abs(adjTemp - 2e7) < 1e-5);

  std::cout << "  Density 10.0 with 0.5 scale -> " << std::fixed << std::setprecision(1)
            << adjDensity << " (expect 5.0)\n"
            << "  Temp 1e7 with 2.0 scale -> " << std::scientific << adjTemp << std::defaultfloat
            << " (expect 2e7)\n"
            << "  Status: " << (scalingOk ? "PASS" : "FAIL") << "\n\n";

  return scalingOk;
}

// Test 3: Multi-field adjustment with independent modifiers
bool testMultifieldAdjustment() {
  std::cout << "Test 3: Multi-Field Adjustment\n";

  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Set different modifiers for each field
  setDensityModifier(state, 1.5, 0.1);         // 1.5x + 0.1
  setTemperatureModifier(state, 0.8, 1e6);     // 0.8x + 1e6
  setMagneticFieldModifier(state, 2.0, -10.0); // 2.0x - 10.0

  // Adjust global scales too
  setGlobalDensityScale(state, 1.0); // No global scale
  setGlobalTemperatureScale(state, 1.0);

  // Test each field independently
  double const rho = adjustDensity(1.0, state);      // 1.0 * 1.0 * 1.5 + 0.1 = 1.6
  double const t = adjustTemperature(1e7, state);    // 1e7 * 1.0 * 0.8 + 1e6 = 9e6
  double const b = adjustMagneticField(50.0, state); // 50.0 * 2.0 - 10.0 = 90.0

  bool const multifieldOk =
      (std::abs(rho - 1.6) < 1e-10) && (std::abs(t - 9e6) < 1e2) && (std::abs(b - 90.0) < 1e-10);

  std::cout << "  Density (1.0 input): " << std::fixed << std::setprecision(2) << rho
            << " (expect 1.6)\n"
            << "  Temperature (1e7 input): " << std::scientific << t << std::defaultfloat
            << " (expect 9e6)\n"
            << "  B-field (50.0 input): " << b << " (expect 90.0)\n"
            << "  Status: " << (multifieldOk ? "PASS" : "FAIL") << "\n\n";

  return multifieldOk;
}

// Test 4: Clamping and bounds checking
bool testClampingBounds() {
  std::cout << "Test 4: Clamping and Bounds Checking\n";

  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Set modifier with aggressive clamping
  setDensityModifier(state, 3.0, -1.0, 0.5, 2.0); // Scale 3x, offset -1, clamp [0.5, 2.0]

  double const val1 = adjustDensity(0.1, state); // 0.1 * 3.0 - 1.0 = -0.7 -> clamped to 0.5
  double const val2 = adjustDensity(0.5, state); // 0.5 * 3.0 - 1.0 = 0.5 (in range)
  double const val3 = adjustDensity(1.5, state); // 1.5 * 3.0 - 1.0 = 3.5 -> clamped to 2.0

  bool const clampOk = (std::abs(val1 - 0.5) < 1e-10) && (std::abs(val2 - 0.5) < 1e-10) &&
                       (std::abs(val3 - 2.0) < 1e-10);

  std::cout << "  Input 0.1 -> " << std::fixed << std::setprecision(2) << val1
            << " (expect 0.5, min clamp)\n"
            << "  Input 0.5 -> " << val2 << " (expect 0.5, in range)\n"
            << "  Input 1.5 -> " << val3 << " (expect 2.0, max clamp)\n"
            << "  Status: " << (clampOk ? "PASS" : "FAIL") << "\n\n";

  return clampOk;
}

// Test 5: Parameter adjustments enable/disable
bool testAdjustmentEnableDisable() {
  std::cout << "Test 5: Adjustment Enable/Disable\n";

  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Set modifiers
  setDensityModifier(state, 2.0, 0.0);

  double const raw = 5.0;

  // Adjustments enabled
  setAdjustmentsEnabled(state, true);
  double const adjEnabled = adjustDensity(raw, state); // 5.0 * 2.0 = 10.0

  // Adjustments disabled
  setAdjustmentsEnabled(state, false);
  double const adjDisabled = adjustDensity(raw, state); // Should return raw value

  bool const enableOk =
      (std::abs(adjEnabled - 10.0) < 1e-10) && (std::abs(adjDisabled - 5.0) < 1e-10);

  std::cout << "  With adjustments enabled: " << std::fixed << std::setprecision(1) << adjEnabled
            << " (expect 10.0)\n"
            << "  With adjustments disabled: " << adjDisabled << " (expect 5.0)\n"
            << "  Status: " << (enableOk ? "PASS" : "FAIL") << "\n\n";

  return enableOk;
}

// Test 6: Multi-sequence synchronization
bool testMultisequenceSync() {
  std::cout << "Test 6: Multi-Sequence Synchronization\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Create 3 playback states for 3 sequences
  AdvancedPlaybackState state1 = createAdvancedPlaybackState(ts, 1.0);
  AdvancedPlaybackState state2 = createAdvancedPlaybackState(ts, 1.0);
  AdvancedPlaybackState state3 = createAdvancedPlaybackState(ts, 1.0);

  // Create sync group
  SynchronizedPlaybackGroup group = createSyncGroup();
  (void)addToSyncGroup(group, &state1);
  (void)addToSyncGroup(group, &state2);
  (void)addToSyncGroup(group, &state3);

  // Set all to forward mode
  setPlaybackMode(state1, PlaybackMode::Forward);
  setPlaybackMode(state2, PlaybackMode::Forward);
  setPlaybackMode(state3, PlaybackMode::Forward);

  // Sync all to t=1.5
  syncSeekAll(group, ts, 1.5);

  // Verify all are at same time
  bool const syncOk = (std::abs(state1.tCurrent - 1.5) < 1e-10) &&
                      (std::abs(state2.tCurrent - 1.5) < 1e-10) &&
                      (std::abs(state3.tCurrent - 1.5) < 1e-10) && (group.nSequences == 3) &&
                      (std::abs(group.masterTime - 1.5) < 1e-10);

  std::cout << "  Synchronized " << group.nSequences << " sequences\n"
            << "  State 1 at t=" << std::fixed << std::setprecision(2) << state1.tCurrent << "\n"
            << "  State 2 at t=" << state2.tCurrent << "\n"
            << "  State 3 at t=" << state3.tCurrent << "\n"
            << "  Master time: " << group.masterTime << "\n"
            << "  Status: " << (syncOk ? "PASS" : "FAIL") << "\n\n";

  return syncOk;
}

// Test 7: Complete parameter adjustment session
bool testCompleteAdjustmentSession() {
  std::cout << "Test 7: Complete Parameter Adjustment Session\n";

  ParameterAdjustmentState state = createParameterAdjustmentState();

  // Session: adjust fields progressively
  setGlobalDensityScale(state, 1.0);
  setGlobalTemperatureScale(state, 1.0);

  // Step 1: Double density
  setDensityModifier(state, 2.0, 0.0);
  double const rho1 = adjustDensity(1.0, state); // 2.0

  // Step 2: Increase temperature by 50%
  setTemperatureModifier(state, 1.5, 0.0);
  double const t1 = adjustTemperature(1e7, state); // 1.5e7

  // Step 3: Reduce B-field by 20%
  setMagneticFieldModifier(state, 0.8, 0.0);
  double const b1 = adjustMagneticField(100.0, state); // 80.0

  // Step 4: Add constraints
  setDensityModifier(state, 2.0, 0.0, 1.0, 3.0);

  // Step 5: Global scale on top
  setGlobalDensityScale(state, 0.5);
  double const rho2 = adjustDensity(1.0, state); // 1.0 * 0.5 * 2.0 = 1.0

  // Step 6: Disable all adjustments
  setAdjustmentsEnabled(state, false);
  double const rho3 = adjustDensity(1.0, state); // Returns raw 1.0

  bool const sessionOk = (std::abs(rho1 - 2.0) < 1e-10) && (std::abs(t1 - 1.5e7) < 1e4) &&
                         (std::abs(b1 - 80.0) < 1e-10) && (std::abs(rho2 - 1.0) < 1e-10) &&
                         (std::abs(rho3 - 1.0) < 1e-10);

  std::cout << "  Step 1 - Double density: " << std::fixed << std::setprecision(1) << rho1
            << " (expect 2.0)\n"
            << "  Step 2 - 1.5x temperature: " << std::scientific << t1 << std::defaultfloat
            << " (expect 1.5e7)\n"
            << "  Step 3 - 0.8x B-field: " << b1 << " (expect 80.0)\n"
            << "  Step 4+5 - With global scale: " << rho2 << " (expect 1.0)\n"
            << "  Step 6 - Disabled: " << rho3 << " (expect 1.0)\n"
            << "  Status: " << (sessionOk ? "PASS" : "FAIL") << "\n\n";

  return sessionOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "REAL-TIME PARAMETER ADJUSTMENT VALIDATION\n"
              << "Phase 9.1: Parameter Adjustment & Multi-Sequence Sync\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 7;

    if (testFieldModifierApplication()) {
      passed++;
    }
    if (testGlobalFieldScaling()) {
      passed++;
    }
    if (testMultifieldAdjustment()) {
      passed++;
    }
    if (testClampingBounds()) {
      passed++;
    }
    if (testAdjustmentEnableDisable()) {
      passed++;
    }
    if (testMultisequenceSync()) {
      passed++;
    }
    if (testCompleteAdjustmentSession()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
