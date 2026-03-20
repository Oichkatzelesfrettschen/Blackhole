/**
 * @file temporal_grmhd_sampling_test.cpp
 * @brief Phase 8.1b: Temporal GRMHD Field Sampling & Interpolation
 *
 * Validates sampling of GRMHD fields at arbitrary times by interpolating between dumps
 */

#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

#include "../src/physics/timeseries_interpolation.h"

using namespace physics;

// Test 1: GRMHD field time evolution
namespace {

bool testGrmhdFieldEvolution() {
  std::cout << "Test 1: GRMHD Field Time Evolution\n";

  // Simulate 10 dumps of GRMHD density field
  std::vector<double> times;
  std::vector<double> rhoField;

  for (int i = 0; i < 10; i++) {
    times.push_back(i * 0.1);
    // Density evolves sinusoidally
    rhoField.push_back(1.0 + (0.5 * std::sin(i * 0.628)));
  }

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Sample at multiple times
  double const rho0 = interpolateField(ts, rhoField.data(), 0.0, false);
  double const rhoMid = interpolateField(ts, rhoField.data(), 0.45, false);
  double const rhoEnd = interpolateField(ts, rhoField.data(), 0.9, false);

  bool const evolutionOk = (std::abs(rho0 - 1.0) < 0.1) && (rhoMid > 0.5 && rhoMid < 1.5) &&
                           (std::abs(rhoEnd - 0.7) < 0.2); // Near minimum of sine

  std::cout << "  rho(t=0.0) = " << rho0 << " (expect ~1.0)\n"
            << "  rho(t=0.45) = " << rhoMid << " (expect between peaks)\n"
            << "  rho(t=0.9) = " << rhoEnd << " (expect ~0.7, near sine min)\n"
            << "  Status: " << (evolutionOk ? "PASS" : "FAIL") << "\n\n";

  return evolutionOk;
}

// Test 2: Multi-field interpolation
bool testMultiFieldInterpolation() {
  std::cout << "Test 2: Multi-Field Interpolation\n";

  // Two GRMHD fields: density and temperature
  std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
  std::vector<double> rho = {1.0, 1.2, 1.1, 0.9};
  std::vector<double> temp = {1e7, 2e7, 1.5e7, 1.2e7};

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Sample both fields at mid-points
  double const rho1p5 = interpolateField(ts, rho.data(), 1.5, false);
  double const temp1p5 = interpolateField(ts, temp.data(), 1.5, false);

  bool const multiOk = (rho1p5 > 1.1 && rho1p5 < 1.2) && (temp1p5 > 1.5e7 && temp1p5 < 2e7);

  std::cout << std::scientific << std::setprecision(2);
  std::cout << "  rho(1.5) = " << rho1p5 << " (expect between 1.1 and 1.2)\n"
            << "  T(1.5) = " << temp1p5 << " (expect between 1.5e7 and 2e7)\n"
            << "  Status: " << (multiOk ? "PASS" : "FAIL") << "\n\n";

  return multiOk;
}

// Test 3: Rapid field sampling at fine time steps
bool testFineTimescaleSampling() {
  std::cout << "Test 3: Fine Timescale Field Sampling\n";

  // 5 dumps over 0.1 time units
  std::vector<double> times = {0.0, 0.025, 0.05, 0.075, 0.1};
  std::vector<double> bField = {100.0, 105.0, 110.0, 105.0, 100.0};

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Sample at very fine resolution
  std::vector<double> const sampleTimes = {0.01, 0.03, 0.06, 0.08};
  std::vector<double> samples;

  samples.reserve(sampleTimes.size());
  for (double const t : sampleTimes) {
    samples.push_back(interpolateField(ts, bField.data(), t, false));
  }

  // All samples should be between min and max
  bool fineOk = true;
  for (double const b : samples) {
    if (b < 99.0 || b > 111.0) {
      fineOk = false;
    }
  }

  std::cout << "  Samples at fine times: ";
  for (double const sample : samples) {
    std::cout << std::fixed << std::setprecision(1) << sample << " ";
  }
  std::cout << "\n  All in range [99, 111]: " << (fineOk ? "yes" : "no") << "\n"
            << "  Status: " << (fineOk ? "PASS" : "FAIL") << "\n\n";

  return fineOk;
}

// Test 4: Boundary behavior at time series edges
bool testBoundarySampling() {
  std::cout << "Test 4: Boundary Sampling Behavior\n";

  std::vector<double> times = {0.0, 1.0, 2.0};
  std::vector<double> field = {10.0, 20.0, 15.0};

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Sample at exact boundaries
  double const fStart = interpolateField(ts, field.data(), 0.0, false);
  double const fEnd = interpolateField(ts, field.data(), 2.0, false);

  // Sample just beyond boundaries
  double const fBefore = interpolateField(ts, field.data(), -0.5, false);
  double const fAfter = interpolateField(ts, field.data(), 2.5, false);

  bool const boundaryOk = (std::abs(fStart - 10.0) < 1e-10) && (std::abs(fEnd - 15.0) < 1e-10) &&
                          (std::abs(fBefore - 10.0) < 1.0) && // Should extrapolate
                          (std::abs(fAfter - 15.0) < 1.0);

  std::cout << "  f(0.0) = " << fStart << " (expect 10.0)\n"
            << "  f(2.0) = " << fEnd << " (expect 15.0)\n"
            << "  f(-0.5) = " << fBefore << " (extrapolate)\n"
            << "  f(2.5) = " << fAfter << " (extrapolate)\n"
            << "  Status: " << (boundaryOk ? "PASS" : "FAIL") << "\n\n";

  return boundaryOk;
}

// Test 5: High-frequency oscillations
bool testOscillatingFields() {
  std::cout << "Test 5: Oscillating Field Sampling\n";

  // Rapidly oscillating magnetic field (magnetohydrodynamic waves)
  std::vector<double> times;
  std::vector<double> bOsc;

  for (int i = 0; i < 20; i++) {
    times.push_back(i * 0.05);
    // High-frequency B-field oscillations
    bOsc.push_back(100.0 + (50.0 * std::sin(i * 1.57))); // freq ~ 10 Hz
  }

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Sample at intermediate times
  double const bMid = interpolateField(ts, bOsc.data(), 0.475, false);
  double const bPeak1 = interpolateField(ts, bOsc.data(), 0.25, false);
  double const bValley = interpolateField(ts, bOsc.data(), 0.5, false);

  bool const oscOk =
      (bMid > 50.0 && bMid < 150.0) && (bPeak1 > 100.0) && (bValley > 50.0 && bValley < 150.0);

  std::cout << std::fixed << std::setprecision(1);
  std::cout << "  B(0.475) = " << bMid << " (oscillating)\n"
            << "  B(0.25) = " << bPeak1 << " (near peak)\n"
            << "  B(0.5) = " << bValley << " (near valley)\n"
            << "  Status: " << (oscOk ? "PASS" : "FAIL") << "\n\n";

  return oscOk;
}

// Test 6: Smooth vs. linear interpolation difference
bool testInterpolationSmoothness() {
  std::cout << "Test 6: Interpolation Smoothness Comparison\n";

  // Sharp feature in field evolution
  std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0};
  std::vector<double> field = {1.0, 10.0, 2.0, 10.0, 1.0};

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  double const lin1p5 = interpolateField(ts, field.data(), 1.5, false);
  double const herm1p5 = interpolateField(ts, field.data(), 1.5, true);

  // Hermite should be smoother than linear near sharp transitions
  bool const smoothnessOk = (lin1p5 > 2.0 && lin1p5 < 10.0) && (herm1p5 > 2.0 && herm1p5 < 10.0);

  std::cout << std::fixed << std::setprecision(2);
  std::cout << "  Linear f(1.5) = " << lin1p5 << "\n"
            << "  Hermite f(1.5) = " << herm1p5 << "\n"
            << "  Both in valid range: " << (smoothnessOk ? "yes" : "no") << "\n"
            << "  Status: " << (smoothnessOk ? "PASS" : "FAIL") << "\n\n";

  return smoothnessOk;
}

// Test 7: Complete multi-dump animation cycle
bool testAnimationCycle() {
  std::cout << "Test 7: Complete Animation Cycle\n";

  // 10-dump simulation sequence
  std::vector<double> times;
  std::vector<double> accretionRate;

  for (int i = 0; i < 10; i++) {
    times.push_back(i * 0.1);
    // Accretion rate varies sinusoidally over cycle
    accretionRate.push_back(1.0 + (0.5 * std::sin(i * 0.628)));
  }

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));
  PlaybackState pb = createPlaybackState(ts, 1.0);

  // Simulate 30 frames at 30 FPS
  pb.isPlaying = true;
  int frameCount = 0;

  for (int f = 0; f < 30; f++) {
    updatePlayback(pb, ts, 1.0 / 30.0);
    double const mdot = interpolateField(ts, accretionRate.data(), pb.tCurrent, false);
    if (mdot > 0.5 && mdot < 1.5) {
      frameCount++;
    }
  }

  bool const cycleOk = (pb.frameNumber == 30) && (pb.tCurrent > ts.tStart) &&
                       (frameCount >= 25); // Most frames should have valid field

  std::cout << "  Total frames: " << pb.frameNumber << " (expect 30)\n"
            << "  Final time: " << std::fixed << std::setprecision(3) << pb.tCurrent << "\n"
            << "  Valid field frames: " << frameCount << "/30\n"
            << "  Status: " << (cycleOk ? "PASS" : "FAIL") << "\n\n";

  return cycleOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "TEMPORAL GRMHD FIELD SAMPLING VALIDATION\n"
              << "Phase 8.1b: Time-Dependent GRMHD\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 7;

    if (testGrmhdFieldEvolution()) {
      passed++;
    }
    if (testMultiFieldInterpolation()) {
      passed++;
    }
    if (testFineTimescaleSampling()) {
      passed++;
    }
    if (testBoundarySampling()) {
      passed++;
    }
    if (testOscillatingFields()) {
      passed++;
    }
    if (testInterpolationSmoothness()) {
      passed++;
    }
    if (testAnimationCycle()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
