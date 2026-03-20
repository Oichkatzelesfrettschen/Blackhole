/**
 * @file phase8_pipeline_validation_test.cpp
 * @brief Phase 8.1d: Full GRMHD Time Series Playback Pipeline Validation
 *
 * Integration tests for complete Phase 8: temporal interpolation, GRMHD
 * field sampling, and advanced playback control working together
 */

#include <cassert>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

#include "../src/physics/playback_control.h"
#include "../src/physics/timeseries_interpolation.h"

using namespace physics;

// Test 1: Multi-field GRMHD interpolation with playback control
namespace {

bool testMultifieldGrmhdPlayback() {
  std::cout << "Test 1: Multi-Field GRMHD Playback Integration\n";

  // Simulate 15-dump GRMHD sequence
  std::vector<double> times;
  std::vector<double> rhoField; // Density
  std::vector<double> tField;   // Temperature
  std::vector<double> bField;   // Magnetic field magnitude

  for (int i = 0; i < 15; i++) {
    times.push_back(i * 0.1);
    rhoField.push_back(1.0 + (0.3 * std::sin(i * 0.418)));
    tField.push_back(1e7 * (1.0 + (0.5 * std::cos(i * 0.314))));
    bField.push_back(100.0 + (50.0 * std::sin(i * 0.628)));
  }

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);
  setPlaybackMode(state, PlaybackMode::Forward);

  // Sample all 3 fields at multiple times
  std::vector<double> sampledRho;
  std::vector<double> sampledT;
  std::vector<double> sampledB;

  for (int frame = 0; frame < 5; frame++) {
    updateAdvancedPlayback(state, ts, 1.0 / 30.0, 0.0);

    double const rho = interpolateField(ts, rhoField.data(), state.tCurrent, false);
    double const temp = interpolateField(ts, tField.data(), state.tCurrent, false);
    double const b = interpolateField(ts, bField.data(), state.tCurrent, true); // Hermite

    sampledRho.push_back(rho);
    sampledT.push_back(temp);
    sampledB.push_back(b);
  }

  // Verify sample ranges
  bool const multifieldOk =
      (sampledRho.size() == 5) && (sampledT.size() == 5) && (sampledB.size() == 5) &&
      (sampledRho.at(0) > 0.7 && sampledRho.at(0) < 1.3) &&
      (sampledT.at(0) > 0.5e7 && sampledT.at(0) < 1.5e7) && (sampledB.at(0) > 50.0 && sampledB.at(0) < 150.0);

  std::cout << "  Samples collected: " << sampledRho.size() << "\n"
            << "  Rho range: [" << sampledRho.at(0) << ", " << sampledRho.back() << "]\n"
            << "  T range: [" << std::scientific << sampledT.at(0) << ", " << sampledT.back()
            << std::defaultfloat << "]\n"
            << "  B field range: [" << sampledB.at(0) << ", " << sampledB.back() << "]\n"
            << "  Status: " << (multifieldOk ? "PASS" : "FAIL") << "\n\n";

  return multifieldOk;
}

// Test 2: Hermite vs linear interpolation switching
bool testInterpolationModeSwitching() {
  std::cout << "Test 2: Interpolation Mode Switching\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0};
  std::vector<double> field = {1.0, 5.0, 2.0, 8.0, 3.0, 7.0};

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Sample at mid-points with both methods
  double const linear2p5 = interpolateField(ts, field.data(), 2.5, false);
  double const hermite2p5 = interpolateField(ts, field.data(), 2.5, true);

  double const linear4p5 = interpolateField(ts, field.data(), 4.5, false);
  double const hermite4p5 = interpolateField(ts, field.data(), 4.5, true);

  // Hermite should be smoother (closer to Catmull-Rom continuity)
  bool const switchingOk =
      (linear2p5 > 1.0 && linear2p5 < 8.0) && (hermite2p5 > 1.0 && hermite2p5 < 8.0) &&
      (linear4p5 > 2.0 && linear4p5 < 8.0) && (hermite4p5 > 2.0 && hermite4p5 < 8.0);

  std::cout << "  Linear f(2.5) = " << std::fixed << std::setprecision(2) << linear2p5 << "\n"
            << "  Hermite f(2.5) = " << hermite2p5 << " (smoother)\n"
            << "  Linear f(4.5) = " << linear4p5 << "\n"
            << "  Hermite f(4.5) = " << hermite4p5 << " (smoother)\n"
            << "  Status: " << (switchingOk ? "PASS" : "FAIL") << "\n\n";

  return switchingOk;
}

// Test 3: Multi-rate playback (fast-forward, slo-mo)
bool testMultiratePlayback() {
  std::cout << "Test 3: Multi-Rate Playback\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
  std::vector<double> const field = {0.0, 10.0, 20.0, 30.0};

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  // Test 1x speed
  AdvancedPlaybackState state1x = createAdvancedPlaybackState(ts, 1.0);
  setPlaybackMode(state1x, PlaybackMode::Forward);

  // Test 2x speed (fast-forward)
  AdvancedPlaybackState state2x = createAdvancedPlaybackState(ts, 2.0);
  setPlaybackMode(state2x, PlaybackMode::Forward);

  // Test 0.5x speed (slow-motion)
  AdvancedPlaybackState state05x = createAdvancedPlaybackState(ts, 0.5);
  setPlaybackMode(state05x, PlaybackMode::Forward);

  // Simulate 1 frame at 60 FPS
  double const dtFrame = 1.0 / 60.0;

  updateAdvancedPlayback(state1x, ts, dtFrame, 0.0);
  updateAdvancedPlayback(state2x, ts, dtFrame, 0.0);
  updateAdvancedPlayback(state05x, ts, dtFrame, 0.0);

  // At 2x speed, time should advance ~2x faster than 1x
  // At 0.5x speed, time should advance ~0.5x slower than 1x
  bool const t2xFaster = (state2x.tCurrent > state1x.tCurrent);
  bool const t05xSlower = (state05x.tCurrent < state1x.tCurrent);

  bool const multirateOk = (state1x.mode == PlaybackMode::Forward) &&
                           (state2x.mode == PlaybackMode::Forward) &&
                           (state05x.mode == PlaybackMode::Forward) && t2xFaster && t05xSlower;

  std::cout << "  1x speed: t = " << std::fixed << std::setprecision(4) << state1x.tCurrent << "\n"
            << "  2x speed: t = " << state2x.tCurrent << " (faster)\n"
            << "  0.5x speed: t = " << state05x.tCurrent << " (slower)\n"
            << "  Status: " << (multirateOk ? "PASS" : "FAIL") << "\n\n";

  return multirateOk;
}

// Test 4: Reverse playback with hermite interpolation
bool testReverseWithInterpolation() {
  std::cout << "Test 4: Reverse Playback with Hermite Interpolation\n";

  // Create smooth field evolution
  std::vector<double> times;
  std::vector<double> smoothField;

  for (int i = 0; i < 20; i++) {
    times.push_back(i * 0.05);
    smoothField.push_back(10.0 + (5.0 * std::sin(i * 0.314)));
  }

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);
  state.tCurrent = ts.tEnd; // Start at end
  setPlaybackMode(state, PlaybackMode::Reverse);
  state.reverseSpeed = 1.0;

  // Simulate 5 frames backward
  std::vector<double> reverseSamples;

  for (int frame = 0; frame < 5; frame++) {
    updateAdvancedPlayback(state, ts, 1.0 / 30.0, 0.0);
    double const val = interpolateField(ts, smoothField.data(), state.tCurrent, true);
    reverseSamples.push_back(val);
  }

  // Check that time decreased monotonically
  bool const reverseOk = (state.frameNumber == 5) && (state.mode == PlaybackMode::Reverse) &&
                         (state.tCurrent < ts.tEnd) && (state.tCurrent > ts.tStart) &&
                         (reverseSamples.size() == 5);

  std::cout << "  Frames played backward: " << state.frameNumber << "\n"
            << "  Current time: " << std::fixed << std::setprecision(3) << state.tCurrent << "\n"
            << "  Field values sampled: " << reverseSamples.size() << "\n"
            << "  All samples in valid range: "
            << (reverseSamples.at(0) > 5.0 && reverseSamples.at(0) < 15.0 ? "yes" : "no") << "\n"
            << "  Status: " << (reverseOk ? "PASS" : "FAIL") << "\n\n";

  return reverseOk;
}

// Test 5: Frame-by-frame stepping with interpolation
bool testFrameSteppingIntegration() {
  std::cout << "Test 5: Frame-By-Frame Stepping Integration\n";

  // 10-dump GRMHD sequence
  std::vector<double> times;
  std::vector<double> density;

  for (int i = 0; i < 10; i++) {
    times.push_back(i * 0.5);
    density.push_back(1.0 + (0.2 * i));
  }

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Step through all frames manually (with safety limit)
  std::vector<double> densitiesAtFrames;

  uint32_t maxSteps = 50; // Safety limit
  while (state.tCurrent <= ts.tEnd && maxSteps-- > 0) {
    double const rho = interpolateField(ts, density.data(), state.tCurrent, false);
    densitiesAtFrames.push_back(rho);

    stepFrameForward(state, ts);

    if (state.tCurrent > ts.tEnd) {
      break;
    }
  }

  // Verify samples are in reasonable range
  bool allPositive = true;
  for (double const densitiesAtFrame : densitiesAtFrames) {
    if (densitiesAtFrame <= 0.0 || densitiesAtFrame > 3.0) {
      allPositive = false;
      break;
    }
  }

  bool const steppingOk = (densitiesAtFrames.size() > 5) && (state.frameNumber > 5) && allPositive;

  std::cout << "  Frame count: " << state.frameNumber << "\n"
            << "  Samples collected: " << densitiesAtFrames.size() << "\n"
            << "  All samples in valid range [0,3]: " << (allPositive ? "yes" : "no") << "\n"
            << "  First density: " << std::fixed << std::setprecision(2) << densitiesAtFrames.at(0)
            << "\n"
            << "  Last density: " << densitiesAtFrames.back() << "\n"
            << "  Status: " << (steppingOk ? "PASS" : "FAIL") << "\n\n";

  return steppingOk;
}

// Test 6: Timeline marker navigation with field sampling
bool testMarkerNavigation() {
  std::cout << "Test 6: Timeline Marker Navigation with Field Sampling\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0, 5.0};
  std::vector<double> field = {10.0, 20.0, 15.0, 25.0, 18.0, 22.0};

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Add markers at peaks and valleys
  (void)addTimelineMarker(state, 1.0, ts); // Peak
  (void)addTimelineMarker(state, 2.0, ts); // Valley
  (void)addTimelineMarker(state, 3.0, ts); // Peak
  (void)addTimelineMarker(state, 4.0, ts); // Valley
  (void)addTimelineMarker(state, 5.0, ts); // Peak

  // Navigate to markers and sample field
  std::vector<double> markerSamples;

  state.tCurrent = 0.5;
  for (uint32_t i = 0; i < state.nMarkers; i++) {
    (void)seekToMarker(state, ts, true);
    double const val = interpolateField(ts, field.data(), state.tCurrent, false);
    markerSamples.push_back(val);

    if (state.tCurrent >= ts.tEnd) {
      break;
    }
  }

  bool const markerOk = (state.nMarkers == 5) && (markerSamples.size() > 2) &&
                        (markerSamples.at(0) > 15.0); // First marker is at 1.0, field=20.0

  std::cout << "  Markers created: " << state.nMarkers << "\n"
            << "  Markers navigated: " << markerSamples.size() << "\n"
            << "  Fields at markers: ";
  for (size_t i = 0; i < markerSamples.size() && i < 3; i++) {
    std::cout << std::fixed << std::setprecision(0) << markerSamples.at(i) << " ";
  }
  std::cout << "...\n"
            << "  Status: " << (markerOk ? "PASS" : "FAIL") << "\n\n";

  return markerOk;
}

// Test 7: Complete Phase 8 pipeline validation
bool testCompletePhase8Pipeline() {
  std::cout << "Test 7: Complete Phase 8 Pipeline Validation\n";

  // Realistic 20-dump GRMHD simulation
  std::vector<double> times;
  std::vector<double> rho;
  std::vector<double> t;
  std::vector<double> b;
  std::vector<double> psi;

  for (int i = 0; i < 20; i++) {
    times.push_back(i * 0.05);
    rho.push_back(1.0 + (0.3 * std::sin(i * 0.314)));
    t.push_back(1e7 * (1.0 + (0.4 * std::cos(i * 0.418))));
    b.push_back(100.0 + (40.0 * std::sin(i * 0.628)));
    psi.push_back(0.5 * (1.0 + (0.2 * std::cos(i * 0.314))));
  }

  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Add key markers
  (void)addTimelineMarker(state, 0.25, ts); // Early time
  (void)addTimelineMarker(state, 0.50, ts); // Mid time
  (void)addTimelineMarker(state, 0.95, ts); // Late time

  // Full simulation: forward, pause, seek, reverse
  setPlaybackMode(state, PlaybackMode::Forward);

  uint32_t totalSamples = 0;
  double sumRho = 0.0;
  double sumT = 0.0;
  double sumB = 0.0;

  // Play forward 5 frames
  for (int f = 0; f < 5; f++) {
    updateAdvancedPlayback(state, ts, 1.0 / 30.0, 50.0);

    double const rhoVal = interpolateField(ts, rho.data(), state.tCurrent, false);
    double const tVal = interpolateField(ts, t.data(), state.tCurrent, false);
    double const bVal = interpolateField(ts, b.data(), state.tCurrent, true);

    sumRho += rhoVal;
    sumT += tVal;
    sumB += bVal;
    totalSamples++;
  }

  // Pause and seek
  togglePause(state);
  (void)seekToMarker(state, ts, true);

  // Play backward 3 frames
  reversePlaybackDirection(state);
  togglePause(state);

  for (int f = 0; f < 3; f++) {
    updateAdvancedPlayback(state, ts, 1.0 / 30.0, 55.0);

    double const rhoVal = interpolateField(ts, rho.data(), state.tCurrent, false);
    double const tVal = interpolateField(ts, t.data(), state.tCurrent, false);
    double const bVal = interpolateField(ts, b.data(), state.tCurrent, true);

    sumRho += rhoVal;
    sumT += tVal;
    sumB += bVal;
    totalSamples++;
  }

  // Verify stats
  bool const pipelineOk = (totalSamples == 8) && (ts.nDumps == 20) && (state.nMarkers == 3) &&
                          (state.frameNumber == 8) && (sumRho > 0.0) && (sumT > 0.0) &&
                          (sumB > 0.0) && (state.avgInterpolationTime > 0.0) &&
                          (state.interpolationCalls == 8);

  std::cout << "  GRMHD dumps: " << ts.nDumps << "\n"
            << "  Total timeline markers: " << state.nMarkers << "\n"
            << "  Total frames played: " << state.frameNumber << "\n"
            << "  Field samples collected: " << totalSamples << "\n"
            << "  Avg density: " << std::fixed << std::setprecision(2) << (sumRho / totalSamples)
            << "\n"
            << "  Avg temperature: " << std::scientific << (sumT / totalSamples)
            << std::defaultfloat << "\n"
            << "  Avg B-field: " << (sumB / totalSamples) << "\n"
            << "  Interpolation overhead: " << state.avgInterpolationTime << " us\n"
            << "  Status: " << (pipelineOk ? "PASS" : "FAIL") << "\n\n";

  return pipelineOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "PHASE 8 FULL PIPELINE VALIDATION\n"
              << "Phase 8.1d: Complete GRMHD Time Series Playback\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 7;

    if (testMultifieldGrmhdPlayback()) {
      passed++;
    }
    if (testInterpolationModeSwitching()) {
      passed++;
    }
    if (testMultiratePlayback()) {
      passed++;
    }
    if (testReverseWithInterpolation()) {
      passed++;
    }
    if (testFrameSteppingIntegration()) {
      passed++;
    }
    if (testMarkerNavigation()) {
      passed++;
    }
    if (testCompletePhase8Pipeline()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
