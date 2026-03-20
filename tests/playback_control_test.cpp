/**
 * @file playback_control_test.cpp
 * @brief Phase 8.1c: Advanced Playback Control & Timeline Management
 *
 * Tests seeking, reverse playback, frame stepping, timeline markers,
 * and playback mode transitions
 */

#include <cassert>
#include <cmath>
#include <cstdint>
#include <iomanip>
#include <iostream>
#include <vector>

#include "../src/physics/playback_control.h"
#include "timeseries_interpolation.h"

using namespace physics;

// Test 1: Playback mode transitions
namespace {

bool testPlaybackModeTransitions() {
  std::cout << "Test 1: Playback Mode Transitions\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Test mode changes
  assert(state.mode == PlaybackMode::Stopped);

  setPlaybackMode(state, PlaybackMode::Forward);
  assert(state.mode == PlaybackMode::Forward);

  togglePause(state);
  assert(state.mode == PlaybackMode::PausedForward);

  togglePause(state);
  assert(state.mode == PlaybackMode::Forward);

  reversePlaybackDirection(state);
  assert(state.mode == PlaybackMode::Reverse);

  togglePause(state);
  assert(state.mode == PlaybackMode::PausedReverse);

  bool const modeOk = (state.mode == PlaybackMode::PausedReverse);

  std::cout << "  Forward -> Paused -> Reverse -> Paused: ";
  std::cout << (modeOk ? "PASS" : "FAIL") << "\n\n";

  return modeOk;
}

// Test 2: Timeline seeking and scrubbing
bool testTimelineSeeking() {
  std::cout << "Test 2: Timeline Seeking & Scrubbing\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Test immediate seek
  bool const seek1 = seekTimeline(state, ts, 1.5, 0);
  bool const seek2 = seekTimeline(state, ts, 3.5, 0);
  bool const seek3 = seekTimeline(state, ts, -1.0, 0); // Out of bounds

  bool const seekOk = seek1 && seek2 && !seek3 && (std::abs(state.tCurrent - 3.5) < 1e-10);

  std::cout << "  Seek to 1.5: " << (seek1 ? "ok" : "fail") << "\n"
            << "  Seek to 3.5: " << (seek2 ? "ok" : "fail") << "\n"
            << "  Seek to -1.0 (invalid): " << (!seek3 ? "rejected" : "ERROR") << "\n"
            << "  Final position: " << std::fixed << std::setprecision(2) << state.tCurrent << "\n"
            << "  Status: " << (seekOk ? "PASS" : "FAIL") << "\n\n";

  return seekOk;
}

// Test 3: Frame stepping (forward and backward)
bool testFrameStepping() {
  std::cout << "Test 3: Frame Stepping\n";

  std::vector<double> times = {0.0, 0.5, 1.0, 1.5, 2.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);
  state.tCurrent = 1.0;

  uint32_t const initialFrames = state.frameNumber;

  // Step forward 2 frames
  stepFrameForward(state, ts);
  stepFrameForward(state, ts);

  double const tAfterForward = state.tCurrent;
  uint32_t const framesAfterForward = state.frameNumber;

  // Step backward 1 frame
  stepFrameBackward(state, ts);

  double const tAfterBackward = state.tCurrent;
  uint32_t const finalFrames = state.frameNumber;

  bool const steppingOk = (framesAfterForward == initialFrames + 2) &&
                          (finalFrames == initialFrames + 3) &&
                          (std::abs(tAfterForward - 2.0) < 0.15) && // ~2.0 after 2 steps from t=1.0
                          (std::abs(tAfterBackward - 1.5) < 0.15);  // ~1.5 after 1 back from t=2.0

  std::cout << "  Initial frames: " << initialFrames << "\n"
            << "  After 2 forward steps: t=" << std::fixed << std::setprecision(2) << tAfterForward
            << ", frames=" << framesAfterForward << "\n"
            << "  After 1 backward step: t=" << tAfterBackward << ", frames=" << finalFrames << "\n"
            << "  Status: " << (steppingOk ? "PASS" : "FAIL") << "\n\n";

  return steppingOk;
}

// Test 4: Timeline markers
bool testTimelineMarkers() {
  std::cout << "Test 4: Timeline Markers\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Add markers at key times
  bool const m1 = addTimelineMarker(state, 1.0, ts);
  bool const m2 = addTimelineMarker(state, 2.5, ts);
  bool const m3 = addTimelineMarker(state, 4.0, ts);
  bool const mInvalid = addTimelineMarker(state, 5.0, ts); // Out of bounds

  // Test seeking to markers
  state.tCurrent = 0.5;
  (void)seekToMarker(state, ts, true);
  double const tAtNext = state.tCurrent;

  state.tCurrent = 3.0;
  (void)seekToMarker(state, ts, false);
  double const tAtPrev = state.tCurrent;

  bool const markersOk = m1 && m2 && m3 && !mInvalid && (state.nMarkers == 3) &&
                         (std::abs(tAtNext - 1.0) < 1e-10) && (std::abs(tAtPrev - 2.5) < 1e-10);

  std::cout << "  Added 3 markers: " << (m1 && m2 && m3 ? "ok" : "fail") << "\n"
            << "  Invalid marker rejected: " << (!mInvalid ? "yes" : "ERROR") << "\n"
            << "  Seek from 0.5 to next (expect 1.0): " << std::fixed << std::setprecision(2)
            << tAtNext << "\n"
            << "  Seek from 3.0 to prev (expect 2.5): " << tAtPrev << "\n"
            << "  Total markers: " << state.nMarkers << "\n"
            << "  Status: " << (markersOk ? "PASS" : "FAIL") << "\n\n";

  return markersOk;
}

// Test 5: Reverse playback with mode switching
bool testReversePlayback() {
  std::cout << "Test 5: Reverse Playback\n";

  std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);
  state.reverseSpeed = 1.0;

  // Start at end, play backward
  state.tCurrent = 3.0;
  setPlaybackMode(state, PlaybackMode::Reverse);

  // Simulate 3 frames of backward playback at 1.0 FPS
  double const dtFrame = 1.0 / 3.0; // ~33ms per frame

  updateAdvancedPlayback(state, ts, dtFrame, 0.0);
  double const t1frame = state.tCurrent;

  updateAdvancedPlayback(state, ts, dtFrame, 0.0);
  double const t2frames = state.tCurrent;

  updateAdvancedPlayback(state, ts, dtFrame, 0.0);
  double const t3frames = state.tCurrent;

  bool const reverseOk = (state.frameNumber == 3) && (t1frame < 3.0) && (t2frames < t1frame) &&
                         (t3frames < t2frames) && (t3frames > ts.tStart); // Still within bounds

  std::cout << "  Start at t=3.0, reverse mode\n"
            << "  After frame 1: t=" << std::fixed << std::setprecision(3) << t1frame << "\n"
            << "  After frame 2: t=" << t2frames << "\n"
            << "  After frame 3: t=" << t3frames << "\n"
            << "  Frame counter: " << state.frameNumber << "\n"
            << "  Status: " << (reverseOk ? "PASS" : "FAIL") << "\n\n";

  return reverseOk;
}

// Test 6: Performance metrics tracking
bool testPerformanceMetrics() {
  std::cout << "Test 6: Performance Metrics\n";

  std::vector<double> times = {0.0, 1.0, 2.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Simulate 10 frames with varying interpolation times
  setPlaybackMode(state, PlaybackMode::Forward);

  for (int i = 0; i < 10; i++) {
    double const dtFrame = 1.0 / 60.0;            // 60 FPS
    double const interpTime = 100.0 + (i * 10.0); // 100-190 microseconds

    updateAdvancedPlayback(state, ts, dtFrame, interpTime);
  }

  // Check metrics
  bool const metricsOk =
      (state.frameCount == 0) && // Not explicitly incremented
      (state.interpolationCalls == 10) &&
      (state.avgInterpolationTime > 100.0 && state.avgInterpolationTime < 200.0) &&
      (state.peakInterpolationTime >= 190.0) && (std::abs(state.frameTimeMs - 16.67) < 0.1);

  std::cout << "  Interpolation calls: " << state.interpolationCalls << " (expect 10)\n"
            << "  Avg interp time: " << std::fixed << std::setprecision(1)
            << state.avgInterpolationTime << " us (expect ~145)\n"
            << "  Peak interp time: " << state.peakInterpolationTime << " us (expect ~190)\n"
            << "  Frame time: " << state.frameTimeMs << " ms (expect ~16.67)\n"
            << "  Status: " << (metricsOk ? "PASS" : "FAIL") << "\n\n";

  return metricsOk;
}

// Test 7: Complete interactive timeline control session
bool testCompleteTimelineControl() {
  std::cout << "Test 7: Complete Timeline Control Session\n";

  std::vector<double> times = {0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0};
  TimeSeriesMetadata const ts =
      buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

  AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

  // Add markers at interesting points
  (void)addTimelineMarker(state, 1.0, ts);
  (void)addTimelineMarker(state, 2.0, ts);

  // Simulate interactive session:
  // 1. Start playback
  setPlaybackMode(state, PlaybackMode::Forward);
  assert(state.mode == PlaybackMode::Forward);

  // 2. Play forward 2 frames
  for (int i = 0; i < 2; i++) {
    updateAdvancedPlayback(state, ts, 1.0 / 30.0, 50.0);
  }
  double const tAfterPlay = state.tCurrent;

  // 3. Pause
  togglePause(state);
  double const tPaused = state.tCurrent;

  // 4. Seek to marker
  (void)seekToMarker(state, ts, true);
  double const tAfterSeek = state.tCurrent;

  // 5. Resume and play backward
  reversePlaybackDirection(state);
  togglePause(state);
  assert(state.mode == PlaybackMode::Reverse);

  // 6. Play backward 1 frame
  updateAdvancedPlayback(state, ts, 1.0 / 30.0, 60.0);
  double const tFinal = state.tCurrent;

  bool const sessionOk =
      (state.frameNumber >= 3) && (std::abs(tPaused - tAfterPlay) < 1e-10) && // Paused unchanged
      (std::abs(tAfterSeek - 1.0) < 1e-10) && // Seeked to first marker
      (tFinal < tAfterSeek) &&                // Playing backward moves time down
      (state.nMarkers == 2) &&
      (state.interpolationCalls == 3); // 2 forward + 1 backward (pause doesn't call update)

  std::cout << "  After 2 forward frames: t=" << std::fixed << std::setprecision(3) << tAfterPlay
            << "\n"
            << "  Paused at: t=" << tPaused << "\n"
            << "  Seeked to marker: t=" << tAfterSeek << "\n"
            << "  After 1 reverse frame: t=" << tFinal << "\n"
            << "  Total frames: " << state.frameNumber << "\n"
            << "  Markers: " << state.nMarkers << "\n"
            << "  Interpolation calls: " << state.interpolationCalls << "\n"
            << "  Status: " << (sessionOk ? "PASS" : "FAIL") << "\n\n";

  return sessionOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "ADVANCED PLAYBACK CONTROL VALIDATION\n"
              << "Phase 8.1c: Playback Control & Timeline Management\n"
              << "====================================================\n";

    int passed = 0;
    int const total = 7;

    if (testPlaybackModeTransitions()) {
      passed++;
    }
    if (testTimelineSeeking()) {
      passed++;
    }
    if (testFrameStepping()) {
      passed++;
    }
    if (testTimelineMarkers()) {
      passed++;
    }
    if (testReversePlayback()) {
      passed++;
    }
    if (testPerformanceMetrics()) {
      passed++;
    }
    if (testCompleteTimelineControl()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
