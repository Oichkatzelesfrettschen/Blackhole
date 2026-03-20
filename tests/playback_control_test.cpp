/**
 * @file playback_control_test.cpp
 * @brief Phase 8.1c: Advanced Playback Control & Timeline Management
 *
 * Tests seeking, reverse playback, frame stepping, timeline markers,
 * and playback mode transitions
 */

#include <iostream>
#include <cassert>
#include <cstdint>
#include <vector>
#include <cmath>
#include <iomanip>

#include "../src/physics/playback_control.h"

using namespace physics;

// Test 1: Playback mode transitions
bool test_playback_mode_transitions() {
    std::cout << "Test 1: Playback Mode Transitions\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

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

    bool mode_ok = (state.mode == PlaybackMode::PausedReverse);

    std::cout << "  Forward -> Paused -> Reverse -> Paused: ";
    std::cout << (mode_ok ? "PASS" : "FAIL") << "\n\n";

    return mode_ok;
}

// Test 2: Timeline seeking and scrubbing
bool test_timeline_seeking() {
    std::cout << "Test 2: Timeline Seeking & Scrubbing\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

    // Test immediate seek
    bool seek1 = seekTimeline(state, ts, 1.5, 0);
    bool seek2 = seekTimeline(state, ts, 3.5, 0);
    bool seek3 = seekTimeline(state, ts, -1.0, 0);  // Out of bounds

    bool seek_ok = seek1 && seek2 && !seek3 &&
                   (std::abs(state.tCurrent - 3.5) < 1e-10);

    std::cout << "  Seek to 1.5: " << (seek1 ? "ok" : "fail") << "\n"
              << "  Seek to 3.5: " << (seek2 ? "ok" : "fail") << "\n"
              << "  Seek to -1.0 (invalid): " << (!seek3 ? "rejected" : "ERROR") << "\n"
              << "  Final position: " << std::fixed << std::setprecision(2) << state.tCurrent << "\n"
              << "  Status: " << (seek_ok ? "PASS" : "FAIL") << "\n\n";

    return seek_ok;
}

// Test 3: Frame stepping (forward and backward)
bool test_frame_stepping() {
    std::cout << "Test 3: Frame Stepping\n";

    std::vector<double> times = {0.0, 0.5, 1.0, 1.5, 2.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);
    state.tCurrent = 1.0;

    uint32_t initial_frames = state.frameNumber;

    // Step forward 2 frames
    stepFrameForward(state, ts);
    stepFrameForward(state, ts);

    double t_after_forward = state.tCurrent;
    uint32_t frames_after_forward = state.frameNumber;

    // Step backward 1 frame
    stepFrameBackward(state, ts);

    double t_after_backward = state.tCurrent;
    uint32_t final_frames = state.frameNumber;

    bool stepping_ok = (frames_after_forward == initial_frames + 2) &&
                      (final_frames == initial_frames + 3) &&
                      (std::abs(t_after_forward - 2.0) < 0.15) &&  // ~2.0 after 2 steps from t=1.0
                      (std::abs(t_after_backward - 1.5) < 0.15);   // ~1.5 after 1 back from t=2.0

    std::cout << "  Initial frames: " << initial_frames << "\n"
              << "  After 2 forward steps: t=" << std::fixed << std::setprecision(2)
              << t_after_forward << ", frames=" << frames_after_forward << "\n"
              << "  After 1 backward step: t=" << t_after_backward << ", frames=" << final_frames << "\n"
              << "  Status: " << (stepping_ok ? "PASS" : "FAIL") << "\n\n";

    return stepping_ok;
}

// Test 4: Timeline markers
bool test_timeline_markers() {
    std::cout << "Test 4: Timeline Markers\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0, 4.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

    // Add markers at key times
    bool m1 = addTimelineMarker(state, 1.0, ts);
    bool m2 = addTimelineMarker(state, 2.5, ts);
    bool m3 = addTimelineMarker(state, 4.0, ts);
    bool m_invalid = addTimelineMarker(state, 5.0, ts);  // Out of bounds

    // Test seeking to markers
    state.tCurrent = 0.5;
    (void)seekToMarker(state, ts, true);
    double t_at_next = state.tCurrent;

    state.tCurrent = 3.0;
    (void)seekToMarker(state, ts, false);
    double t_at_prev = state.tCurrent;

    bool markers_ok = m1 && m2 && m3 && !m_invalid &&
                     (state.nMarkers == 3) &&
                     (std::abs(t_at_next - 1.0) < 1e-10) &&
                     (std::abs(t_at_prev - 2.5) < 1e-10);

    std::cout << "  Added 3 markers: " << (m1 && m2 && m3 ? "ok" : "fail") << "\n"
              << "  Invalid marker rejected: " << (!m_invalid ? "yes" : "ERROR") << "\n"
              << "  Seek from 0.5 to next (expect 1.0): " << std::fixed << std::setprecision(2)
              << t_at_next << "\n"
              << "  Seek from 3.0 to prev (expect 2.5): " << t_at_prev << "\n"
              << "  Total markers: " << state.nMarkers << "\n"
              << "  Status: " << (markers_ok ? "PASS" : "FAIL") << "\n\n";

    return markers_ok;
}

// Test 5: Reverse playback with mode switching
bool test_reverse_playback() {
    std::cout << "Test 5: Reverse Playback\n";

    std::vector<double> times = {0.0, 1.0, 2.0, 3.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);
    state.reverseSpeed = 1.0;

    // Start at end, play backward
    state.tCurrent = 3.0;
    setPlaybackMode(state, PlaybackMode::Reverse);

    // Simulate 3 frames of backward playback at 1.0 FPS
    double dt_frame = 1.0 / 3.0;  // ~33ms per frame

    updateAdvancedPlayback(state, ts, dt_frame, 0.0);
    double t_1frame = state.tCurrent;

    updateAdvancedPlayback(state, ts, dt_frame, 0.0);
    double t_2frames = state.tCurrent;

    updateAdvancedPlayback(state, ts, dt_frame, 0.0);
    double t_3frames = state.tCurrent;

    bool reverse_ok = (state.frameNumber == 3) &&
                     (t_1frame < 3.0) &&
                     (t_2frames < t_1frame) &&
                     (t_3frames < t_2frames) &&
                     (t_3frames > ts.tStart);  // Still within bounds

    std::cout << "  Start at t=3.0, reverse mode\n"
              << "  After frame 1: t=" << std::fixed << std::setprecision(3) << t_1frame << "\n"
              << "  After frame 2: t=" << t_2frames << "\n"
              << "  After frame 3: t=" << t_3frames << "\n"
              << "  Frame counter: " << state.frameNumber << "\n"
              << "  Status: " << (reverse_ok ? "PASS" : "FAIL") << "\n\n";

    return reverse_ok;
}

// Test 6: Performance metrics tracking
bool test_performance_metrics() {
    std::cout << "Test 6: Performance Metrics\n";

    std::vector<double> times = {0.0, 1.0, 2.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

    AdvancedPlaybackState state = createAdvancedPlaybackState(ts, 1.0);

    // Simulate 10 frames with varying interpolation times
    setPlaybackMode(state, PlaybackMode::Forward);

    for (int i = 0; i < 10; i++) {
        double dt_frame = 1.0 / 60.0;  // 60 FPS
        double interp_time = 100.0 + (i * 10.0);  // 100-190 microseconds

        updateAdvancedPlayback(state, ts, dt_frame, interp_time);
    }

    // Check metrics
    bool metrics_ok = (state.frameCount == 0) &&  // Not explicitly incremented
                     (state.interpolationCalls == 10) &&
                     (state.avgInterpolationTime > 100.0 && state.avgInterpolationTime < 200.0) &&
                     (state.peakInterpolationTime >= 190.0) &&
                     (std::abs(state.frameTimeMs - 16.67) < 0.1);

    std::cout << "  Interpolation calls: " << state.interpolationCalls << " (expect 10)\n"
              << "  Avg interp time: " << std::fixed << std::setprecision(1)
              << state.avgInterpolationTime << " us (expect ~145)\n"
              << "  Peak interp time: " << state.peakInterpolationTime << " us (expect ~190)\n"
              << "  Frame time: " << state.frameTimeMs << " ms (expect ~16.67)\n"
              << "  Status: " << (metrics_ok ? "PASS" : "FAIL") << "\n\n";

    return metrics_ok;
}

// Test 7: Complete interactive timeline control session
bool test_complete_timeline_control() {
    std::cout << "Test 7: Complete Timeline Control Session\n";

    std::vector<double> times = {0.0, 0.5, 1.0, 1.5, 2.0, 2.5, 3.0};
    TimeSeriesMetadata ts = buildTimeseriesMetadata(times.data(), static_cast<uint32_t>(times.size()));

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
    double t_after_play = state.tCurrent;

    // 3. Pause
    togglePause(state);
    double t_paused = state.tCurrent;

    // 4. Seek to marker
    (void)seekToMarker(state, ts, true);
    double t_after_seek = state.tCurrent;

    // 5. Resume and play backward
    reversePlaybackDirection(state);
    togglePause(state);
    assert(state.mode == PlaybackMode::Reverse);

    // 6. Play backward 1 frame
    updateAdvancedPlayback(state, ts, 1.0 / 30.0, 60.0);
    double t_final = state.tCurrent;

    bool session_ok = (state.frameNumber >= 3) &&
                     (std::abs(t_paused - t_after_play) < 1e-10) &&  // Paused unchanged
                     (std::abs(t_after_seek - 1.0) < 1e-10) &&  // Seeked to first marker
                     (t_final < t_after_seek) &&  // Playing backward moves time down
                     (state.nMarkers == 2) &&
                     (state.interpolationCalls == 3);  // 2 forward + 1 backward (pause doesn't call update)

    std::cout << "  After 2 forward frames: t=" << std::fixed << std::setprecision(3) << t_after_play << "\n"
              << "  Paused at: t=" << t_paused << "\n"
              << "  Seeked to marker: t=" << t_after_seek << "\n"
              << "  After 1 reverse frame: t=" << t_final << "\n"
              << "  Total frames: " << state.frameNumber << "\n"
              << "  Markers: " << state.nMarkers << "\n"
              << "  Interpolation calls: " << state.interpolationCalls << "\n"
              << "  Status: " << (session_ok ? "PASS" : "FAIL") << "\n\n";

    return session_ok;
}

// ============================================================================
// Main Test Driver
// ============================================================================

int main() {
    std::cout << "\n====================================================\n"
              << "ADVANCED PLAYBACK CONTROL VALIDATION\n"
              << "Phase 8.1c: Playback Control & Timeline Management\n"
              << "====================================================\n";

    int passed = 0;
    int total = 7;

    if (test_playback_mode_transitions())  passed++;
    if (test_timeline_seeking())           passed++;
    if (test_frame_stepping())             passed++;
    if (test_timeline_markers())           passed++;
    if (test_reverse_playback())           passed++;
    if (test_performance_metrics())        passed++;
    if (test_complete_timeline_control())  passed++;

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
