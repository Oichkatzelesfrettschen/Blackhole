/**
 * @file playback_control.h
 * @brief Phase 8.1c: Advanced Playback Control & Timeline Management
 *
 * Enables rich playback control: seeking, reverse playback, frame stepping,
 * timeline scrubbing, and synchronization across multiple time-series
 *
 * WHY: Interactive visualization requires precise timeline control and sync
 * WHAT: Seeking, reverse playback, frame stepping, scrubbing, multi-series sync
 * HOW: Timeline state machine with playback modes and seek operations
 */

#ifndef PLAYBACK_CONTROL_H
#define PLAYBACK_CONTROL_H

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <vector>

#include "timeseries_interpolation.h"

namespace physics {

// ============================================================================
// Playback Modes and States
// ============================================================================

enum class PlaybackMode {
    Stopped,      // Not playing
    Forward,      // Playing forward
    Reverse,      // Playing backward
    PausedForward,  // Paused while in forward mode
    PausedReverse   // Paused while in reverse mode
};

/**
 * @brief Extended playback state with advanced features
 */
struct AdvancedPlaybackState {
    // Core timeline state
    double tCurrent{};          // Current playback time
    double tTarget{};           // Target time for seeking (ease to target)
    PlaybackMode mode{};        // Current playback mode

    // Playback control
    double playbackSpeed{};     // Speed multiplier (1.0 = real-time)
    double reverseSpeed{};      // Reverse speed multiplier (separate from forward)
    bool loop{};                // Loop when reaching end
    bool reverseAtEnds{};       // Reverse direction at boundaries instead of wrapping

    // Frame tracking
    uint32_t frameNumber{};     // Frame counter (counts all frames, not reset on wrap)
    uint32_t frameCount{};      // Total frames rendered (for performance)
    double frameTimeMs{};       // Time to render last frame (milliseconds)

    // Timeline markers
    uint32_t nMarkers{};             // Number of timeline markers
    std::vector<double> markers;     // Marker times
    uint32_t currentMarker{};        // Index of nearest marker

    // Performance metrics
    double avgInterpolationTime{};   // Average interpolation cost (microseconds)
    double peakInterpolationTime{};  // Peak interpolation cost
    uint32_t interpolationCalls{};   // Total interpolation function calls
};

// ============================================================================
// Timeline Seeking and Scrubbing
// ============================================================================

/**
 * @brief Seek to specific time in timeline
 *
 * @param state Playback state (modified in place)
 * @param ts Time series metadata
 * @param t_seek Target seek time
 * @param ease_frames Number of frames to ease to target (smooth seeking)
 * @return Whether seek was successful
 */
[[nodiscard]] inline bool seekTimeline(AdvancedPlaybackState& state,
                                        const TimeSeriesMetadata& ts,
                                        double tSeek,
                                        uint32_t easeFrames = 0) {
    if ((tSeek < ts.tStart) || (tSeek > ts.tEnd)) {
        return false;  // Out of bounds
    }

    if (easeFrames == 0) {
        // Immediate seek
        state.tCurrent = tSeek;
    } else {
        // Eased seek (gradual transition)
        state.tTarget = tSeek;
    }

    return true;
}

/**
 * @brief Seek to frame number
 *
 * @param state Playback state
 * @param ts Time series metadata
 * @param frame_index Target frame (0-based)
 * @return Whether seek was successful
 */
[[nodiscard]] inline bool seekToFrame(AdvancedPlaybackState& state,
                                       const TimeSeriesMetadata& ts,
                                       uint32_t frameIndex) {
    if (ts.nDumps < 2) {
        return false;
    }

    // Assume uniform frame spacing in time range
    const double dtPerFrame = (ts.tEnd - ts.tStart) / (ts.nDumps - 1);
    const double tSeek = ts.tStart + (frameIndex * dtPerFrame);

    return seekTimeline(state, ts, tSeek, 0);
}

/**
 * @brief Seek to nearest timeline marker
 *
 * @param state Playback state
 * @param ts Time series metadata
 * @param forward If true, seek to next marker; if false, seek to previous
 * @return Whether seek was successful
 */
[[nodiscard]] inline bool seekToMarker(AdvancedPlaybackState& state,
                                        const TimeSeriesMetadata& ts,
                                        bool forward) {
    if (state.nMarkers == 0) {
        return false;
    }

    double nearestMarker = state.markers.at(0);
    uint32_t nearestIdx = 0;

    if (forward) {
        // Find next marker after current time
        for (uint32_t i = 0; i < state.nMarkers; i++) {
            if (state.markers.at(i) > state.tCurrent) {
                nearestMarker = state.markers.at(i);
                nearestIdx = i;
                break;
            }
        }
    } else {
        // Find previous marker before current time
        for (uint32_t i = state.nMarkers; i > 0; i--) {
            if (state.markers.at(i - 1) < state.tCurrent) {
                nearestMarker = state.markers.at(i - 1);
                nearestIdx = i - 1;
                break;
            }
        }
    }

    state.currentMarker = nearestIdx;
    return seekTimeline(state, ts, nearestMarker, 0);
}

// ============================================================================
// Playback Mode Control
// ============================================================================

/**
 * @brief Set playback mode
 *
 * @param state Playback state (modified in place)
 * @param mode New playback mode
 */
inline void setPlaybackMode(AdvancedPlaybackState& state, PlaybackMode mode) {
    state.mode = mode;
}

/**
 * @brief Toggle pause (pause if playing, resume if paused)
 *
 * @param state Playback state (modified in place)
 */
inline void togglePause(AdvancedPlaybackState& state) {
    if (state.mode == PlaybackMode::Forward) {
        state.mode = PlaybackMode::PausedForward;
    } else if (state.mode == PlaybackMode::Reverse) {
        state.mode = PlaybackMode::PausedReverse;
    } else if (state.mode == PlaybackMode::PausedForward) {
        state.mode = PlaybackMode::Forward;
    } else if (state.mode == PlaybackMode::PausedReverse) {
        state.mode = PlaybackMode::Reverse;
    }
}

/**
 * @brief Reverse playback direction (forward -> reverse or vice versa)
 *
 * @param state Playback state (modified in place)
 */
inline void reversePlaybackDirection(AdvancedPlaybackState& state) {
    if (state.mode == PlaybackMode::Forward) {
        state.mode = PlaybackMode::Reverse;
    } else if (state.mode == PlaybackMode::Reverse) {
        state.mode = PlaybackMode::Forward;
    } else if (state.mode == PlaybackMode::PausedForward) {
        state.mode = PlaybackMode::PausedReverse;
    } else if (state.mode == PlaybackMode::PausedReverse) {
        state.mode = PlaybackMode::PausedForward;
    }
}

// ============================================================================
// Frame Stepping
// ============================================================================

/**
 * @brief Step forward by single frame
 *
 * @param state Playback state (modified in place)
 * @param ts Time series metadata
 */
inline void stepFrameForward(AdvancedPlaybackState& state,
                              const TimeSeriesMetadata& ts) {
    if (ts.nDumps < 2) {
        return;
    }

    const double dtPerFrame = (ts.tEnd - ts.tStart) / (ts.nDumps - 1);
    state.tCurrent = advanceTime(ts, state.tCurrent, dtPerFrame, state.loop);
    state.frameNumber++;
}

/**
 * @brief Step backward by single frame
 *
 * @param state Playback state (modified in place)
 * @param ts Time series metadata
 */
inline void stepFrameBackward(AdvancedPlaybackState& state,
                               const TimeSeriesMetadata& ts) {
    if (ts.nDumps < 2) {
        return;
    }

    const double dtPerFrame = (ts.tEnd - ts.tStart) / (ts.nDumps - 1);
    double tPrev = state.tCurrent - dtPerFrame;

    if (tPrev < ts.tStart) {
        if (state.loop) {
            tPrev = ts.tEnd + (tPrev - ts.tStart);
        } else {
            tPrev = ts.tStart;
        }
    }

    state.tCurrent = tPrev;
    state.frameNumber++;
}

// ============================================================================
// Advanced Playback Update
// ============================================================================

/**
 * @brief Update playback state with mode-aware time stepping
 *
 * @param state Playback state (modified in place)
 * @param ts Time series metadata
 * @param dt_frame Wall clock frame time in seconds
 * @param interp_time_us Time spent in interpolation (microseconds)
 */
inline void updateAdvancedPlayback(AdvancedPlaybackState& state,
                                    const TimeSeriesMetadata& ts,
                                    double dtFrame,
                                    double interpTimeUs = 0.0) {
    // Update performance metrics
    state.frameTimeMs = dtFrame * 1000.0;
    state.interpolationCalls++;

    if (interpTimeUs > 0.0) {
        // Update interpolation statistics
        if (state.interpolationCalls == 1) {
            state.avgInterpolationTime = interpTimeUs;
        } else {
            // Moving average
            const uint32_t n = state.interpolationCalls;
            state.avgInterpolationTime =
                ((state.avgInterpolationTime * (n - 1)) + interpTimeUs) / n;
        }

        state.peakInterpolationTime = std::max(state.peakInterpolationTime, interpTimeUs);
    }

    // Handle paused states
    if ((state.mode == PlaybackMode::PausedForward) ||
        (state.mode == PlaybackMode::PausedReverse) ||
        (state.mode == PlaybackMode::Stopped)) {
        return;  // No time advancement when paused
    }

    // Determine effective playback speed and direction
    double speed = state.playbackSpeed;
    if (state.mode == PlaybackMode::Reverse) {
        speed = -(state.reverseSpeed);
    }

    // Handle target seeking (eased seek)
    if (std::abs(state.tTarget - state.tCurrent) > 1e-10) {
        // Smoothly ease to target time
        const double dtSim = dtFrame * speed;
        const double newT  = state.tCurrent + dtSim;

        if (((speed > 0) && (newT >= state.tTarget)) ||
            ((speed < 0) && (newT <= state.tTarget))) {
            state.tCurrent = state.tTarget;
        } else {
            state.tCurrent = newT;
        }
    } else {
        // Normal playback
        const double dtSim = dtFrame * speed;

        if (state.mode == PlaybackMode::Forward) {
            state.tCurrent = advanceTime(ts, state.tCurrent, dtSim, state.loop);

            // Reverse at boundaries if enabled
            if (state.reverseAtEnds && (state.tCurrent >= ts.tEnd)) {
                state.mode = PlaybackMode::Reverse;
            }
        } else if (state.mode == PlaybackMode::Reverse) {
            double tPrev = state.tCurrent + dtSim;  // dtSim is negative

            if (tPrev < ts.tStart) {
                if (state.loop) {
                    tPrev = ts.tEnd + (tPrev - ts.tStart);
                } else if (state.reverseAtEnds) {
                    state.mode = PlaybackMode::Forward;
                    tPrev = ts.tStart;
                } else {
                    tPrev = ts.tStart;
                }
            }

            state.tCurrent = tPrev;
        }
    }

    state.frameNumber++;
}

// ============================================================================
// Timeline Marker Management
// ============================================================================

/**
 * @brief Add marker to timeline
 *
 * @param state Playback state (modified in place)
 * @param t_marker Marker time
 * @param ts Time series metadata (for bounds checking)
 * @return Whether marker was added (false if out of bounds)
 */
[[nodiscard]] inline bool addTimelineMarker(AdvancedPlaybackState& state,
                                             double tMarker,
                                             const TimeSeriesMetadata& ts) {
    if ((tMarker < ts.tStart) || (tMarker > ts.tEnd)) {
        return false;  // Out of bounds
    }

    state.markers.push_back(tMarker);
    state.nMarkers++;

    // Keep markers sorted
    std::ranges::sort(state.markers);

    return true;
}

/**
 * @brief Clear all timeline markers
 *
 * @param state Playback state (modified in place)
 */
inline void clearTimelineMarkers(AdvancedPlaybackState& state) {
    state.markers.clear();
    state.nMarkers = 0;
    state.currentMarker = 0;
}

/**
 * @brief Get time to next or previous marker
 *
 * @param state Playback state
 * @param forward If true, distance to next marker; if false, to previous
 * @return Distance in time units (negative if no marker exists in direction)
 */
[[nodiscard]] inline double timeToMarker(const AdvancedPlaybackState& state, bool forward) {
    if (state.nMarkers == 0) {
        return -1.0;
    }

    if (forward) {
        for (uint32_t i = 0; i < state.nMarkers; i++) {
            if (state.markers.at(i) > state.tCurrent) {
                return state.markers.at(i) - state.tCurrent;
            }
        }
        return -1.0;  // No marker ahead
    }

    for (uint32_t i = state.nMarkers; i > 0; i--) {
        if (state.markers.at(i - 1) < state.tCurrent) {
            return state.tCurrent - state.markers.at(i - 1);
        }
    }
    return -1.0;  // No marker behind
}

// ============================================================================
// Initialization
// ============================================================================

/**
 * @brief Initialize advanced playback state
 *
 * @param ts Time series metadata
 * @param speed Initial playback speed
 * @return New AdvancedPlaybackState
 */
[[nodiscard]] inline AdvancedPlaybackState createAdvancedPlaybackState(
    const TimeSeriesMetadata& ts,
    double speed = 1.0) {
    AdvancedPlaybackState state;
    state.tCurrent              = ts.tStart;
    state.tTarget               = ts.tStart;
    state.mode                  = PlaybackMode::Stopped;
    state.playbackSpeed         = speed;
    state.reverseSpeed          = speed;
    state.loop                  = true;
    state.reverseAtEnds         = false;
    state.frameNumber           = 0;
    state.frameCount            = 0;
    state.frameTimeMs           = 0.0;
    state.nMarkers              = 0;
    state.currentMarker         = 0;
    state.avgInterpolationTime  = 0.0;
    state.peakInterpolationTime = 0.0;
    state.interpolationCalls    = 0;
    return state;
}

}  // namespace physics

#endif  // PLAYBACK_CONTROL_H
