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

#include "timeseries_interpolation.h"
#include <cmath>
#include <algorithm>
#include <vector>

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
    double t_current;        // Current playback time
    double t_target;         // Target time for seeking (ease to target)
    PlaybackMode mode;       // Current playback mode

    // Playback control
    double playback_speed;   // Speed multiplier (1.0 = real-time)
    double reverse_speed;    // Reverse speed multiplier (separate from forward)
    bool loop;               // Loop when reaching end
    bool reverse_at_ends;    // Reverse direction at boundaries instead of wrapping

    // Frame tracking
    uint32_t frame_number;   // Frame counter (counts all frames, not reset on wrap)
    uint32_t frame_count;    // Total frames rendered (for performance)
    double frame_time_ms;    // Time to render last frame (milliseconds)

    // Timeline markers
    uint32_t n_markers;      // Number of timeline markers
    std::vector<double> markers;  // Marker times
    uint32_t current_marker; // Index of nearest marker

    // Performance metrics
    double avg_interpolation_time;  // Average interpolation cost (microseconds)
    double peak_interpolation_time; // Peak interpolation cost
    uint32_t interpolation_calls;   // Total interpolation function calls
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
inline bool seek_timeline(AdvancedPlaybackState& state,
                         const TimeSeriesMetadata& ts,
                         double t_seek,
                         uint32_t ease_frames = 0) {
    if (t_seek < ts.t_start || t_seek > ts.t_end) {
        return false;  // Out of bounds
    }

    if (ease_frames == 0) {
        // Immediate seek
        state.t_current = t_seek;
    } else {
        // Eased seek (gradual transition)
        state.t_target = t_seek;
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
inline bool seek_to_frame(AdvancedPlaybackState& state,
                         const TimeSeriesMetadata& ts,
                         uint32_t frame_index) {
    if (ts.n_dumps < 2) return false;

    // Assume uniform frame spacing in time range
    double dt_per_frame = (ts.t_end - ts.t_start) / (ts.n_dumps - 1);
    double t_seek = ts.t_start + frame_index * dt_per_frame;

    return seek_timeline(state, ts, t_seek, 0);
}

/**
 * @brief Seek to nearest timeline marker
 *
 * @param state Playback state
 * @param ts Time series metadata
 * @param forward If true, seek to next marker; if false, seek to previous
 * @return Whether seek was successful
 */
inline bool seek_to_marker(AdvancedPlaybackState& state,
                          const TimeSeriesMetadata& ts,
                          bool forward) {
    if (state.n_markers == 0) return false;

    double nearest_marker = state.markers[0];
    uint32_t nearest_idx = 0;

    if (forward) {
        // Find next marker after current time
        for (uint32_t i = 0; i < state.n_markers; i++) {
            if (state.markers[i] > state.t_current) {
                nearest_marker = state.markers[i];
                nearest_idx = i;
                break;
            }
        }
    } else {
        // Find previous marker before current time
        for (uint32_t i = state.n_markers; i > 0; i--) {
            if (state.markers[i - 1] < state.t_current) {
                nearest_marker = state.markers[i - 1];
                nearest_idx = i - 1;
                break;
            }
        }
    }

    state.current_marker = nearest_idx;
    return seek_timeline(state, ts, nearest_marker, 0);
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
inline void set_playback_mode(AdvancedPlaybackState& state, PlaybackMode mode) {
    state.mode = mode;
}

/**
 * @brief Toggle pause (pause if playing, resume if paused)
 *
 * @param state Playback state (modified in place)
 */
inline void toggle_pause(AdvancedPlaybackState& state) {
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
inline void reverse_playback_direction(AdvancedPlaybackState& state) {
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
inline void step_frame_forward(AdvancedPlaybackState& state,
                              const TimeSeriesMetadata& ts) {
    if (ts.n_dumps < 2) return;

    double dt_per_frame = (ts.t_end - ts.t_start) / (ts.n_dumps - 1);
    double t_next = advance_time(ts, state.t_current, dt_per_frame, state.loop);
    state.t_current = t_next;
    state.frame_number++;
}

/**
 * @brief Step backward by single frame
 *
 * @param state Playback state (modified in place)
 * @param ts Time series metadata
 */
inline void step_frame_backward(AdvancedPlaybackState& state,
                               const TimeSeriesMetadata& ts) {
    if (ts.n_dumps < 2) return;

    double dt_per_frame = (ts.t_end - ts.t_start) / (ts.n_dumps - 1);
    double t_prev = state.t_current - dt_per_frame;

    if (t_prev < ts.t_start) {
        if (state.loop) {
            t_prev = ts.t_end + (t_prev - ts.t_start);
        } else {
            t_prev = ts.t_start;
        }
    }

    state.t_current = t_prev;
    state.frame_number++;
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
inline void update_advanced_playback(AdvancedPlaybackState& state,
                                    const TimeSeriesMetadata& ts,
                                    double dt_frame,
                                    double interp_time_us = 0.0) {
    // Update performance metrics
    state.frame_time_ms = dt_frame * 1000.0;
    state.interpolation_calls++;

    if (interp_time_us > 0.0) {
        // Update interpolation statistics
        if (state.interpolation_calls == 1) {
            state.avg_interpolation_time = interp_time_us;
        } else {
            // Moving average
            uint32_t n = state.interpolation_calls;
            state.avg_interpolation_time =
                (state.avg_interpolation_time * (n - 1) + interp_time_us) / n;
        }

        state.peak_interpolation_time = std::max(state.peak_interpolation_time,
                                                 interp_time_us);
    }

    // Handle paused states
    if (state.mode == PlaybackMode::PausedForward ||
        state.mode == PlaybackMode::PausedReverse ||
        state.mode == PlaybackMode::Stopped) {
        return;  // No time advancement when paused
    }

    // Determine effective playback speed and direction
    double speed = state.playback_speed;
    if (state.mode == PlaybackMode::Reverse) {
        speed = -state.reverse_speed;
    }

    // Handle target seeking (eased seek)
    if (std::abs(state.t_target - state.t_current) > 1e-10) {
        // Smoothly ease to target time
        double dt_sim = dt_frame * speed;
        double new_t = state.t_current + dt_sim;

        if ((speed > 0 && new_t >= state.t_target) ||
            (speed < 0 && new_t <= state.t_target)) {
            state.t_current = state.t_target;
        } else {
            state.t_current = new_t;
        }
    } else {
        // Normal playback
        double dt_sim = dt_frame * speed;

        if (state.mode == PlaybackMode::Forward) {
            state.t_current = advance_time(ts, state.t_current, dt_sim, state.loop);

            // Reverse at boundaries if enabled
            if (state.reverse_at_ends && state.t_current >= ts.t_end) {
                state.mode = PlaybackMode::Reverse;
            }
        } else if (state.mode == PlaybackMode::Reverse) {
            double t_prev = state.t_current + dt_sim;  // dt_sim is negative

            if (t_prev < ts.t_start) {
                if (state.loop) {
                    t_prev = ts.t_end + (t_prev - ts.t_start);
                } else if (state.reverse_at_ends) {
                    state.mode = PlaybackMode::Forward;
                    t_prev = ts.t_start;
                } else {
                    t_prev = ts.t_start;
                }
            }

            state.t_current = t_prev;
        }
    }

    state.frame_number++;
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
inline bool add_timeline_marker(AdvancedPlaybackState& state,
                               double t_marker,
                               const TimeSeriesMetadata& ts) {
    if (t_marker < ts.t_start || t_marker > ts.t_end) {
        return false;  // Out of bounds
    }

    state.markers.push_back(t_marker);
    state.n_markers++;

    // Keep markers sorted
    std::sort(state.markers.begin(), state.markers.end());

    return true;
}

/**
 * @brief Clear all timeline markers
 *
 * @param state Playback state (modified in place)
 */
inline void clear_timeline_markers(AdvancedPlaybackState& state) {
    state.markers.clear();
    state.n_markers = 0;
    state.current_marker = 0;
}

/**
 * @brief Get time to next or previous marker
 *
 * @param state Playback state
 * @param forward If true, distance to next marker; if false, to previous
 * @return Distance in time units (negative if no marker exists in direction)
 */
inline double time_to_marker(const AdvancedPlaybackState& state, bool forward) {
    if (state.n_markers == 0) return -1.0;

    if (forward) {
        for (uint32_t i = 0; i < state.n_markers; i++) {
            if (state.markers[i] > state.t_current) {
                return state.markers[i] - state.t_current;
            }
        }
        return -1.0;  // No marker ahead
    } else {
        for (uint32_t i = state.n_markers; i > 0; i--) {
            if (state.markers[i - 1] < state.t_current) {
                return state.t_current - state.markers[i - 1];
            }
        }
        return -1.0;  // No marker behind
    }
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
inline AdvancedPlaybackState create_advanced_playback_state(
    const TimeSeriesMetadata& ts,
    double speed = 1.0) {
    AdvancedPlaybackState state;
    state.t_current = ts.t_start;
    state.t_target = ts.t_start;
    state.mode = PlaybackMode::Stopped;
    state.playback_speed = speed;
    state.reverse_speed = speed;
    state.loop = true;
    state.reverse_at_ends = false;
    state.frame_number = 0;
    state.frame_count = 0;
    state.frame_time_ms = 0.0;
    state.n_markers = 0;
    state.current_marker = 0;
    state.avg_interpolation_time = 0.0;
    state.peak_interpolation_time = 0.0;
    state.interpolation_calls = 0;
    return state;
}

}  // namespace physics

#endif  // PLAYBACK_CONTROL_H
