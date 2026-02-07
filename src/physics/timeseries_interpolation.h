/**
 * @file timeseries_interpolation.h
 * @brief Phase 8.1a: Time Series Metadata & Temporal Interpolation
 *
 * Handles multi-dump GRMHD time series with linear and higher-order interpolation
 *
 * WHY: Enable smooth animation between discrete simulation snapshots
 * WHAT: Time metadata, interpolation coefficients, smooth field evolution
 * HOW: Linear and cubic Hermite spline interpolation between dumps
 */

#ifndef TIMESERIES_INTERPOLATION_H
#define TIMESERIES_INTERPOLATION_H

#include <vector>
#include <cmath>
#include <algorithm>
#include <cstdint>

namespace physics {

// ============================================================================
// Time Metadata
// ============================================================================

/**
 * @brief Single GRMHD dump metadata
 */
struct DumpMetadata {
    double time;           // Code time unit
    double dt;             // Time step to next dump
    uint32_t dump_number;  // Sequential index
    uint32_t fields_offset; // Byte offset in field storage
};

/**
 * @brief Time series metadata for multiple dumps
 */
struct TimeSeriesMetadata {
    std::vector<DumpMetadata> dumps;
    double t_start;     // Earliest time
    double t_end;       // Latest time
    uint32_t n_dumps;   // Total number of dumps
    double frequency;   // Time sampling frequency (Hz in code units)
};

// ============================================================================
// Interpolation Data
// ============================================================================

/**
 * @brief Interpolation state for current time
 */
struct InterpolationState {
    uint32_t dump_left;    // Index of left dump
    uint32_t dump_right;   // Index of right dump
    double alpha;          // Interpolation parameter [0, 1]
    double time_current;   // Current interpolation time
    bool is_valid;         // Whether interpolation is within bounds
};

/**
 * @brief Hermite spline coefficients for smooth interpolation
 */
struct HermiteCoefficients {
    double h00, h10, h01, h11;  // Basis functions
    double dh00, dh10, dh01, dh11;  // Derivatives
};

// ============================================================================
// Time Series Management
// ============================================================================

/**
 * @brief Build time series metadata from dump array
 *
 * @param times Array of simulation times for each dump
 * @param n_dumps Number of dumps
 * @return TimeSeriesMetadata structure
 */
inline TimeSeriesMetadata build_timeseries_metadata(const double* times, uint32_t n_dumps) {
    TimeSeriesMetadata ts;
    ts.n_dumps = n_dumps;

    for (uint32_t i = 0; i < n_dumps; i++) {
        DumpMetadata dm;
        dm.time = times[i];
        dm.dump_number = i;
        dm.fields_offset = 0;  // Would be set during actual file loading

        if (i < n_dumps - 1) {
            dm.dt = times[i + 1] - times[i];
        } else {
            dm.dt = 0.0;  // Last dump
        }

        ts.dumps.push_back(dm);
    }

    if (n_dumps > 0) {
        ts.t_start = times[0];
        ts.t_end = times[n_dumps - 1];
        ts.frequency = 1.0 / ((ts.t_end - ts.t_start) / (n_dumps - 1));
    } else {
        ts.t_start = ts.t_end = 0.0;
        ts.frequency = 0.0;
    }

    return ts;
}

// ============================================================================
// Interpolation Calculation
// ============================================================================

/**
 * @brief Find interpolation state for given time
 *
 * @param ts Time series metadata
 * @param t_query Query time
 * @return InterpolationState with left/right dumps and alpha
 */
inline InterpolationState get_interpolation_state(const TimeSeriesMetadata& ts, double t_query) {
    InterpolationState state;
    state.time_current = t_query;
    state.is_valid = false;

    // Clamp to valid range
    if (t_query < ts.t_start) {
        state.dump_left = 0;
        state.dump_right = 0;
        state.alpha = 0.0;
        return state;
    }

    if (t_query > ts.t_end) {
        state.dump_left = ts.n_dumps - 1;
        state.dump_right = ts.n_dumps - 1;
        state.alpha = 1.0;
        return state;
    }

    // Binary search for bracketing dumps
    for (uint32_t i = 0; i < ts.n_dumps - 1; i++) {
        if (ts.dumps[i].time <= t_query && t_query <= ts.dumps[i + 1].time) {
            state.dump_left = i;
            state.dump_right = i + 1;

            double dt = ts.dumps[i + 1].time - ts.dumps[i].time;
            if (dt > 0.0) {
                state.alpha = (t_query - ts.dumps[i].time) / dt;
            } else {
                state.alpha = 0.0;
            }

            state.is_valid = true;
            return state;
        }
    }

    // Fallback: use last dump
    state.dump_left = ts.n_dumps - 1;
    state.dump_right = ts.n_dumps - 1;
    state.alpha = 1.0;
    state.is_valid = true;

    return state;
}

/**
 * @brief Linear interpolation coefficient
 *
 * result = (1 - alpha) * f_left + alpha * f_right
 *
 * @param alpha Interpolation parameter [0, 1]
 * @param f_left Left value
 * @param f_right Right value
 * @return Interpolated value
 */
inline double linear_interpolate(double alpha, double f_left, double f_right) {
    return (1.0 - alpha) * f_left + alpha * f_right;
}

/**
 * @brief Cubic Hermite spline interpolation
 *
 * Uses Catmull-Rom spline for smooth C1-continuous interpolation
 * Requires values at 4 points: p0, p1, p2, p3
 * Interpolates between p1 and p2 using tangent estimates from p0/p3
 *
 * @param t Normalized time parameter [0, 1]
 * @param p0 Value at t=-1
 * @param p1 Value at t=0
 * @param p2 Value at t=1
 * @param p3 Value at t=2
 * @return Interpolated value at t
 */
inline double hermite_interpolate(double t, double p0, double p1, double p2, double p3) {
    // Catmull-Rom tangent vectors
    double m0 = 0.5 * (p2 - p0);
    double m1 = 0.5 * (p3 - p1);

    // Hermite basis functions
    double t2 = t * t;
    double t3 = t2 * t;

    double h00 = 2.0 * t3 - 3.0 * t2 + 1.0;
    double h10 = t3 - 2.0 * t2 + t;
    double h01 = -2.0 * t3 + 3.0 * t2;
    double h11 = t3 - t2;

    return h00 * p1 + h10 * m0 + h01 * p2 + h11 * m1;
}

// ============================================================================
// Multi-Field Interpolation
// ============================================================================

/**
 * @brief Interpolate scalar field value at time t
 *
 * @param ts Time series metadata
 * @param field_values Array of field values at each dump
 * @param t_query Query time
 * @param use_hermite Use Hermite spline (true) vs linear (false)
 * @return Interpolated field value
 */
inline double interpolate_field(const TimeSeriesMetadata& ts,
                                const double* field_values,
                                double t_query,
                                bool use_hermite = false) {
    InterpolationState state = get_interpolation_state(ts, t_query);

    if (!state.is_valid) {
        return field_values[state.dump_left];
    }

    if (!use_hermite) {
        // Linear interpolation
        return linear_interpolate(state.alpha,
                                 field_values[state.dump_left],
                                 field_values[state.dump_right]);
    }

    // Hermite interpolation (requires 4 points)
    if (state.dump_left == 0 || state.dump_right >= ts.n_dumps - 1) {
        // At boundaries, fall back to linear
        return linear_interpolate(state.alpha,
                                 field_values[state.dump_left],
                                 field_values[state.dump_right]);
    }

    double p0 = field_values[state.dump_left - 1];
    double p1 = field_values[state.dump_left];
    double p2 = field_values[state.dump_right];
    double p3 = field_values[state.dump_right + 1];

    return hermite_interpolate(state.alpha, p0, p1, p2, p3);
}

// ============================================================================
// Time Advancement
// ============================================================================

/**
 * @brief Advance time by dt, handling wrap-around
 *
 * @param ts Time series metadata
 * @param t_current Current time
 * @param dt Time step
 * @param wrap_around If true, loop from end to start; if false, clamp at end
 * @return Advanced time
 */
inline double advance_time(const TimeSeriesMetadata& ts, double t_current,
                          double dt, bool wrap_around = true) {
    double t_next = t_current + dt;

    if (t_next > ts.t_end) {
        if (wrap_around) {
            // Loop back to start
            double period = ts.t_end - ts.t_start;
            t_next = ts.t_start + std::fmod(t_next - ts.t_start, period);
        } else {
            // Clamp at end
            t_next = ts.t_end;
        }
    }

    return t_next;
}

// ============================================================================
// Playback Control
// ============================================================================

/**
 * @brief Playback state for time series animation
 */
struct PlaybackState {
    double t_current;      // Current playback time
    double playback_speed; // Speed multiplier (1.0 = real-time)
    bool is_playing;       // Whether animation is running
    bool loop;             // Whether to loop when reaching end
    uint32_t frame_number; // Current frame number
};

/**
 * @brief Initialize playback state
 *
 * @param ts Time series metadata
 * @param speed Playback speed multiplier
 * @return Initial PlaybackState
 */
inline PlaybackState create_playback_state(const TimeSeriesMetadata& ts, double speed = 1.0) {
    PlaybackState ps;
    ps.t_current = ts.t_start;
    ps.playback_speed = speed;
    ps.is_playing = false;
    ps.loop = true;
    ps.frame_number = 0;
    return ps;
}

/**
 * @brief Update playback state for one frame
 *
 * @param ps PlaybackState (modified in place)
 * @param ts Time series metadata
 * @param dt_frame Frame time step (real time)
 */
inline void update_playback(PlaybackState& ps, const TimeSeriesMetadata& ts, double dt_frame) {
    if (!ps.is_playing) return;

    double dt_sim = dt_frame * ps.playback_speed;
    ps.t_current = advance_time(ts, ps.t_current, dt_sim, ps.loop);
    ps.frame_number++;
}

}  // namespace physics

#endif  // TIMESERIES_INTERPOLATION_H
