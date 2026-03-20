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

#include <cmath>
#include <cstdint>
#include <vector>

namespace physics {

// ============================================================================
// Time Metadata
// ============================================================================

/**
 * @brief Single GRMHD dump metadata
 */
struct DumpMetadata {
    double time{0.0};          // Code time unit
    double dt{0.0};            // Time step to next dump
    uint32_t dumpNumber{0};    // Sequential index
    uint32_t fieldsOffset{0};  // Byte offset in field storage
};

/**
 * @brief Time series metadata for multiple dumps
 */
struct TimeSeriesMetadata {
    std::vector<DumpMetadata> dumps;
    double tStart{0.0};     // Earliest time
    double tEnd{0.0};       // Latest time
    uint32_t nDumps{0};     // Total number of dumps
    double frequency{0.0};  // Time sampling frequency (Hz in code units)
};

// ============================================================================
// Interpolation Data
// ============================================================================

/**
 * @brief Interpolation state for current time
 */
struct InterpolationState {
    uint32_t dumpLeft{0};     // Index of left dump
    uint32_t dumpRight{0};    // Index of right dump
    double alpha{0.0};        // Interpolation parameter [0, 1]
    double timeCurrent{0.0};  // Current interpolation time
    bool isValid{false};      // Whether interpolation is within bounds
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
[[nodiscard]] inline TimeSeriesMetadata buildTimeseriesMetadata(const double* times, uint32_t nDumps) {
    TimeSeriesMetadata ts;
    ts.nDumps = nDumps;

    for (uint32_t i = 0; i < nDumps; i++) {
        DumpMetadata dm;
        dm.time = times[i];
        dm.dumpNumber = i;
        dm.fieldsOffset = 0;  // Would be set during actual file loading

        if (i < nDumps - 1) {
            dm.dt = times[i + 1] - times[i];
        } else {
            dm.dt = 0.0;  // Last dump
        }

        ts.dumps.push_back(dm);
    }

    if (nDumps > 0) {
        ts.tStart = times[0];
        ts.tEnd = times[nDumps - 1];
        ts.frequency = 1.0 / ((ts.tEnd - ts.tStart) / static_cast<double>(nDumps - 1));
    } else {
        ts.tStart = ts.tEnd = 0.0;
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
[[nodiscard]] inline InterpolationState getInterpolationState(const TimeSeriesMetadata& ts, double tQuery) {
    InterpolationState state;
    state.timeCurrent = tQuery;

    // Clamp to valid range
    if (tQuery < ts.tStart) {
        return state;
    }

    if (tQuery > ts.tEnd) {
        state.dumpLeft = ts.nDumps - 1;
        state.dumpRight = ts.nDumps - 1;
        state.alpha = 1.0;
        return state;
    }

    // Binary search for bracketing dumps
    for (uint32_t i = 0; i < ts.nDumps - 1; i++) {
        if (ts.dumps.at(i).time <= tQuery && tQuery <= ts.dumps.at(i + 1).time) {
            state.dumpLeft = i;
            state.dumpRight = i + 1;

            const double dt = ts.dumps.at(i + 1).time - ts.dumps.at(i).time;
            if (dt > 0.0) {
                state.alpha = (tQuery - ts.dumps.at(i).time) / dt;
            }

            state.isValid = true;
            return state;
        }
    }

    // Fallback: use last dump
    state.dumpLeft = ts.nDumps - 1;
    state.dumpRight = ts.nDumps - 1;
    state.alpha = 1.0;
    state.isValid = true;

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
[[nodiscard]] inline double linearInterpolate(double alpha, double fLeft, double fRight) {
    return ((1.0 - alpha) * fLeft) + (alpha * fRight);
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
[[nodiscard]] inline double hermiteInterpolate(double t, double p0, double p1, double p2, double p3) {
    // Catmull-Rom tangent vectors
    const double m0 = 0.5 * (p2 - p0);
    const double m1 = 0.5 * (p3 - p1);

    // Hermite basis functions
    const double t2 = t * t;
    const double t3 = t2 * t;

    const double h00 = (2.0 * t3) - (3.0 * t2) + 1.0;
    const double h10 = t3 - (2.0 * t2) + t;
    const double h01 = (-2.0 * t3) + (3.0 * t2);
    const double h11 = t3 - t2;

    return (h00 * p1) + (h10 * m0) + (h01 * p2) + (h11 * m1);
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
[[nodiscard]] inline double interpolateField(const TimeSeriesMetadata& ts,
                                             const double* fieldValues,
                                             double tQuery,
                                             bool useHermite = false) {
    const InterpolationState state = getInterpolationState(ts, tQuery);

    if (!state.isValid) {
        return fieldValues[state.dumpLeft];
    }

    if (!useHermite) {
        return linearInterpolate(state.alpha,
                                 fieldValues[state.dumpLeft],
                                 fieldValues[state.dumpRight]);
    }

    // Hermite interpolation (requires 4 points)
    if (state.dumpLeft == 0 || state.dumpRight >= ts.nDumps - 1) {
        // At boundaries, fall back to linear
        return linearInterpolate(state.alpha,
                                 fieldValues[state.dumpLeft],
                                 fieldValues[state.dumpRight]);
    }

    const double p0 = fieldValues[state.dumpLeft - 1];
    const double p1 = fieldValues[state.dumpLeft];
    const double p2 = fieldValues[state.dumpRight];
    const double p3 = fieldValues[state.dumpRight + 1];

    return hermiteInterpolate(state.alpha, p0, p1, p2, p3);
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
[[nodiscard]] inline double advanceTime(const TimeSeriesMetadata& ts, double tCurrent,
                                       double dt, bool wrapAround = true) {
    double tNext = tCurrent + dt;

    if (tNext > ts.tEnd) {
        if (wrapAround) {
            // Loop back to start
            const double period = ts.tEnd - ts.tStart;
            tNext = ts.tStart + std::fmod(tNext - ts.tStart, period);
        } else {
            // Clamp at end
            tNext = ts.tEnd;
        }
    }

    return tNext;
}

// ============================================================================
// Playback Control
// ============================================================================

/**
 * @brief Playback state for time series animation
 */
struct PlaybackState {
    double tCurrent{0.0};      // Current playback time
    double playbackSpeed{1.0}; // Speed multiplier (1.0 = real-time)
    bool isPlaying{false};     // Whether animation is running
    bool loop{true};           // Whether to loop when reaching end
    uint32_t frameNumber{0};   // Current frame number
};

/**
 * @brief Initialize playback state
 *
 * @param ts Time series metadata
 * @param speed Playback speed multiplier
 * @return Initial PlaybackState
 */
[[nodiscard]] inline PlaybackState createPlaybackState(const TimeSeriesMetadata& ts, double speed = 1.0) {
    PlaybackState ps;
    ps.tCurrent = ts.tStart;
    ps.playbackSpeed = speed;
    return ps;
}

/**
 * @brief Update playback state for one frame
 *
 * @param ps PlaybackState (modified in place)
 * @param ts Time series metadata
 * @param dt_frame Frame time step (real time)
 */
inline void updatePlayback(PlaybackState& ps, const TimeSeriesMetadata& ts, double dtFrame) {
    if (!ps.isPlaying) { return; }

    const double dtSim = dtFrame * ps.playbackSpeed;
    ps.tCurrent = advanceTime(ts, ps.tCurrent, dtSim, ps.loop);
    ps.frameNumber++;
}

}  // namespace physics

#endif  // TIMESERIES_INTERPOLATION_H
