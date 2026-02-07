/**
 * @file parameter_adjustment.h
 * @brief Phase 9.1: Real-time Parameter Adjustment & Multi-Sequence Sync
 *
 * Enables live editing of GRMHD parameters during playback and
 * synchronization across multiple time series
 *
 * WHY: Interactive visualization requires real-time parameter modification
 * WHAT: Live density/temperature editing, multi-field adjustment, sequence sync
 * HOW: Parameter snapshots, field multipliers, synchronized playback states
 */

#ifndef PARAMETER_ADJUSTMENT_H
#define PARAMETER_ADJUSTMENT_H

#include "timeseries_interpolation.h"
#include "playback_control.h"
#include <vector>
#include <cmath>

namespace physics {

// ============================================================================
// Parameter Modifiers
// ============================================================================

/**
 * @brief Field scaling and offset adjustments
 */
struct FieldModifier {
    double scale;       // Multiplicative scale factor
    double offset;      // Additive offset
    double clamp_min;   // Minimum clamped value (-1 = no clamp)
    double clamp_max;   // Maximum clamped value (-1 = no clamp)
};

/**
 * @brief Real-time parameter adjustment state
 */
struct ParameterAdjustmentState {
    // Field modifiers (density, temperature, magnetic field, etc.)
    FieldModifier density_mod;
    FieldModifier temperature_mod;
    FieldModifier magnetic_field_mod;
    FieldModifier other_mods[4];  // Up to 4 additional fields

    // Global modifiers
    double density_scale;      // Global density scaling
    double temperature_scale;  // Global temperature scaling
    bool enable_adjustments;   // Master enable/disable

    // Snapshot management
    uint32_t n_snapshots;
    uint32_t current_snapshot;
    std::vector<ParameterAdjustmentState> snapshot_history;
};

// ============================================================================
// Field Value Adjustment
// ============================================================================

/**
 * @brief Apply field modifier to interpolated value
 *
 * @param raw_value Raw interpolated field value
 * @param modifier Modifier with scale, offset, clamping
 * @return Modified field value
 */
inline double apply_field_modifier(double raw_value, const FieldModifier& modifier) {
    double modified = raw_value * modifier.scale + modifier.offset;

    if (modifier.clamp_min >= 0.0) {
        modified = std::max(modified, modifier.clamp_min);
    }
    if (modifier.clamp_max >= 0.0) {
        modified = std::min(modified, modifier.clamp_max);
    }

    return modified;
}

/**
 * @brief Adjust interpolated density field
 *
 * @param raw_density Raw interpolated density
 * @param state Parameter adjustment state
 * @return Adjusted density value
 */
inline double adjust_density(double raw_density, const ParameterAdjustmentState& state) {
    if (!state.enable_adjustments) return raw_density;

    double scaled = raw_density * state.density_scale;
    return apply_field_modifier(scaled, state.density_mod);
}

/**
 * @brief Adjust interpolated temperature field
 *
 * @param raw_temperature Raw interpolated temperature
 * @param state Parameter adjustment state
 * @return Adjusted temperature value
 */
inline double adjust_temperature(double raw_temperature,
                                const ParameterAdjustmentState& state) {
    if (!state.enable_adjustments) return raw_temperature;

    double scaled = raw_temperature * state.temperature_scale;
    return apply_field_modifier(scaled, state.temperature_mod);
}

/**
 * @brief Adjust interpolated magnetic field
 *
 * @param raw_b_field Raw interpolated B-field magnitude
 * @param state Parameter adjustment state
 * @return Adjusted B-field value
 */
inline double adjust_magnetic_field(double raw_b_field,
                                   const ParameterAdjustmentState& state) {
    if (!state.enable_adjustments) return raw_b_field;

    return apply_field_modifier(raw_b_field, state.magnetic_field_mod);
}

/**
 * @brief Adjust additional field (indexed 0-3)
 *
 * @param raw_value Raw interpolated field value
 * @param field_index Index into other_mods array (0-3)
 * @param state Parameter adjustment state
 * @return Adjusted field value
 */
inline double adjust_other_field(double raw_value,
                                uint32_t field_index,
                                const ParameterAdjustmentState& state) {
    if (!state.enable_adjustments || field_index >= 4) return raw_value;

    return apply_field_modifier(raw_value, state.other_mods[field_index]);
}

// ============================================================================
// Parameter Control Functions
// ============================================================================

/**
 * @brief Set density field modifier
 *
 * @param state Parameter adjustment state (modified in place)
 * @param scale Multiplicative scale (1.0 = unchanged)
 * @param offset Additive offset (0.0 = no offset)
 * @param min_val Minimum clamped value (-1 = no clamp)
 * @param max_val Maximum clamped value (-1 = no clamp)
 */
inline void set_density_modifier(ParameterAdjustmentState& state,
                                double scale,
                                double offset = 0.0,
                                double min_val = -1.0,
                                double max_val = -1.0) {
    state.density_mod.scale = scale;
    state.density_mod.offset = offset;
    state.density_mod.clamp_min = min_val;
    state.density_mod.clamp_max = max_val;
}

/**
 * @brief Set temperature field modifier
 *
 * @param state Parameter adjustment state (modified in place)
 * @param scale Multiplicative scale (1.0 = unchanged)
 * @param offset Additive offset (0.0 = no offset)
 * @param min_val Minimum clamped value (-1 = no clamp)
 * @param max_val Maximum clamped value (-1 = no clamp)
 */
inline void set_temperature_modifier(ParameterAdjustmentState& state,
                                    double scale,
                                    double offset = 0.0,
                                    double min_val = -1.0,
                                    double max_val = -1.0) {
    state.temperature_mod.scale = scale;
    state.temperature_mod.offset = offset;
    state.temperature_mod.clamp_min = min_val;
    state.temperature_mod.clamp_max = max_val;
}

/**
 * @brief Set magnetic field modifier
 *
 * @param state Parameter adjustment state (modified in place)
 * @param scale Multiplicative scale (1.0 = unchanged)
 * @param offset Additive offset (0.0 = no offset)
 * @param min_val Minimum clamped value (-1 = no clamp)
 * @param max_val Maximum clamped value (-1 = no clamp)
 */
inline void set_magnetic_field_modifier(ParameterAdjustmentState& state,
                                       double scale,
                                       double offset = 0.0,
                                       double min_val = -1.0,
                                       double max_val = -1.0) {
    state.magnetic_field_mod.scale = scale;
    state.magnetic_field_mod.offset = offset;
    state.magnetic_field_mod.clamp_min = min_val;
    state.magnetic_field_mod.clamp_max = max_val;
}

/**
 * @brief Set global density scaling
 *
 * @param state Parameter adjustment state (modified in place)
 * @param scale Global density scale factor
 */
inline void set_global_density_scale(ParameterAdjustmentState& state, double scale) {
    state.density_scale = std::max(0.0, scale);
}

/**
 * @brief Set global temperature scaling
 *
 * @param state Parameter adjustment state (modified in place)
 * @param scale Global temperature scale factor
 */
inline void set_global_temperature_scale(ParameterAdjustmentState& state, double scale) {
    state.temperature_scale = std::max(0.0, scale);
}

/**
 * @brief Enable or disable all adjustments
 *
 * @param state Parameter adjustment state (modified in place)
 * @param enable Whether adjustments are active
 */
inline void set_adjustments_enabled(ParameterAdjustmentState& state, bool enable) {
    state.enable_adjustments = enable;
}

// ============================================================================
// Multi-Sequence Synchronization
// ============================================================================

/**
 * @brief Synchronized playback for multiple sequences
 */
struct SynchronizedPlaybackGroup {
    std::vector<AdvancedPlaybackState*> states;  // Pointers to playback states
    uint32_t n_sequences;
    double master_time;      // Master timeline time
    bool synchronized;       // Whether all states are locked to master
};

/**
 * @brief Create synchronized playback group
 *
 * @return New SynchronizedPlaybackGroup with no sequences
 */
inline SynchronizedPlaybackGroup create_sync_group() {
    SynchronizedPlaybackGroup group;
    group.n_sequences = 0;
    group.master_time = 0.0;
    group.synchronized = true;
    return group;
}

/**
 * @brief Add playback state to synchronization group
 *
 * @param group Synchronized group (modified in place)
 * @param state Playback state to add
 * @return Whether addition was successful
 */
inline bool add_to_sync_group(SynchronizedPlaybackGroup& group,
                             AdvancedPlaybackState* state) {
    if (state == nullptr) return false;

    group.states.push_back(state);
    group.n_sequences++;
    return true;
}

/**
 * @brief Clear all states from synchronization group
 *
 * @param group Synchronized group (modified in place)
 */
inline void clear_sync_group(SynchronizedPlaybackGroup& group) {
    group.states.clear();
    group.n_sequences = 0;
}

/**
 * @brief Seek all sequences in group to same time
 *
 * @param group Synchronized group
 * @param ts Time series metadata (same for all sequences)
 * @param t_seek Target seek time
 */
inline void sync_seek_all(SynchronizedPlaybackGroup& group,
                         const TimeSeriesMetadata& /* ts */,
                         double t_seek) {
    group.master_time = t_seek;

    for (uint32_t i = 0; i < group.n_sequences; i++) {
        if (group.states[i] != nullptr) {
            group.states[i]->t_current = t_seek;
        }
    }
}

/**
 * @brief Update all sequences in group synchronously
 *
 * @param group Synchronized group
 * @param ts Time series metadata (for boundary checking)
 * @param dt_frame Frame time delta
 */
inline void sync_update_all(SynchronizedPlaybackGroup& group,
                           const TimeSeriesMetadata& ts,
                           double dt_frame) {
    if (!group.synchronized || group.n_sequences == 0) return;

    // Get master playback mode and speed from first state
    if (group.states[0] == nullptr) return;

    AdvancedPlaybackState* master = group.states[0];
    double dt_sim = dt_frame * master->playback_speed;

    if (master->mode == PlaybackMode::Reverse) {
        dt_sim = -dt_sim * master->reverse_speed;
    }

    // Update master time (use ts for advance_time boundaries)
    if (master->mode != PlaybackMode::Stopped &&
        master->mode != PlaybackMode::PausedForward &&
        master->mode != PlaybackMode::PausedReverse) {
        group.master_time = advance_time(ts, group.master_time, dt_sim, true);
    }

    // Sync all to master time
    for (uint32_t i = 0; i < group.n_sequences; i++) {
        if (group.states[i] != nullptr) {
            group.states[i]->t_current = group.master_time;
            group.states[i]->frame_number = master->frame_number;
            group.states[i]->mode = master->mode;
        }
    }
}

// ============================================================================
// Initialization
// ============================================================================

/**
 * @brief Initialize parameter adjustment state with default values
 *
 * @return New ParameterAdjustmentState with all modifiers at neutral (1.0)
 */
inline ParameterAdjustmentState create_parameter_adjustment_state() {
    ParameterAdjustmentState state;

    // Initialize all modifiers to neutral (scale=1.0, offset=0.0)
    state.density_mod = {1.0, 0.0, -1.0, -1.0};
    state.temperature_mod = {1.0, 0.0, -1.0, -1.0};
    state.magnetic_field_mod = {1.0, 0.0, -1.0, -1.0};

    for (int i = 0; i < 4; i++) {
        state.other_mods[i] = {1.0, 0.0, -1.0, -1.0};
    }

    state.density_scale = 1.0;
    state.temperature_scale = 1.0;
    state.enable_adjustments = true;
    state.n_snapshots = 0;
    state.current_snapshot = 0;

    return state;
}

}  // namespace physics

#endif  // PARAMETER_ADJUSTMENT_H
