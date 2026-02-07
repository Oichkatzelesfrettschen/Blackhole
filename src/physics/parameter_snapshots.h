/**
 * @file parameter_snapshots.h
 * @brief Phase 9.2: Snapshot Management & Parameter History
 *
 * Enables saving/restoring parameter states and temporal interpolation
 * of adjustments across snapshot points
 *
 * WHY: Interactive visualization requires parameter undo/redo and smooth transitions
 * WHAT: Snapshot history, temporal parameter interpolation, state management
 * HOW: Time-stamped snapshots with linear interpolation between states
 */

#ifndef PARAMETER_SNAPSHOTS_H
#define PARAMETER_SNAPSHOTS_H

#include "parameter_adjustment.h"
#include <vector>
#include <cmath>
#include <algorithm>
#include <cstdint>

namespace physics {

// ============================================================================
// Snapshot Structures
// ============================================================================

/**
 * @brief Time-stamped parameter snapshot
 */
struct ParameterSnapshot {
    double timestamp;                  // Global simulation time
    uint32_t frame_number;             // Frame when snapshot was taken
    ParameterAdjustmentState state;    // Complete parameter state
};

/**
 * @brief Snapshot history and management
 */
struct SnapshotHistory {
    std::vector<ParameterSnapshot> snapshots;
    uint32_t n_snapshots;
    uint32_t current_snapshot_idx;
    double max_history_time;  // Max time span to keep (0 = unlimited)
};

// ============================================================================
// Snapshot Management
// ============================================================================

/**
 * @brief Create snapshot of current parameter state
 *
 * @param history Snapshot history (modified in place)
 * @param state Current parameter adjustment state
 * @param timestamp Time to associate with snapshot
 * @param frame_num Frame number
 * @return Index of created snapshot
 */
inline uint32_t create_snapshot(SnapshotHistory& history,
                               const ParameterAdjustmentState& state,
                               double timestamp,
                               uint32_t frame_num) {
    ParameterSnapshot snapshot;
    snapshot.timestamp = timestamp;
    snapshot.frame_number = frame_num;
    snapshot.state = state;

    history.snapshots.push_back(snapshot);
    history.n_snapshots++;
    history.current_snapshot_idx = history.n_snapshots - 1;

    return history.current_snapshot_idx;
}

/**
 * @brief Restore state from snapshot
 *
 * @param history Snapshot history
 * @param snapshot_idx Index of snapshot to restore
 * @param state Parameter state to modify (modified in place)
 * @return Whether restoration was successful
 */
inline bool restore_snapshot(const SnapshotHistory& history,
                            uint32_t snapshot_idx,
                            ParameterAdjustmentState& state) {
    if (snapshot_idx >= history.n_snapshots) return false;

    state = history.snapshots[snapshot_idx].state;
    return true;
}

/**
 * @brief Clear all snapshots
 *
 * @param history Snapshot history (modified in place)
 */
inline void clear_snapshots(SnapshotHistory& history) {
    history.snapshots.clear();
    history.n_snapshots = 0;
    history.current_snapshot_idx = 0;
}

/**
 * @brief Get number of snapshots
 *
 * @param history Snapshot history
 * @return Number of stored snapshots
 */
inline uint32_t get_snapshot_count(const SnapshotHistory& history) {
    return history.n_snapshots;
}

/**
 * @brief Get timestamp of snapshot
 *
 * @param history Snapshot history
 * @param snapshot_idx Index of snapshot
 * @return Timestamp (-1 if invalid)
 */
inline double get_snapshot_timestamp(const SnapshotHistory& history,
                                    uint32_t snapshot_idx) {
    if (snapshot_idx >= history.n_snapshots) return -1.0;
    return history.snapshots[snapshot_idx].timestamp;
}

// ============================================================================
// Temporal Parameter Interpolation
// ============================================================================

/**
 * @brief Linear interpolation of field modifier between two snapshots
 *
 * @param mod_a Modifier at time t_a
 * @param mod_b Modifier at time t_b
 * @param alpha Interpolation parameter [0, 1] where 0=a, 1=b
 * @return Interpolated modifier
 */
inline FieldModifier interpolate_modifier(const FieldModifier& mod_a,
                                         const FieldModifier& mod_b,
                                         double alpha) {
    FieldModifier result;
    result.scale = mod_a.scale + alpha * (mod_b.scale - mod_a.scale);
    result.offset = mod_a.offset + alpha * (mod_b.offset - mod_a.offset);
    result.clamp_min = mod_a.clamp_min + alpha * (mod_b.clamp_min - mod_a.clamp_min);
    result.clamp_max = mod_a.clamp_max + alpha * (mod_b.clamp_max - mod_a.clamp_max);
    return result;
}

/**
 * @brief Get interpolated parameter state between two snapshots
 *
 * @param snap_a First snapshot
 * @param snap_b Second snapshot
 * @param t Interpolation time (should be between snap_a.timestamp and snap_b.timestamp)
 * @return Interpolated parameter state
 */
inline ParameterAdjustmentState interpolate_snapshots(const ParameterSnapshot& snap_a,
                                                      const ParameterSnapshot& snap_b,
                                                      double t) {
    double t_total = snap_b.timestamp - snap_a.timestamp;
    double alpha = 0.0;

    if (t_total > 1e-10) {
        alpha = (t - snap_a.timestamp) / t_total;
        alpha = std::max(0.0, std::min(1.0, alpha));  // Clamp to [0, 1]
    }

    ParameterAdjustmentState result;
    result.density_mod = interpolate_modifier(snap_a.state.density_mod,
                                             snap_b.state.density_mod, alpha);
    result.temperature_mod = interpolate_modifier(snap_a.state.temperature_mod,
                                                 snap_b.state.temperature_mod, alpha);
    result.magnetic_field_mod = interpolate_modifier(snap_a.state.magnetic_field_mod,
                                                    snap_b.state.magnetic_field_mod, alpha);

    for (int i = 0; i < 4; i++) {
        result.other_mods[i] = interpolate_modifier(snap_a.state.other_mods[i],
                                                   snap_b.state.other_mods[i], alpha);
    }

    result.density_scale = snap_a.state.density_scale +
                         alpha * (snap_b.state.density_scale - snap_a.state.density_scale);
    result.temperature_scale = snap_a.state.temperature_scale +
                              alpha * (snap_b.state.temperature_scale - snap_a.state.temperature_scale);

    // Use current enable state (from snap_a)
    result.enable_adjustments = snap_a.state.enable_adjustments;
    result.n_snapshots = snap_a.state.n_snapshots;
    result.current_snapshot = snap_a.state.current_snapshot;

    return result;
}

/**
 * @brief Get interpolated state at specific time using history
 *
 * @param history Snapshot history
 * @param t Query time
 * @param result Parameter state to populate (modified in place)
 * @return Whether interpolation was successful
 */
inline bool get_interpolated_state_at_time(const SnapshotHistory& history,
                                          double t,
                                          ParameterAdjustmentState& result) {
    if (history.n_snapshots == 0) return false;

    // Find bracketing snapshots
    uint32_t idx_left = 0, idx_right = 0;
    bool found = false;

    for (uint32_t i = 0; i < history.n_snapshots - 1; i++) {
        if (history.snapshots[i].timestamp <= t &&
            t <= history.snapshots[i + 1].timestamp) {
            idx_left = i;
            idx_right = i + 1;
            found = true;
            break;
        }
    }

    if (!found) {
        // Out of range - clamp to nearest snapshot
        if (t < history.snapshots[0].timestamp) {
            result = history.snapshots[0].state;
        } else {
            result = history.snapshots[history.n_snapshots - 1].state;
        }
        return true;
    }

    // Interpolate between bracketing snapshots
    result = interpolate_snapshots(history.snapshots[idx_left],
                                  history.snapshots[idx_right],
                                  t);
    return true;
}

// ============================================================================
// Snapshot Navigation
// ============================================================================

/**
 * @brief Move to next snapshot
 *
 * @param history Snapshot history (modified in place)
 * @param state Parameter state to update (modified in place)
 * @return Whether successful
 */
inline bool go_to_next_snapshot(SnapshotHistory& history,
                               ParameterAdjustmentState& state) {
    if (history.current_snapshot_idx + 1 >= history.n_snapshots) {
        return false;  // Already at last snapshot
    }

    history.current_snapshot_idx++;
    return restore_snapshot(history, history.current_snapshot_idx, state);
}

/**
 * @brief Move to previous snapshot
 *
 * @param history Snapshot history (modified in place)
 * @param state Parameter state to update (modified in place)
 * @return Whether successful
 */
inline bool go_to_previous_snapshot(SnapshotHistory& history,
                                   ParameterAdjustmentState& state) {
    if (history.current_snapshot_idx == 0) {
        return false;  // Already at first snapshot
    }

    history.current_snapshot_idx--;
    return restore_snapshot(history, history.current_snapshot_idx, state);
}

/**
 * @brief Find snapshot nearest to time
 *
 * @param history Snapshot history
 * @param t Query time
 * @return Index of nearest snapshot (-1 if none)
 */
inline uint32_t find_nearest_snapshot(const SnapshotHistory& history, double t) {
    if (history.n_snapshots == 0) return UINT32_MAX;

    uint32_t nearest = 0;
    double min_distance = std::abs(history.snapshots[0].timestamp - t);

    for (uint32_t i = 1; i < history.n_snapshots; i++) {
        double distance = std::abs(history.snapshots[i].timestamp - t);
        if (distance < min_distance) {
            min_distance = distance;
            nearest = i;
        }
    }

    return nearest;
}

// ============================================================================
// Initialization
// ============================================================================

/**
 * @brief Initialize snapshot history
 *
 * @param max_time Maximum time span to keep (0 = unlimited)
 * @return New SnapshotHistory
 */
inline SnapshotHistory create_snapshot_history(double max_time = 0.0) {
    SnapshotHistory history;
    history.n_snapshots = 0;
    history.current_snapshot_idx = 0;
    history.max_history_time = max_time;
    return history;
}

}  // namespace physics

#endif  // PARAMETER_SNAPSHOTS_H
