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
    double timestamp{0.0};             // Global simulation time
    uint32_t frameNumber{0};           // Frame when snapshot was taken
    ParameterAdjustmentState state;    // Complete parameter state
};

/**
 * @brief Snapshot history and management
 */
struct SnapshotHistory {
    std::vector<ParameterSnapshot> snapshots;
    uint32_t nSnapshots{0};
    uint32_t currentSnapshotIdx{0};
    double maxHistoryTime{0.0};  // Max time span to keep (0 = unlimited)
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
 * @param frameNum Frame number
 * @return Index of created snapshot
 */
[[nodiscard]] inline uint32_t createSnapshot(SnapshotHistory& history,
                                            const ParameterAdjustmentState& state,
                                            double timestamp,
                                            uint32_t frameNum) {
    ParameterSnapshot snapshot;
    snapshot.timestamp = timestamp;
    snapshot.frameNumber = frameNum;
    snapshot.state = state;

    history.snapshots.push_back(snapshot);
    history.nSnapshots++;
    history.currentSnapshotIdx = history.nSnapshots - 1;

    return history.currentSnapshotIdx;
}

/**
 * @brief Restore state from snapshot
 *
 * @param history Snapshot history
 * @param snapshotIdx Index of snapshot to restore
 * @param state Parameter state to modify (modified in place)
 * @return Whether restoration was successful
 */
[[nodiscard]] inline bool restoreSnapshot(const SnapshotHistory& history,
                                         uint32_t snapshotIdx,
                                         ParameterAdjustmentState& state) {
    if (snapshotIdx >= history.nSnapshots) { return false; }

    state = history.snapshots.at(snapshotIdx).state;
    return true;
}

/**
 * @brief Clear all snapshots
 *
 * @param history Snapshot history (modified in place)
 */
inline void clearSnapshots(SnapshotHistory& history) {
    history.snapshots.clear();
    history.nSnapshots = 0;
    history.currentSnapshotIdx = 0;
}

/**
 * @brief Get number of snapshots
 *
 * @param history Snapshot history
 * @return Number of stored snapshots
 */
[[nodiscard]] inline uint32_t getSnapshotCount(const SnapshotHistory& history) {
    return history.nSnapshots;
}

/**
 * @brief Get timestamp of snapshot
 *
 * @param history Snapshot history
 * @param snapshotIdx Index of snapshot
 * @return Timestamp (-1 if invalid)
 */
[[nodiscard]] inline double getSnapshotTimestamp(const SnapshotHistory& history,
                                               uint32_t snapshotIdx) {
    if (snapshotIdx >= history.nSnapshots) { return -1.0; }
    return history.snapshots.at(snapshotIdx).timestamp;
}

// ============================================================================
// Temporal Parameter Interpolation
// ============================================================================

/**
 * @brief Linear interpolation of field modifier between two snapshots
 *
 * @param modA Modifier at time t_a
 * @param modB Modifier at time t_b
 * @param alpha Interpolation parameter [0, 1] where 0=a, 1=b
 * @return Interpolated modifier
 */
[[nodiscard]] inline FieldModifier interpolateModifier(const FieldModifier& modA,
                                                      const FieldModifier& modB,
                                                      double alpha) {
    FieldModifier result;
    result.scale = modA.scale + (alpha * (modB.scale - modA.scale));
    result.offset = modA.offset + (alpha * (modB.offset - modA.offset));
    result.clampMin = modA.clampMin + (alpha * (modB.clampMin - modA.clampMin));
    result.clampMax = modA.clampMax + (alpha * (modB.clampMax - modA.clampMax));
    return result;
}

/**
 * @brief Get interpolated parameter state between two snapshots
 *
 * @param snapA First snapshot
 * @param snapB Second snapshot
 * @param t Interpolation time (should be between snapA.timestamp and snapB.timestamp)
 * @return Interpolated parameter state
 */
[[nodiscard]] inline ParameterAdjustmentState interpolateSnapshots(const ParameterSnapshot& snapA,
                                                                  const ParameterSnapshot& snapB,
                                                                  double t) {
    const double tTotal = snapB.timestamp - snapA.timestamp;
    double alpha = 0.0;

    if (tTotal > 1e-10) {
        alpha = (t - snapA.timestamp) / tTotal;
        alpha = std::max(0.0, std::min(1.0, alpha));  // Clamp to [0, 1]
    }

    ParameterAdjustmentState result;
    result.densityMod = interpolateModifier(snapA.state.densityMod,
                                             snapB.state.densityMod, alpha);
    result.temperatureMod = interpolateModifier(snapA.state.temperatureMod,
                                                 snapB.state.temperatureMod, alpha);
    result.magneticFieldMod = interpolateModifier(snapA.state.magneticFieldMod,
                                                    snapB.state.magneticFieldMod, alpha);

    for (int i = 0; i < 4; i++) {
        result.otherMods[i] = interpolateModifier(snapA.state.otherMods[i],
                                                   snapB.state.otherMods[i], alpha);
    }

    result.densityScale =
        snapA.state.densityScale + (alpha * (snapB.state.densityScale - snapA.state.densityScale));
    result.temperatureScale =
        snapA.state.temperatureScale +
        (alpha * (snapB.state.temperatureScale - snapA.state.temperatureScale));

    // Use current enable state (from snap_a)
    result.enableAdjustments = snapA.state.enableAdjustments;
    result.nSnapshots = snapA.state.nSnapshots;
    result.currentSnapshot = snapA.state.currentSnapshot;

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
[[nodiscard]] inline bool getInterpolatedStateAtTime(const SnapshotHistory& history,
                                                    double t,
                                                    ParameterAdjustmentState& result) {
    if (history.nSnapshots == 0) { return false; }

    // Find bracketing snapshots
    uint32_t idxLeft = 0;
    uint32_t idxRight = 0;
    bool found = false;

    for (uint32_t i = 0; i < history.nSnapshots - 1; i++) {
        if (history.snapshots.at(i).timestamp <= t &&
            t <= history.snapshots.at(i + 1).timestamp) {
            idxLeft = i;
            idxRight = i + 1;
            found = true;
            break;
        }
    }

    if (!found) {
        // Out of range - clamp to nearest snapshot
        if (t < history.snapshots.at(0).timestamp) {
            result = history.snapshots.at(0).state;
        } else {
            result = history.snapshots.at(history.nSnapshots - 1).state;
        }
        return true;
    }

    // Interpolate between bracketing snapshots
    result = interpolateSnapshots(history.snapshots.at(idxLeft),
                                  history.snapshots.at(idxRight),
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
[[nodiscard]] inline bool goToNextSnapshot(SnapshotHistory& history,
                                          ParameterAdjustmentState& state) {
    if (history.currentSnapshotIdx + 1 >= history.nSnapshots) {
        return false;  // Already at last snapshot
    }

    history.currentSnapshotIdx++;
    return restoreSnapshot(history, history.currentSnapshotIdx, state);
}

/**
 * @brief Move to previous snapshot
 *
 * @param history Snapshot history (modified in place)
 * @param state Parameter state to update (modified in place)
 * @return Whether successful
 */
[[nodiscard]] inline bool goToPreviousSnapshot(SnapshotHistory& history,
                                              ParameterAdjustmentState& state) {
    if (history.currentSnapshotIdx == 0) {
        return false;  // Already at first snapshot
    }

    history.currentSnapshotIdx--;
    return restoreSnapshot(history, history.currentSnapshotIdx, state);
}

/**
 * @brief Find snapshot nearest to time
 *
 * @param history Snapshot history
 * @param t Query time
 * @return Index of nearest snapshot (-1 if none)
 */
[[nodiscard]] inline uint32_t findNearestSnapshot(const SnapshotHistory& history, double t) {
    if (history.nSnapshots == 0) { return UINT32_MAX; }

    uint32_t nearest = 0;
    double minDistance = std::abs(history.snapshots.at(0).timestamp - t);

    for (uint32_t i = 1; i < history.nSnapshots; i++) {
        const double distance = std::abs(history.snapshots.at(i).timestamp - t);
        if (distance < minDistance) {
            minDistance = distance;
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
 * @param maxTime Maximum time span to keep (0 = unlimited)
 * @return New SnapshotHistory
 */
[[nodiscard]] inline SnapshotHistory createSnapshotHistory(double maxTime = 0.0) {
    SnapshotHistory history;
    history.maxHistoryTime = maxTime;
    return history;
}

}  // namespace physics

#endif  // PARAMETER_SNAPSHOTS_H
