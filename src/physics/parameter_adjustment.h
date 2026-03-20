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
    double scale{1.0};      // Multiplicative scale factor
    double offset{0.0};     // Additive offset
    double clampMin{-1.0};  // Minimum clamped value (-1 = no clamp)
    double clampMax{-1.0};  // Maximum clamped value (-1 = no clamp)
};

/**
 * @brief Real-time parameter adjustment state
 */
struct ParameterAdjustmentState {
    // Field modifiers (density, temperature, magnetic field, etc.)
    FieldModifier densityMod;
    FieldModifier temperatureMod;
    FieldModifier magneticFieldMod;
    FieldModifier otherMods[4];  // Up to 4 additional fields

    // Global modifiers
    double densityScale{1.0};      // Global density scaling
    double temperatureScale{1.0};  // Global temperature scaling
    bool enableAdjustments{true};  // Master enable/disable

    // Snapshot management
    uint32_t nSnapshots{0};
    uint32_t currentSnapshot{0};
    std::vector<ParameterAdjustmentState> snapshotHistory;
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
[[nodiscard]] inline double applyFieldModifier(double rawValue, const FieldModifier& modifier) {
    double modified = (rawValue * modifier.scale) + modifier.offset;

    if (modifier.clampMin >= 0.0) {
        modified = std::max(modified, modifier.clampMin);
    }
    if (modifier.clampMax >= 0.0) {
        modified = std::min(modified, modifier.clampMax);
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
[[nodiscard]] inline double adjustDensity(double rawDensity, const ParameterAdjustmentState& state) {
    if (!state.enableAdjustments) { return rawDensity; }

    const double scaled = rawDensity * state.densityScale;
    return applyFieldModifier(scaled, state.densityMod);
}

/**
 * @brief Adjust interpolated temperature field
 *
 * @param raw_temperature Raw interpolated temperature
 * @param state Parameter adjustment state
 * @return Adjusted temperature value
 */
[[nodiscard]] inline double adjustTemperature(double rawTemperature,
                                             const ParameterAdjustmentState& state) {
    if (!state.enableAdjustments) { return rawTemperature; }

    const double scaled = rawTemperature * state.temperatureScale;
    return applyFieldModifier(scaled, state.temperatureMod);
}

/**
 * @brief Adjust interpolated magnetic field
 *
 * @param raw_b_field Raw interpolated B-field magnitude
 * @param state Parameter adjustment state
 * @return Adjusted B-field value
 */
[[nodiscard]] inline double adjustMagneticField(double rawBField,
                                               const ParameterAdjustmentState& state) {
    if (!state.enableAdjustments) { return rawBField; }

    return applyFieldModifier(rawBField, state.magneticFieldMod);
}

/**
 * @brief Adjust additional field (indexed 0-3)
 *
 * @param raw_value Raw interpolated field value
 * @param field_index Index into other_mods array (0-3)
 * @param state Parameter adjustment state
 * @return Adjusted field value
 */
[[nodiscard]] inline double adjustOtherField(double rawValue,
                                            uint32_t fieldIndex,
                                            const ParameterAdjustmentState& state) {
    if (!state.enableAdjustments || fieldIndex >= 4) { return rawValue; }

    return applyFieldModifier(rawValue, state.otherMods[fieldIndex]);
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
inline void setDensityModifier(ParameterAdjustmentState& state,
                               double scale,
                               double offset = 0.0,
                               double minVal = -1.0,
                               double maxVal = -1.0) {
    state.densityMod.scale = scale;
    state.densityMod.offset = offset;
    state.densityMod.clampMin = minVal;
    state.densityMod.clampMax = maxVal;
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
inline void setTemperatureModifier(ParameterAdjustmentState& state,
                                   double scale,
                                   double offset = 0.0,
                                   double minVal = -1.0,
                                   double maxVal = -1.0) {
    state.temperatureMod.scale = scale;
    state.temperatureMod.offset = offset;
    state.temperatureMod.clampMin = minVal;
    state.temperatureMod.clampMax = maxVal;
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
inline void setMagneticFieldModifier(ParameterAdjustmentState& state,
                                     double scale,
                                     double offset = 0.0,
                                     double minVal = -1.0,
                                     double maxVal = -1.0) {
    state.magneticFieldMod.scale = scale;
    state.magneticFieldMod.offset = offset;
    state.magneticFieldMod.clampMin = minVal;
    state.magneticFieldMod.clampMax = maxVal;
}

/**
 * @brief Set global density scaling
 *
 * @param state Parameter adjustment state (modified in place)
 * @param scale Global density scale factor
 */
inline void setGlobalDensityScale(ParameterAdjustmentState& state, double scale) {
    state.densityScale = std::max(0.0, scale);
}

/**
 * @brief Set global temperature scaling
 *
 * @param state Parameter adjustment state (modified in place)
 * @param scale Global temperature scale factor
 */
inline void setGlobalTemperatureScale(ParameterAdjustmentState& state, double scale) {
    state.temperatureScale = std::max(0.0, scale);
}

/**
 * @brief Enable or disable all adjustments
 *
 * @param state Parameter adjustment state (modified in place)
 * @param enable Whether adjustments are active
 */
inline void setAdjustmentsEnabled(ParameterAdjustmentState& state, bool enable) {
    state.enableAdjustments = enable;
}

// ============================================================================
// Multi-Sequence Synchronization
// ============================================================================

/**
 * @brief Synchronized playback for multiple sequences
 */
struct SynchronizedPlaybackGroup {
    std::vector<AdvancedPlaybackState*> states;  // Pointers to playback states
    uint32_t nSequences{0};
    double masterTime{0.0};  // Master timeline time
    bool synchronized{true}; // Whether all states are locked to master
};

/**
 * @brief Create synchronized playback group
 *
 * @return New SynchronizedPlaybackGroup with no sequences
 */
[[nodiscard]] inline SynchronizedPlaybackGroup createSyncGroup() {
    return SynchronizedPlaybackGroup{};
}

/**
 * @brief Add playback state to synchronization group
 *
 * @param group Synchronized group (modified in place)
 * @param state Playback state to add
 * @return Whether addition was successful
 */
[[nodiscard]] inline bool addToSyncGroup(SynchronizedPlaybackGroup& group,
                                        AdvancedPlaybackState* state) {
    if (state == nullptr) { return false; }

    group.states.push_back(state);
    group.nSequences++;
    return true;
}

/**
 * @brief Clear all states from synchronization group
 *
 * @param group Synchronized group (modified in place)
 */
inline void clearSyncGroup(SynchronizedPlaybackGroup& group) {
    group.states.clear();
    group.nSequences = 0;
}

/**
 * @brief Seek all sequences in group to same time
 *
 * @param group Synchronized group
 * @param ts Time series metadata (same for all sequences)
 * @param t_seek Target seek time
 */
inline void syncSeekAll(SynchronizedPlaybackGroup& group,
                        const TimeSeriesMetadata& /* ts */,
                        double tSeek) {
    group.masterTime = tSeek;

    for (uint32_t i = 0; i < group.nSequences; i++) {
        if (group.states.at(i) != nullptr) {
            group.states.at(i)->tCurrent = tSeek;
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
inline void syncUpdateAll(SynchronizedPlaybackGroup& group,
                          const TimeSeriesMetadata& ts,
                          double dtFrame) {
    if (!group.synchronized || group.nSequences == 0) { return; }

    // Get master playback mode and speed from first state
    if (group.states.at(0) == nullptr) { return; }

    const AdvancedPlaybackState* const master = group.states.at(0);
    double dtSim = dtFrame * master->playbackSpeed;

    if (master->mode == PlaybackMode::Reverse) {
        dtSim = -(dtSim * master->reverseSpeed);
    }

    // Update master time (use ts for advance_time boundaries)
    if (master->mode != PlaybackMode::Stopped &&
        master->mode != PlaybackMode::PausedForward &&
        master->mode != PlaybackMode::PausedReverse) {
        group.masterTime = advance_time(ts, group.masterTime, dtSim, true);
    }

    // Sync all to master time
    for (uint32_t i = 0; i < group.nSequences; i++) {
        if (group.states.at(i) != nullptr) {
            group.states.at(i)->tCurrent = group.masterTime;
            group.states.at(i)->frameNumber = master->frameNumber;
            group.states.at(i)->mode = master->mode;
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
[[nodiscard]] inline ParameterAdjustmentState createParameterAdjustmentState() {
    return ParameterAdjustmentState{};
}

}  // namespace physics

#endif  // PARAMETER_ADJUSTMENT_H
