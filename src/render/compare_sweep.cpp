/**
 * @file compare_sweep.cpp
 * @brief Compute-vs-fragment parity sweep advance/restore state machine.
 */

#include "render/compare_sweep.h"

#include <algorithm>
#include <cstddef>

#include "input.h"                 // InputManager, CameraState
#include "render/render_state.h"   // RenderState
#include "tools/compare_harness.h" // K_COMPARE_PRESETS

namespace blackhole {

void advanceComparePresetSweep(RenderState &rs, InputManager &input, bool computeShadersAvailable) {
  rs.compare.comparePresetSettleFrames = std::clamp(rs.compare.comparePresetSettleFrames, 1, 10);
  bool const compareSweepAllowed = rs.compare.compareComputeFragment && computeShadersAvailable;
  if (rs.compare.comparePresetSweep && !compareSweepAllowed) {
    rs.compare.comparePresetSweep = false;
    if (rs.compare.comparePresetSaved) {
      rs.compare.compareRestorePending = true;
    }
  }
  if (rs.compare.comparePresetSweep) {
    if (!rs.compare.comparePresetSaved) {
      rs.compare.comparePresetSavedCamera = input.camera();
      rs.compare.comparePresetSavedMode = rs.camera.cameraModeIndex;
      rs.compare.comparePresetSavedOrbitRadius = rs.camera.orbitRadius;
      rs.compare.comparePresetSavedOrbitSpeed = rs.camera.orbitSpeed;
      rs.compare.comparePresetSavedOrbitTime = rs.camera.orbitTime;
      rs.compare.comparePresetSavedKerrSpin = rs.physicsCore.kerrSpin;
      rs.compare.comparePresetSaved = true;
    }
    int const presetCount = static_cast<int>(K_COMPARE_PRESETS.size());
    rs.compare.comparePresetIndex = std::clamp(rs.compare.comparePresetIndex, 0, presetCount);
    if (rs.compare.comparePresetIndex >= presetCount) {
      rs.compare.comparePresetSweep = false;
      rs.compare.compareRestorePending = true;
    } else {
      const auto &preset = K_COMPARE_PRESETS.at(static_cast<std::size_t>(rs.compare.comparePresetIndex));
      CameraState &camMutable = input.camera();
      camMutable = preset.camera;
      rs.camera.cameraModeIndex = static_cast<int>(preset.mode);
      rs.camera.orbitRadius = preset.orbitRadius;
      rs.camera.orbitSpeed = preset.orbitSpeed;
      rs.camera.orbitTime = 0.0f;
      rs.physicsCore.kerrSpin = preset.kerrSpin;
      rs.compare.comparePresetFrameCounter++;
      if (rs.compare.comparePresetFrameCounter >= rs.compare.comparePresetSettleFrames) {
        rs.compare.captureCompareSnapshot = true;
        rs.compare.comparePresetFrameCounter = 0;
        rs.compare.comparePresetIndex++;
        if (rs.compare.comparePresetIndex >= presetCount) {
          rs.compare.comparePresetSweep = false;
          rs.compare.compareRestorePending = true;
        }
      }
    }
  }
}

void restoreCompareSweepState(RenderState &rs, InputManager &input) {
  if (rs.compare.compareRestorePending && !rs.compare.comparePresetSweep && rs.compare.comparePresetSaved &&
      !rs.compare.captureCompareSnapshot) {
    CameraState &camMutable = input.camera();
    camMutable = rs.compare.comparePresetSavedCamera;
    rs.camera.cameraModeIndex = rs.compare.comparePresetSavedMode;
    rs.camera.orbitRadius = rs.compare.comparePresetSavedOrbitRadius;
    rs.camera.orbitSpeed = rs.compare.comparePresetSavedOrbitSpeed;
    rs.camera.orbitTime = rs.compare.comparePresetSavedOrbitTime;
    rs.physicsCore.kerrSpin = rs.compare.comparePresetSavedKerrSpin;
    rs.compare.comparePresetSaved = false;
    rs.compare.compareRestorePending = false;
  }
}

} // namespace blackhole
