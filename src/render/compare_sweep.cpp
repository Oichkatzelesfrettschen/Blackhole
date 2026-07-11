/**
 * @file compare_sweep.cpp
 * @brief Compute-vs-fragment parity sweep advance/restore state machine.
 */

#include "render/compare_sweep.h"

#include <algorithm>
#include <cstddef>
#include <string>
#include <utility>
#include <vector>

#include "input.h"                 // InputManager, CameraState
#include "render/render_state.h"   // RenderState
#include "tools/compare_harness.h" // K_COMPARE_PRESETS, DiffStats, snapshot/CSV writers

using namespace gl;

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

void captureCompareParity(RenderState &rs, const CompareParityInputs &in) {
  if (in.compareActive && in.fragmentTarget != 0 && in.computeTarget != 0) {
    if (rs.compare.compareAutoCapture && rs.compare.compareAutoRemaining > 0) {
      rs.compare.compareAutoStrideCounter++;
      if (rs.compare.compareAutoStrideCounter >= rs.compare.compareAutoStride) {
        rs.compare.captureCompareSnapshot = true;
        rs.compare.compareAutoStrideCounter = 0;
        rs.compare.compareAutoRemaining--;
        if (rs.compare.compareAutoRemaining <= 0) {
          rs.compare.compareAutoCapture = false;
        }
      }
    }

    if (++rs.compare.compareFrameCounter >= rs.compare.compareFrameStride) {
      rs.compare.compareStats =
          sampleTextureDiff(rs.targets.texBlackhole, rs.targets.texBlackholeCompare, rs.targets.renderWidth,
                            rs.targets.renderHeight, // NOLINT(readability-suspicious-call-argument) --
                                          // order is correct: primary then compare
                            rs.compare.compareSampleSize);
      rs.compare.compareFrameCounter = 0;
    }

    if (rs.compare.captureCompareSnapshot) {
      std::vector<float> primary;
      std::vector<float> secondary;
      if (readTextureRGBA(rs.targets.texBlackhole, rs.targets.renderWidth, rs.targets.renderHeight, primary) &&
          readTextureRGBA(rs.targets.texBlackholeCompare, rs.targets.renderWidth, rs.targets.renderHeight, secondary)) {
        rs.compare.compareFullStats = computeDiffStats(primary, secondary);
        std::size_t const outlierCount =
            countDiffOutliers(primary, secondary, rs.compare.compareThreshold);
        std::size_t const totalPixels = primary.size() / 4;
        std::size_t limitFromFrac = 0;
        if (rs.compare.compareMaxOutlierFrac > 0.0f && totalPixels > 0) {
          limitFromFrac =
              static_cast<std::size_t>(static_cast<double>(rs.compare.compareMaxOutlierFrac) *
                                       static_cast<double>(totalPixels));
        }
        std::size_t const limitFromCount =
            static_cast<std::size_t>(std::max(rs.compare.compareMaxOutliers, 0));
        std::size_t const outlierLimit = std::max(limitFromCount, limitFromFrac);
        rs.compare.compareLastOutliers = static_cast<int>(outlierCount);
        rs.compare.compareLastOutlierLimit = static_cast<int>(outlierLimit);
        float const outlierFrac = totalPixels > 0 ? static_cast<float>(outlierCount) /
                                                        static_cast<float>(totalPixels)
                                                  : 0.0f;
        bool const outlierGateEnabled =
            (rs.compare.compareMaxOutliers > 0) || (rs.compare.compareMaxOutlierFrac > 0.0f);
        rs.compare.compareLastExceeded = rs.compare.compareFullStats.valid &&
                              rs.compare.compareFullStats.maxAbs > rs.compare.compareThreshold &&
                              (!outlierGateEnabled || outlierCount > outlierLimit);
        if (rs.compare.compareLastExceeded) {
          ++rs.compare.compareFailureCount;
        }

        const bool computeIsPrimary = (in.computeTarget == rs.targets.texBlackhole);
        const std::string primaryTag = computeIsPrimary ? "compute" : "fragment";
        const std::string secondaryTag = computeIsPrimary ? "fragment" : "compute";
        std::string presetLabel = "custom";
        if (rs.compare.compareSnapshotIndex >= 0 &&
            std::cmp_less(rs.compare.compareSnapshotIndex, K_COMPARE_PRESETS.size())) {
          presetLabel =
              K_COMPARE_PRESETS.at(static_cast<std::size_t>(rs.compare.compareSnapshotIndex)).label;
        }

        if (rs.compare.compareWriteOutputs) {
          writePpm(compareSnapshotPath(rs.compare.compareSnapshotIndex, primaryTag), primary,
                   rs.targets.renderWidth, rs.targets.renderHeight, 1.0f);
          writePpm(compareSnapshotPath(rs.compare.compareSnapshotIndex, secondaryTag), secondary,
                   rs.targets.renderWidth, rs.targets.renderHeight, 1.0f);
        }
        if (rs.compare.compareWriteDiff) {
          writeDiffPpm(compareSnapshotPath(rs.compare.compareSnapshotIndex, "diff"), primary,
                       secondary, rs.targets.renderWidth, rs.targets.renderHeight, rs.compare.compareDiffScale);
        }
        if (rs.compare.compareWriteSummary) {
          appendCompareSummary(compareSummaryPath(), rs.compare.compareSnapshotIndex, primaryTag,
                               secondaryTag, rs.targets.renderWidth, rs.targets.renderHeight, rs.compare.compareFullStats,
                               rs.compare.compareDiffScale, rs.compare.compareWriteOutputs, rs.compare.compareWriteDiff,
                               rs.compare.compareThreshold, rs.compare.compareLastExceeded, in.timeSec,
                               rs.physicsCore.kerrSpin, in.grbModulationEnabled, in.grbTimeSeconds,
                               rs.compare.compareLastOutliers, rs.compare.compareLastOutlierLimit, outlierFrac);
          appendCompareUniforms(compareUniformsPath(), rs.compare.compareSnapshotIndex, presetLabel,
                                in.interop, in.compareBaselineActive, rs.compare.compareOverridesEnabled,
                                in.backgroundEnabledEffective, in.noiseReady, in.grmhdEnabled,
                                in.spectralEnabled, in.grbModulationEnabled,
                                in.enablePhotonSphereEffective);
        }
        rs.compare.compareSnapshotIndex++;
      } else {
        rs.compare.compareFullStats.valid = false;
        rs.compare.compareLastExceeded = false;
      }
      rs.compare.captureCompareSnapshot = false;
    }
  } else {
    rs.compare.compareStats.valid = false;
    rs.compare.compareFullStats.valid = false;
    rs.compare.captureCompareSnapshot = false;
    rs.compare.compareLastExceeded = false;
    rs.compare.compareLastOutliers = 0;
    rs.compare.compareLastOutlierLimit = 0;
  }
}

} // namespace blackhole
