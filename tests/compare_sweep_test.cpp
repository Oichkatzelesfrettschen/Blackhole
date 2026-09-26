/**
 * @file compare_sweep_test.cpp
 * @brief State-machine tests for the compute-vs-fragment parity sweep.
 *
 * advanceComparePresetSweep and restoreCompareSweepState were loop-inline code
 * that never ran under a runnable gate in the headless sandbox (the sweep needs
 * a focused window and compute shaders to complete). Extracting them into
 * compare_sweep.* makes the state machine a pure function of RenderState and
 * InputManager; these GL-free tests drive the sweep across presets and assert
 * preset advancement, the settle-boundary capture flag, the compute-unavailable
 * disable path, the post-sweep camera restore, and the cancel a scene change
 * applies mid-sweep. They link the test-only
 * blackhole_testcore library so RenderState can be constructed without the app
 * executables.
 */

#include <memory>

#include <gtest/gtest.h>

#include "input.h"
#include "render/compare_sweep.h"
#include "render/render_state.h"
#include "tools/compare_harness.h"

using blackhole::advanceComparePresetSweep;
using blackhole::K_COMPARE_PRESETS;
using blackhole::RenderState;
using blackhole::restoreCompareSweepState;
using blackhole::updateComparePresetSweep;

namespace {

// Puts rs into an armed sweep with a known live camera and returns the frame
// count of the preset table.
int armSweep(RenderState &rs, InputManager &input) {
  input.camera() =
      CameraState{.yaw = 12.0f, .pitch = 34.0f, .roll = 5.0f, .distance = 42.0f, .fov = 55.0f};
  rs.camera.cameraModeIndex = 2;
  rs.camera.orbitRadius = 9.0f;
  rs.camera.orbitSpeed = 3.0f;
  rs.camera.orbitTime = 1.5f;
  rs.physicsCore.kerrSpin = 0.44f;
  rs.compare.compareComputeFragment = true;
  rs.compare.comparePresetSweep = true;
  rs.compare.comparePresetSaved = false;
  rs.compare.comparePresetIndex = 0;
  rs.compare.comparePresetFrameCounter = 0;
  rs.compare.captureCompareSnapshot = false;
  rs.compare.compareRestorePending = false;
  return static_cast<int>(K_COMPARE_PRESETS.size());
}

} // namespace

// Compute shaders unavailable: an armed sweep is disabled and, once a camera was
// saved, a restore is requested rather than the sweep silently proceeding.
TEST(CompareSweep, DisablesWhenComputeUnavailable) {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  InputManager &input = InputManager::instance();
  armSweep(rs, input);
  rs.compare.comparePresetSaved = true; // a prior frame already saved the camera

  advanceComparePresetSweep(rs, input, /*computeShadersAvailable=*/false);

  EXPECT_FALSE(rs.compare.comparePresetSweep);
  EXPECT_TRUE(rs.compare.compareRestorePending);
}

// First advance saves the live camera exactly once and applies preset 0.
TEST(CompareSweep, SavesLiveCameraOnEntry) {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  InputManager &input = InputManager::instance();
  armSweep(rs, input);

  advanceComparePresetSweep(rs, input, /*computeShadersAvailable=*/true);

  EXPECT_TRUE(rs.compare.comparePresetSaved);
  EXPECT_FLOAT_EQ(rs.compare.comparePresetSavedCamera.yaw, 12.0f);
  EXPECT_FLOAT_EQ(rs.compare.comparePresetSavedCamera.distance, 42.0f);
  EXPECT_EQ(rs.compare.comparePresetSavedMode, 2);
  EXPECT_FLOAT_EQ(rs.compare.comparePresetSavedKerrSpin, 0.44f);
  // Preset 0 has been applied to the live camera.
  EXPECT_FLOAT_EQ(input.camera().yaw, K_COMPARE_PRESETS.at(0).camera.yaw);
  EXPECT_FLOAT_EQ(rs.physicsCore.kerrSpin, K_COMPARE_PRESETS.at(0).kerrSpin);
}

// The snapshot flag fires exactly at the settle boundary and the preset index
// advances only then.
TEST(CompareSweep, CapturesAtSettleBoundary) {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  InputManager &input = InputManager::instance();
  armSweep(rs, input);
  rs.compare.comparePresetSettleFrames = 3;

  advanceComparePresetSweep(rs, input, true);
  EXPECT_FALSE(rs.compare.captureCompareSnapshot);
  EXPECT_EQ(rs.compare.comparePresetIndex, 0);
  advanceComparePresetSweep(rs, input, true);
  EXPECT_FALSE(rs.compare.captureCompareSnapshot);
  EXPECT_EQ(rs.compare.comparePresetIndex, 0);
  advanceComparePresetSweep(rs, input, true);
  EXPECT_TRUE(rs.compare.captureCompareSnapshot);
  EXPECT_EQ(rs.compare.comparePresetIndex, 1);
  EXPECT_EQ(rs.compare.comparePresetFrameCounter, 0);
}

// Driving all presets (one settle frame each) ends the sweep and requests a
// restore; restoreCompareSweepState then returns the saved camera once the final
// snapshot has been consumed.
TEST(CompareSweep, CompletesAndRestores) {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  InputManager &input = InputManager::instance();
  int const presetCount = armSweep(rs, input);
  rs.compare.comparePresetSettleFrames = 1;

  for (int i = 0; i < presetCount; ++i) {
    advanceComparePresetSweep(rs, input, true);
  }
  EXPECT_FALSE(rs.compare.comparePresetSweep);
  EXPECT_TRUE(rs.compare.compareRestorePending);

  // Restore is a no-op while a capture is still pending.
  rs.compare.captureCompareSnapshot = true;
  restoreCompareSweepState(rs, input);
  EXPECT_TRUE(rs.compare.compareRestorePending);

  // Once the capture has been consumed, the saved camera comes back.
  rs.compare.captureCompareSnapshot = false;
  restoreCompareSweepState(rs, input);
  EXPECT_FALSE(rs.compare.compareRestorePending);
  EXPECT_FALSE(rs.compare.comparePresetSaved);
  EXPECT_FLOAT_EQ(input.camera().yaw, 12.0f);
  EXPECT_FLOAT_EQ(input.camera().distance, 42.0f);
  EXPECT_EQ(rs.camera.cameraModeIndex, 2);
  EXPECT_FLOAT_EQ(rs.physicsCore.kerrSpin, 0.44f);
}

// Leaving the black-hole scene mid-sweep, even on a settle boundary with a
// snapshot flagged, stops the sweep and puts the live camera and spin back at
// once; nothing stays armed for a later black-hole frame.
TEST(CompareSweep, SceneChangeCancelsAndRestores) {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  InputManager &input = InputManager::instance();
  armSweep(rs, input);
  rs.compare.comparePresetSettleFrames = 1;
  advanceComparePresetSweep(rs, input, true);
  ASSERT_TRUE(rs.compare.comparePresetSweep);
  ASSERT_TRUE(rs.compare.comparePresetSaved);
  ASSERT_TRUE(rs.compare.captureCompareSnapshot);
  // The preset camera is live while the sweep runs.
  EXPECT_FLOAT_EQ(input.camera().distance, K_COMPARE_PRESETS.front().camera.distance);

  rs.scene.mode = RenderState::SceneMode::Tesseract;
  updateComparePresetSweep(rs, input, true);
  EXPECT_FALSE(rs.compare.comparePresetSweep);
  EXPECT_FALSE(rs.compare.comparePresetSaved);
  EXPECT_FALSE(rs.compare.compareRestorePending);
  EXPECT_FALSE(rs.compare.captureCompareSnapshot);
  EXPECT_EQ(rs.compare.comparePresetIndex, 0);
  EXPECT_FLOAT_EQ(input.camera().yaw, 12.0f);
  EXPECT_FLOAT_EQ(input.camera().distance, 42.0f);
  EXPECT_EQ(rs.camera.cameraModeIndex, 2);
  EXPECT_FLOAT_EQ(rs.camera.orbitRadius, 9.0f);
  EXPECT_FLOAT_EQ(rs.physicsCore.kerrSpin, 0.44f);

  // Later tesseract frames leave the restored camera alone, and returning to
  // the black-hole scene does not resume the sweep.
  input.camera().distance = 17.0f;
  updateComparePresetSweep(rs, input, true);
  EXPECT_FLOAT_EQ(input.camera().distance, 17.0f);
  rs.scene.mode = RenderState::SceneMode::Blackhole;
  updateComparePresetSweep(rs, input, true);
  EXPECT_FLOAT_EQ(input.camera().distance, 17.0f);
  EXPECT_FALSE(rs.compare.comparePresetSaved);
}
