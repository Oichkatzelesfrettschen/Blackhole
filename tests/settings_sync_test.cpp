/**
 * @file settings_sync_test.cpp
 * @brief Load-once and write-back tests for the Settings <-> RenderState bridge.
 *
 * loadSettingsIntoRenderState and syncRenderStateToSettings were loop-inline
 * blocks in main.cpp. Extracting them into settings_sync.* makes the hydration
 * latches and the write-back pure functions of RenderState and Settings; these
 * GL-free tests assert first-frame hydration, the *SettingsLoaded latch guarding
 * against clobber of later user edits, the bloom-iteration clamp, and the
 * write-back of live display/post values. They link the test-only
 * blackhole_testcore library so RenderState can be constructed without the app
 * executables.
 */

#include <memory>

#include <gtest/gtest.h>

#include "input.h"
#include "render/render_state.h"
#include "render/settings_sync.h"
#include "settings.h"

using blackhole::K_DEFAULT_DEPTH_FAR;
using blackhole::K_MAX_BLOOM_ITERATIONS;
using blackhole::loadSettingsIntoRenderState;
using blackhole::RenderState;
using blackhole::syncRenderStateToSettings;

namespace {

// A Settings instance with every synced field set away from the RenderState
// defaults so a hydration can be observed field by field.
Settings distinctSettings() {
  Settings settings;
  settings.cameraMode = 3;
  settings.orbitRadius = 22.0f;
  settings.orbitSpeed = 11.0f;
  settings.renderScale = 0.5f;
  settings.swapInterval = 2;
  settings.bloomStrength = 0.7f;
  settings.tonemappingEnabled = false;
  settings.gamma = 1.8f;
  settings.bloomIterations = 4;
  return settings;
}

// depthFar normalizes depth cues and bounds the gizmo frustum: the default
// camera distance plus the disk's 200-unit outer radius fits inside it.
TEST(SettingsSync, DefaultDepthFarHoldsTheDefaultCameraAndTheDisk) {
  const auto rsStorage = std::make_unique<RenderState>();
  EXPECT_FLOAT_EQ(rsStorage->display.depthFar, K_DEFAULT_DEPTH_FAR);
  EXPECT_GT(K_DEFAULT_DEPTH_FAR, K_DEFAULT_CAMERA_DISTANCE + 200.0f);
}

} // namespace

// First frame with clear latches copies every synced group from Settings and
// latches so a subsequent load with different Settings is ignored.
TEST(SettingsSync, HydratesOnceThenLatches) {
  const auto rsStorage = std::make_unique<RenderState>();
  RenderState &rs = *rsStorage;
  const Settings settings = distinctSettings();

  loadSettingsIntoRenderState(rs, settings);

  EXPECT_EQ(rs.camera.cameraModeIndex, 3);
  EXPECT_FLOAT_EQ(rs.camera.orbitRadius, 22.0f);
  EXPECT_FLOAT_EQ(rs.camera.orbitSpeed, 11.0f);
  EXPECT_FLOAT_EQ(rs.display.renderScale, 0.5f);
  EXPECT_EQ(rs.display.swapInterval, 2);
  EXPECT_FLOAT_EQ(rs.post.bloomStrength, 0.7f);
  EXPECT_FALSE(rs.post.tonemappingEnabled);
  EXPECT_FLOAT_EQ(rs.post.toneExposure, 1.0f);
  EXPECT_FLOAT_EQ(rs.post.gamma, 1.8f);
  EXPECT_EQ(rs.post.bloomIterations, 4);
  EXPECT_TRUE(rs.camera.cameraSettingsLoaded);
  EXPECT_TRUE(rs.display.displaySettingsLoaded);
  EXPECT_TRUE(rs.post.postProcessingSettingsLoaded);
  EXPECT_TRUE(rs.post.bloomSettingsLoaded);

  // A live edit followed by a second load with new persisted values keeps the
  // edit -- the latch blocks the clobber.
  rs.camera.orbitRadius = 99.0f;
  Settings other = distinctSettings();
  other.orbitRadius = 5.0f;
  loadSettingsIntoRenderState(rs, other);
  EXPECT_FLOAT_EQ(rs.camera.orbitRadius, 99.0f);
}

// bloomIterations is clamped into [1, K_MAX_BLOOM_ITERATIONS] on hydration.
TEST(SettingsSync, ClampsBloomIterations) {
  const auto highStorage = std::make_unique<RenderState>();
  RenderState &high = *highStorage;
  Settings tooMany = distinctSettings();
  tooMany.bloomIterations = 999;
  loadSettingsIntoRenderState(high, tooMany);
  EXPECT_EQ(high.post.bloomIterations, K_MAX_BLOOM_ITERATIONS);

  const auto lowStorage = std::make_unique<RenderState>();
  RenderState &low = *lowStorage;
  Settings tooFew = distinctSettings();
  tooFew.bloomIterations = -3;
  loadSettingsIntoRenderState(low, tooFew);
  EXPECT_EQ(low.post.bloomIterations, 1);
}

// The write-back copies live display/post values and the window fullscreen
// state into Settings.
TEST(SettingsSync, WritesBackLiveState) {
  const auto rsStorage = std::make_unique<RenderState>();
  RenderState &rs = *rsStorage;
  rs.display.swapInterval = 0;
  rs.display.renderScale = 0.75f;
  rs.post.bloomStrength = 0.42f;
  rs.post.tonemappingEnabled = false;
  rs.post.gamma = 2.1f;
  rs.post.bloomIterations = 6;

  Settings settings; // defaults, overwritten by the sync
  settings.fullscreen = true;
  syncRenderStateToSettings(rs, settings, InputManager::instance());

  EXPECT_EQ(settings.fullscreen, InputManager::instance().isFullscreen());
  EXPECT_EQ(settings.swapInterval, 0);
  EXPECT_FLOAT_EQ(settings.renderScale, 0.75f);
  EXPECT_FLOAT_EQ(settings.bloomStrength, 0.42f);
  EXPECT_FALSE(settings.tonemappingEnabled);
  EXPECT_FLOAT_EQ(settings.gamma, 2.1f);
  EXPECT_EQ(settings.bloomIterations, 6);
}
