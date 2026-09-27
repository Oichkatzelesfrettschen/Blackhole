/**
 * @file record_clock_test.cpp
 * @brief Recorded frames read content time from their index, not the wall.
 *
 * frameContentSeconds feeds every time-driven shading input: the tonemap film
 * grain, depth-cue motion, disk and sky rotation, and background drift. Under
 * --record-frames it must return recordFrameIndex / K_CINEMATIC_FPS whatever
 * the wall clock reads, so two renders of one frame index, in one run, two
 * runs, or a --start-frame resume, feed the post chain identical inputs.
 * recordPathProgress places the showcase-orbit and compare-orbit-near camera
 * paths by the same absolute index, recordCameraConflict refuses record
 * camera overrides that describe no camera, and applyRecordCameraPath applies
 * --record-distance and --record-fov after every profile's path.
 */

#include <limits>
#include <memory>
#include <optional>
#include <string>

#include <gtest/gtest.h>

#include "cinematic.h"
#include "input.h"
#include "platform/cli_options.h"
#include "render.h"
#include "render/post_pipeline.h"
#include "render/record_mode.h"
#include "render/render_state.h"

namespace {

using blackhole::applyRecordCameraPath;
using blackhole::frameContentSeconds;
using blackhole::observerCaptureClock;
using blackhole::recordCameraConflict;
using blackhole::recordOutputSeconds;
using blackhole::recordPathProgress;
using blackhole::RenderState;
using blackhole::tonemapPass;

platform::CliOptions recordingCli() {
  platform::CliOptions cli;
  cli.recordFramesDir = "frames";
  cli.recordProfile = "cinematic";
  return cli;
}

TEST(RecordClock, RecordedFramesReadTheOutputClock) {
  const platform::CliOptions cli = recordingCli();
  const std::optional<double> recorded = recordOutputSeconds(cli, 150);
  EXPECT_TRUE(recorded.has_value());
  const double seconds = recorded.value_or(-1.0);
  EXPECT_DOUBLE_EQ(seconds, 150.0 / static_cast<double>(K_CINEMATIC_FPS));
  EXPECT_DOUBLE_EQ(frameContentSeconds(cli, 150, 3.7), seconds);
  EXPECT_DOUBLE_EQ(frameContentSeconds(cli, 150, 912.25), seconds);
}

TEST(RecordClock, InteractiveFramesReadTheWallClock) {
  const platform::CliOptions cli;
  EXPECT_FALSE(recordOutputSeconds(cli, 150).has_value());
  EXPECT_DOUBLE_EQ(frameContentSeconds(cli, 150, 3.7), 3.7);
}

TEST(RecordClock, ObserverCaptureClockFollowsTheOutputClockWhileRecording) {
  const platform::CliOptions cli = recordingCli();
  const auto clock = observerCaptureClock(cli, 150);
  if (!clock.has_value()) {
    GTEST_FAIL() << "clock is empty";
  }
  EXPECT_DOUBLE_EQ(clock->first, 150.0 / static_cast<double>(K_CINEMATIC_FPS));
  // frameSeconds is a difference of two divisions (frame 151's output second
  // minus frame 150's), so it is within a rounding ulp of 1 / fps rather than
  // bit-identical to it.
  EXPECT_NEAR(clock->second, 1.0 / static_cast<double>(K_CINEMATIC_FPS), 1.0e-12);
}

TEST(RecordClock, ObserverCaptureClockIsNulloptOffAnyCaptureCli) {
  const platform::CliOptions cli;
  EXPECT_FALSE(observerCaptureClock(cli, 3).has_value());
}

/**
 * Falsifier: before the fix, an --export-frame run with no --record-frames
 * had renderSceneFrame pass std::nullopt to renderObserverSkyScene, so
 * advanceObserverClock stepped the observer's proper time by wall-clock
 * deltaSeconds * skyTimeScale across the five warmup frames. At
 * BLACKHOLE_OBSERVER_TIME_SCALE >= 1 that phase drift makes two exports of
 * the same BLACKHOLE_OBSERVER_PROPER_SECONDS render different frames.
 * observerCaptureClock must instead return a frozen (0, 0) clock so every
 * warmup and export frame advances the clock by zero.
 */
TEST(RecordClock, ObserverCaptureClockFreezesForOneShotExport) {
  platform::CliOptions cli;
  cli.exportFramePath = "frame.png";
  const auto clock = observerCaptureClock(cli, 4);
  if (!clock.has_value()) {
    GTEST_FAIL() << "clock is empty";
  }
  EXPECT_DOUBLE_EQ(clock->first, 0.0);
  EXPECT_DOUBLE_EQ(clock->second, 0.0);
  // Every warmup frame index gives the same frozen clock.
  EXPECT_EQ(observerCaptureClock(cli, 0), clock);

  platform::CliOptions rawCli;
  rawCli.exportRawFramePath = "frame.pfm";
  EXPECT_EQ(observerCaptureClock(rawCli, 2), clock);
}

TEST(RecordClock, SameRecordFrameGivesIdenticalTonemapInputs) {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  // The cinematic, compare, and tesseract record lanes keep film grain on.
  rs.post.tonemapFilmGrainStrength = 0.005f;
  const platform::CliOptions cli = recordingCli();
  const RenderToTextureInfo first = tonemapPass(rs, frameContentSeconds(cli, 150, 3.7));
  const RenderToTextureInfo resumed =
      tonemapPass(rs, frameContentSeconds(cli, 150, 912.25));
  EXPECT_EQ(first.floatUniforms, resumed.floatUniforms);
  EXPECT_FLOAT_EQ(first.floatUniforms.at("time"), 2.5f);
  EXPECT_FLOAT_EQ(first.floatUniforms.at("filmGrainStrength"), 0.005f);
  // A different frame index moves the grain.
  const RenderToTextureInfo next = tonemapPass(rs, frameContentSeconds(cli, 151, 3.7));
  EXPECT_NE(first.floatUniforms.at("time"), next.floatUniforms.at("time"));
}

// A full run of 240 frames and a run resumed at frame 100 with the remaining
// 140 frames give every shared frame the same camera path progress.
TEST(RecordClock, ResumedRunsKeepTheCameraPathProgress) {
  platform::CliOptions full = recordingCli();
  full.recordProfile = "showcase-orbit";
  full.recordFramesTotal = 240;
  platform::CliOptions resumed = full;
  resumed.recordStartFrame = 100;
  resumed.recordFramesTotal = 140;
  for (const int frame : {100, 101, 170, 239}) {
    EXPECT_FLOAT_EQ(recordPathProgress(resumed, frame), recordPathProgress(full, frame)) << frame;
  }
  EXPECT_FLOAT_EQ(recordPathProgress(full, 0), 0.0f);
  EXPECT_FLOAT_EQ(recordPathProgress(full, 239), 1.0f);
  EXPECT_FLOAT_EQ(recordPathProgress(resumed, 100), 100.0f / 239.0f);
}

// A zero distance puts the camera on its focus, where buildCameraBasis
// normalizes a zero vector; a field of view outside (0, 180) degrees has no
// perspective. Both are refused before a window opens.
TEST(RecordClock, RecordCameraOverridesMustDescribeACamera) {
  platform::CliOptions cli = recordingCli();
  cli.recordProfile = "showcase-orbit";
  EXPECT_FALSE(recordCameraConflict(cli).has_value());

  cli.hasRecordDistance = true;
  for (const float distance : {0.0f, -3.0f, std::numeric_limits<float>::infinity(),
                               std::numeric_limits<float>::quiet_NaN()}) {
    cli.recordDistance = distance;
    const std::optional<std::string> conflict = recordCameraConflict(cli);
    if (!conflict.has_value()) {
      GTEST_FAIL() << distance;
    }
    EXPECT_NE(conflict.value_or("").find("--record-distance"), std::string::npos);
  }
  // The cinematic path's 120 lies past the interactive 50 clamp and stays legal.
  for (const float distance : {0.01f, 14.0f, 120.0f}) {
    cli.recordDistance = distance;
    EXPECT_FALSE(recordCameraConflict(cli).has_value()) << distance;
  }

  cli.hasRecordFov = true;
  for (const float fov : {0.0f, -10.0f, 180.0f, 250.0f, std::numeric_limits<float>::quiet_NaN()}) {
    cli.recordFovDeg = fov;
    const std::optional<std::string> conflict = recordCameraConflict(cli);
    if (!conflict.has_value()) {
      GTEST_FAIL() << fov;
    }
    EXPECT_NE(conflict.value_or("").find("--record-fov"), std::string::npos);
  }
  cli.recordFovDeg = 120.0f;
  EXPECT_FALSE(recordCameraConflict(cli).has_value());
}

// Every record profile ends with the distance and field-of-view overrides,
// so they frame both scenes whichever path drives the camera; without them
// each path keeps its own values.
TEST(RecordClock, CameraOverridesApplyToEveryProfile) {
  InputManager &input = InputManager::instance();
  const CameraState saved = input.camera();
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  for (const char *profile : {"cinematic", "compare-orbit-near", "showcase-orbit"}) {
    platform::CliOptions cli = recordingCli();
    cli.recordProfile = profile;
    cli.recordFramesTotal = 240;
    rs.recording.recordFrameIndex = 60;
    rs.recording.recordCinematic = 1.0f;
    applyRecordCameraPath(rs, cli, input);
    const CameraState pathCamera = input.camera();
    EXPECT_NE(pathCamera.distance, 33.0f) << profile;

    cli.hasRecordDistance = true;
    cli.recordDistance = 33.0f;
    cli.hasRecordFov = true;
    cli.recordFovDeg = 55.0f;
    applyRecordCameraPath(rs, cli, input);
    EXPECT_FLOAT_EQ(input.camera().distance, 33.0f) << profile;
    EXPECT_FLOAT_EQ(input.camera().fov, 55.0f) << profile;
    // The path still sets the orientation.
    EXPECT_FLOAT_EQ(input.camera().yaw, pathCamera.yaw) << profile;
    EXPECT_FLOAT_EQ(input.camera().pitch, pathCamera.pitch) << profile;
  }
  // The cinematic HUD keyframe reports the camera the frame renders with.
  EXPECT_FLOAT_EQ(rs.recording.recordCurrentKf.cam.distance, 33.0f);
  input.camera() = saved;
}

} // namespace
