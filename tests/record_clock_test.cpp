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
 * paths by the same absolute index, and recordCameraConflict refuses record
 * camera overrides that describe no camera.
 */

#include <limits>
#include <memory>
#include <optional>
#include <string>

#include <gtest/gtest.h>

#include "cinematic.h"
#include "platform/cli_options.h"
#include "render.h"
#include "render/post_pipeline.h"
#include "render/record_mode.h"
#include "render/render_state.h"

namespace {

using blackhole::frameContentSeconds;
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
    ASSERT_TRUE(conflict.has_value()) << distance;
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
    ASSERT_TRUE(conflict.has_value()) << fov;
    EXPECT_NE(conflict.value_or("").find("--record-fov"), std::string::npos);
  }
  cli.recordFovDeg = 120.0f;
  EXPECT_FALSE(recordCameraConflict(cli).has_value());
}

} // namespace
