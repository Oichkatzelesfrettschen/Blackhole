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
 * paths by the same absolute index.
 */

#include <memory>
#include <optional>

#include <gtest/gtest.h>

#include "cinematic.h"
#include "platform/cli_options.h"
#include "render.h"
#include "render/post_pipeline.h"
#include "render/record_mode.h"
#include "render/render_state.h"

namespace {

using blackhole::frameContentSeconds;
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

} // namespace
