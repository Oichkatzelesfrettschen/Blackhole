/**
 * @file gpu_timing_test.cpp
 * @brief Per-frame sample bookkeeping of the GPU stage timers, without GL.
 *
 * A stage that the frame resolve() reads did not run must publish no value:
 * GpuTimer::resolve drops the sample before it touches a query, the history
 * stores NaN, and the CSV row leaves the field empty. A log started by a build
 * with another column set moves aside before the first new row. Every case
 * here stays on the branches that issue no GL call.
 */

#include <filesystem>
#include <fstream>
#include <string>
#include <system_error>
#include <vector>

#include <gtest/gtest.h>

#include "physics/safe_limits.h"
#include "render/gpu_timing.h"

namespace {

using blackhole::appendGpuTimingSample;
using blackhole::GPU_TIMING_CSV_HEADER;
using blackhole::GpuTimer;
using blackhole::GpuTimerSet;
using blackhole::timerSampleMs;
using blackhole::TimingHistory;

// A timer that resolved lastMs in a frame that ran the stage.
GpuTimer sampledTimer(double ms) {
  GpuTimer timer;
  timer.lastMs = ms;
  timer.hasSample = true;
  return timer;
}

TEST(GpuTiming, SwapRecordsWhetherTheClosedFrameRanTheStage) {
  GpuTimer timer;
  timer.beganThisFrame = true;
  timer.swap();
  EXPECT_TRUE(timer.ranLastFrame);
  EXPECT_FALSE(timer.beganThisFrame);
  timer.swap();
  EXPECT_FALSE(timer.ranLastFrame);
}

TEST(GpuTiming, SkippedStageDropsItsLastSample) {
  GpuTimer timer = sampledTimer(4.25);
  EXPECT_FLOAT_EQ(timerSampleMs(timer), 4.25f);
  // The frame closes without begin(): the next resolve reads nothing.
  timer.swap();
  timer.resolve();
  EXPECT_FALSE(timer.hasSample);
  EXPECT_TRUE(physics::safeIsnan(timerSampleMs(timer)));
}

TEST(GpuTiming, HistoryStoresNanForStagesWithoutSamples) {
  GpuTimerSet timers;
  timers.initialized = true;
  timers.tesseract = sampledTimer(1.5);
  TimingHistory history;
  history.push(16.0f, timers);
  ASSERT_EQ(history.count, 1);
  EXPECT_FLOAT_EQ(history.cpuMs.at(0), 16.0f);
  EXPECT_FLOAT_EQ(history.gpuTesseractMs.at(0), 1.5f);
  EXPECT_TRUE(physics::safeIsnan(history.gpuFragmentMs.at(0)));
  EXPECT_TRUE(physics::safeIsnan(history.gpuComputeMs.at(0)));
  EXPECT_TRUE(physics::safeIsnan(history.gpuDepthMs.at(0)));
  EXPECT_TRUE(physics::safeIsnan(history.gpuGrmhdSliceMs.at(0)));
}

TEST(GpuTiming, UninitializedTimersPublishNothing) {
  GpuTimerSet timers;
  timers.blackholeFragment = sampledTimer(2.0);
  TimingHistory history;
  history.push(16.0f, timers);
  EXPECT_TRUE(physics::safeIsnan(history.gpuFragmentMs.at(0)));
}

TEST(GpuTiming, CsvRowLeavesSkippedStagesEmpty) {
  const std::filesystem::path path =
      std::filesystem::temp_directory_path() / "blackhole_gpu_timing_test.csv";
  std::error_code ignored;
  std::filesystem::remove(path, ignored);

  GpuTimerSet timers;
  timers.initialized = true;
  timers.bloom = sampledTimer(0.5);
  timers.tonemap = sampledTimer(0.25);
  timers.tesseract = sampledTimer(1.5);
  appendGpuTimingSample(path.string(), 7, 640, 360, 16.0f, timers, false, 0.0f, 2.0);

  std::ifstream in(path);
  std::string header;
  std::string row;
  ASSERT_TRUE(std::getline(in, header));
  ASSERT_TRUE(std::getline(in, row));
  in.close();
  std::filesystem::remove(path, ignored);

  EXPECT_EQ(header, "index,time_sec,width,height,cpu_ms,gpu_fragment_ms,gpu_compute_ms,"
                    "gpu_bloom_ms,gpu_tonemap_ms,gpu_depth_ms,gpu_grmhd_slice_ms,"
                    "compute_active,kerr_spin,gpu_tesseract_ms");
  // Fragment, compute, depth, and GRMHD did not run; bloom, tonemap, and the
  // tesseract pass did.
  EXPECT_EQ(row, "7,2.000000,640,360,16.000000,,,0.500000,0.250000,,,0,0.000000,1.500000");
}

std::vector<std::string> readLines(const std::filesystem::path &path) {
  std::ifstream in(path);
  std::vector<std::string> lines;
  for (std::string line; std::getline(in, line);) {
    lines.push_back(line);
  }
  return lines;
}

TEST(GpuTiming, OlderSchemaLogsMoveAsideBeforeAppending) {
  const std::filesystem::path dir =
      std::filesystem::temp_directory_path() / "blackhole_gpu_timing_rotation_test";
  std::error_code ignored;
  std::filesystem::remove_all(dir, ignored);
  std::filesystem::create_directories(dir);
  const std::filesystem::path path = dir / "gpu_timing.csv";
  const std::string legacyHeader =
      "index,time_sec,width,height,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,"
      "gpu_tonemap_ms,gpu_depth_ms,gpu_grmhd_slice_ms,compute_active,kerr_spin";
  const std::string legacyRow = "0,1.0,640,360,16.0,2.0,0.0,0.5,0.25,0.1,0.0,0,0.0";
  {
    std::ofstream legacy(path);
    legacy << legacyHeader << '\n' << legacyRow << '\n';
  }

  GpuTimerSet timers;
  timers.initialized = true;
  timers.tesseract = sampledTimer(1.5);
  appendGpuTimingSample(path.string(), 1, 640, 360, 16.0f, timers, false, 0.0f, 2.0);
  appendGpuTimingSample(path.string(), 2, 640, 360, 16.0f, timers, false, 0.0f, 2.1);

  const std::vector<std::string> current = readLines(path);
  ASSERT_EQ(current.size(), 3U);
  EXPECT_EQ(current.at(0), std::string(GPU_TIMING_CSV_HEADER));
  const std::vector<std::string> stale = readLines(dir / "gpu_timing.stale-1.csv");
  ASSERT_EQ(stale.size(), 2U);
  EXPECT_EQ(stale.at(0), legacyHeader);
  EXPECT_EQ(stale.at(1), legacyRow);
  EXPECT_EQ(blackhole::staleTimingLogPath(path.string()), dir / "gpu_timing.stale-2.csv");
  std::filesystem::remove_all(dir, ignored);
}

} // namespace
