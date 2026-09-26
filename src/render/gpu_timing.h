/**
 * @file gpu_timing.h
 * @brief Double-buffered GL_TIME_ELAPSED query timers, the per-stage
 *        timer set, a rolling frame-time history, and their CSV writers.
 *
 * GpuTimer alternates two query objects so resolve() reads the previous
 * frame's result while the current frame records -- the GPU never stalls
 * on QueryObject readback. GpuTimerSet groups one timer per render stage;
 * TimingHistory keeps the last K_CAPACITY frames for the performance
 * panel plot and CSV export.
 *
 * A stage that the frame resolve() reads did not run carries no sample:
 * hasSample is false, the history stores NaN, the CSV writers leave the
 * field empty, and the panel shows "not run", so a scene that skips a
 * stage never republishes that stage's last measurement.
 */

#ifndef BLACKHOLE_RENDER_GPU_TIMING_H
#define BLACKHOLE_RENDER_GPU_TIMING_H

#include <array>
#include <filesystem>
#include <string>
#include <string_view>

#include <glbinding/gl/types.h>

namespace blackhole {

struct GpuTimer {
  gl::GLuint queries[2] = {0, 0};
  bool issued[2] = {false, false};
  int index = 0;
  double lastMs = 0.0; ///< Last resolved duration; meaningful only while hasSample.
  bool hasSample = false; ///< lastMs measures a frame that ran this stage.
  bool active = false;
  bool beganThisFrame = false; ///< begin() opened a query since the last swap().
  bool ranLastFrame = false;   ///< The frame the last swap() closed ran this stage.

  bool ensureQueries();
  bool init();
  void shutdown();
  void begin();
  void end();
  /**
   * @brief Read the previous frame's query into lastMs.
   *
   * When that frame did not run the stage (ranLastFrame false) the timer
   * drops its sample and touches no GL state. A pending result keeps the
   * sample of an earlier frame that ran the stage.
   */
  void resolve();
  /** @brief Close the frame: flip the query slot and record whether it ran. */
  void swap();
};

struct GpuTimerSet {
  bool initialized = false;
  GpuTimer blackholeFragment;
  GpuTimer blackholeCompute;
  GpuTimer bloom;
  GpuTimer tonemap;
  GpuTimer depth;
  GpuTimer grmhdSlice;
  GpuTimer tesseract; ///< Tesseract scene pass, the black-hole passes' replacement.

  void init();
  void shutdown();
  void resolve();
  void swap();
};

struct TimingHistory {
  static constexpr int K_CAPACITY = 240;
  std::array<float, K_CAPACITY> cpuMs{};
  std::array<float, K_CAPACITY> gpuFragmentMs{};
  std::array<float, K_CAPACITY> gpuComputeMs{};
  std::array<float, K_CAPACITY> gpuBloomMs{};
  std::array<float, K_CAPACITY> gpuTonemapMs{};
  std::array<float, K_CAPACITY> gpuDepthMs{};
  std::array<float, K_CAPACITY> gpuGrmhdSliceMs{};
  std::array<float, K_CAPACITY> gpuTesseractMs{};
  int offset = 0;
  int count = 0;

  /** @brief Record one frame; a GPU stage without a sample stores NaN. */
  void push(float cpuMsSample, const GpuTimerSet &timers);
};

/** @brief @p timer's duration in ms, or NaN when it holds no sample. */
float timerSampleMs(const GpuTimer &timer);

/// Header of gpu_timing.csv; gpu_tesseract_ms trails the columns that
/// predate it.
inline constexpr std::string_view GPU_TIMING_CSV_HEADER =
    "index,time_sec,width,height,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,"
    "gpu_tonemap_ms,gpu_depth_ms,gpu_grmhd_slice_ms,compute_active,kerr_spin,gpu_tesseract_ms";

/**
 * @brief First free "<stem>.stale-<n><ext>" beside @p path, n from 1.
 *
 * appendGpuTimingSample renames a log whose header differs from
 * GPU_TIMING_CSV_HEADER to this path before it appends, so an older build's
 * log keeps its own schema and the new file starts with the current header.
 */
std::filesystem::path staleTimingLogPath(const std::string &path);

std::string gpuTimingPath();
void appendGpuTimingSample(const std::string &path, int index, int width, int height,
                           float cpuFrameMs, const GpuTimerSet &timers, bool computeActive,
                           float kerrSpin, double timeSec);
void writeTimingHistoryCsv(const TimingHistory &history, const std::string &path);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_GPU_TIMING_H
