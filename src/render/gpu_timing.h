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
 */

#ifndef BLACKHOLE_RENDER_GPU_TIMING_H
#define BLACKHOLE_RENDER_GPU_TIMING_H

#include <array>
#include <string>

#include <glbinding/gl/types.h>

namespace blackhole {

struct GpuTimer {
  gl::GLuint queries[2] = {0, 0};
  bool issued[2] = {false, false};
  int index = 0;
  double lastMs = 0.0;
  bool active = false;

  bool ensureQueries();
  bool init();
  void shutdown();
  void begin();
  void end();
  void resolve();
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
  int offset = 0;
  int count = 0;

  void push(float cpuMsSample, const GpuTimerSet &timers);
};

std::string gpuTimingPath();
void appendGpuTimingSample(const std::string &path, int index, int width, int height,
                           float cpuFrameMs, const GpuTimerSet &timers, bool computeActive,
                           float kerrSpin, double timeSec);
void writeTimingHistoryCsv(const TimingHistory &history, const std::string &path);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_GPU_TIMING_H
