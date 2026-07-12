/**
 * @file gpu_timing.cpp
 * @brief GPU stage timing implementation and CSV export.
 */

#include "gpu_timing.h"

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <limits>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>

using namespace gl;

namespace blackhole {

bool GpuTimer::ensureQueries() {
  if (queries[0] != 0 && queries[1] != 0) {
    return true;
  }
  if (queries[0] != 0 || queries[1] != 0) {
    glDeleteQueries(2, queries);
  }
  glGenQueries(2, queries);
  issued[0] = false;
  issued[1] = false;
  active = false;
  return (queries[0] != 0 && queries[1] != 0);
}

bool GpuTimer::init() {
  glGenQueries(2, queries);
  if (queries[0] == 0 || queries[1] == 0) {
    queries[0] = 0;
    queries[1] = 0;
    issued[0] = false;
    issued[1] = false;
    active = false;
    return false;
  }
  issued[0] = false;
  issued[1] = false;
  return true;
}

void GpuTimer::shutdown() {
  if (queries[0] != 0 || queries[1] != 0) {
    glDeleteQueries(2, queries);
  }
  queries[0] = 0;
  queries[1] = 0;
  issued[0] = false;
  issued[1] = false;
  active = false;
}

void GpuTimer::begin() {
  if (active) {
    return;
  }
  if (!ensureQueries()) {
    return;
  }
  glBeginQuery(GL_TIME_ELAPSED, queries[index]);
  issued[index] = true;
  active = true;
}

void GpuTimer::end() {
  if (!active) {
    return;
  }
  glEndQuery(GL_TIME_ELAPSED);
  active = false;
}

void GpuTimer::resolve() {
  if (!ensureQueries()) {
    return;
  }
  int const prev = 1 - index;
  if (queries[prev] == 0 || !issued[prev]) {
    return;
  }
  GLuint available = 0;
  glGetQueryObjectuiv(queries[prev], GL_QUERY_RESULT_AVAILABLE, &available);
  if (available != 0u) {
    GLuint64 timeNs = 0;
    glGetQueryObjectui64v(queries[prev], GL_QUERY_RESULT, &timeNs);
    lastMs = static_cast<double>(timeNs) / 1.0e6;
    issued[prev] = false;
  }
}

void GpuTimer::swap() {
  index = 1 - index;
  active = false;
}

void GpuTimerSet::init() {
  bool ok = true;
  ok &= blackholeFragment.init();
  ok &= blackholeCompute.init();
  ok &= bloom.init();
  ok &= tonemap.init();
  ok &= depth.init();
  ok &= grmhdSlice.init();
  initialized = ok;
  if (!ok) {
    shutdown();
  }
}

void GpuTimerSet::shutdown() {
  blackholeFragment.shutdown();
  blackholeCompute.shutdown();
  bloom.shutdown();
  tonemap.shutdown();
  depth.shutdown();
  grmhdSlice.shutdown();
  initialized = false;
}

void GpuTimerSet::resolve() {
  blackholeFragment.resolve();
  blackholeCompute.resolve();
  bloom.resolve();
  tonemap.resolve();
  depth.resolve();
  grmhdSlice.resolve();
}

void GpuTimerSet::swap() {
  blackholeFragment.swap();
  blackholeCompute.swap();
  bloom.swap();
  tonemap.swap();
  depth.swap();
  grmhdSlice.swap();
}

void TimingHistory::push(float cpuMsSample, const GpuTimerSet &timers) {
  const auto index = static_cast<std::size_t>(offset);
  cpuMs.at(index) = cpuMsSample;
  if (timers.initialized) {
    gpuFragmentMs.at(index) = static_cast<float>(timers.blackholeFragment.lastMs);
    gpuComputeMs.at(index) = static_cast<float>(timers.blackholeCompute.lastMs);
    gpuBloomMs.at(index) = static_cast<float>(timers.bloom.lastMs);
    gpuTonemapMs.at(index) = static_cast<float>(timers.tonemap.lastMs);
    gpuDepthMs.at(index) = static_cast<float>(timers.depth.lastMs);
    gpuGrmhdSliceMs.at(index) = static_cast<float>(timers.grmhdSlice.lastMs);
  } else {
    const float nan = std::numeric_limits<float>::quiet_NaN();
    gpuFragmentMs.at(index) = nan;
    gpuComputeMs.at(index) = nan;
    gpuBloomMs.at(index) = nan;
    gpuTonemapMs.at(index) = nan;
    gpuDepthMs.at(index) = nan;
    gpuGrmhdSliceMs.at(index) = nan;
  }
  offset = (offset + 1) % K_CAPACITY;
  if (count < K_CAPACITY) {
    ++count;
  }
}

std::string gpuTimingPath() {
  std::filesystem::create_directories("logs/perf");
  return "logs/perf/gpu_timing.csv";
}

void appendGpuTimingSample(const std::string &path, int index, int width, int height,
                           float cpuFrameMs, const GpuTimerSet &timers, bool computeActive,
                           float kerrSpin, double timeSec) {
  const bool exists = std::filesystem::exists(path);
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << "index,time_sec,width,height,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,"
           "gpu_tonemap_ms,gpu_depth_ms,gpu_grmhd_slice_ms,compute_active,kerr_spin\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << timeSec << "," << width << "," << height << "," << cpuFrameMs << ","
      << timers.blackholeFragment.lastMs << "," << timers.blackholeCompute.lastMs << ","
      << timers.bloom.lastMs << "," << timers.tonemap.lastMs << "," << timers.depth.lastMs << ","
      << timers.grmhdSlice.lastMs << "," << (computeActive ? 1 : 0) << "," << kerrSpin << "\n";
}

void writeTimingHistoryCsv(const TimingHistory &history, const std::string &path) {
  std::filesystem::create_directories("logs/perf");
  std::ofstream out(path);
  if (!out) {
    return;
  }
  out << "index,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,gpu_tonemap_ms,gpu_depth_ms,"
         "gpu_grmhd_slice_ms\n";
  out << std::fixed << std::setprecision(6);

  int const count = history.count;
  int start = history.offset - count;
  if (start < 0) {
    start += TimingHistory::K_CAPACITY;
  }
  for (int i = 0; i < count; ++i) {
    int const rawIndex = (start + i) % TimingHistory::K_CAPACITY;
    auto const idx = static_cast<std::size_t>(rawIndex);
    out << i << "," << history.cpuMs.at(idx) << "," << history.gpuFragmentMs.at(idx) << ","
        << history.gpuComputeMs.at(idx) << "," << history.gpuBloomMs.at(idx) << ","
        << history.gpuTonemapMs.at(idx) << "," << history.gpuDepthMs.at(idx) << ","
        << history.gpuGrmhdSliceMs.at(idx) << "\n";
  }
}

} // namespace blackhole
