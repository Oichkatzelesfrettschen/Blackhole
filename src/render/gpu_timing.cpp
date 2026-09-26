/**
 * @file gpu_timing.cpp
 * @brief GPU stage timing implementation and CSV export.
 */

#include "gpu_timing.h"

#include <cstddef>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <ios>
#include <limits>
#include <ostream>
#include <string>
#include <system_error>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include "physics/safe_limits.h"

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
  hasSample = false;
  beganThisFrame = false;
  ranLastFrame = false;
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
  hasSample = false;
  beganThisFrame = false;
  ranLastFrame = false;
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
  beganThisFrame = true;
}

void GpuTimer::end() {
  if (!active) {
    return;
  }
  glEndQuery(GL_TIME_ELAPSED);
  active = false;
}

void GpuTimer::resolve() {
  if (!ranLastFrame) {
    hasSample = false;
    return;
  }
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
    hasSample = true;
    issued[prev] = false;
  }
}

void GpuTimer::swap() {
  index = 1 - index;
  active = false;
  ranLastFrame = beganThisFrame;
  beganThisFrame = false;
}

void GpuTimerSet::init() {
  bool ok = true;
  ok &= blackholeFragment.init();
  ok &= blackholeCompute.init();
  ok &= bloom.init();
  ok &= tonemap.init();
  ok &= depth.init();
  ok &= grmhdSlice.init();
  ok &= tesseract.init();
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
  tesseract.shutdown();
  initialized = false;
}

void GpuTimerSet::resolve() {
  blackholeFragment.resolve();
  blackholeCompute.resolve();
  bloom.resolve();
  tonemap.resolve();
  depth.resolve();
  grmhdSlice.resolve();
  tesseract.resolve();
}

void GpuTimerSet::swap() {
  blackholeFragment.swap();
  blackholeCompute.swap();
  bloom.swap();
  tonemap.swap();
  depth.swap();
  grmhdSlice.swap();
  tesseract.swap();
}

float timerSampleMs(const GpuTimer &timer) {
  return timer.hasSample ? static_cast<float>(timer.lastMs)
                         : std::numeric_limits<float>::quiet_NaN();
}

void TimingHistory::push(float cpuMsSample, const GpuTimerSet &timers) {
  const auto index = static_cast<std::size_t>(offset);
  cpuMs.at(index) = cpuMsSample;
  const auto sample = [&timers](const GpuTimer &timer) {
    return timers.initialized ? timerSampleMs(timer) : std::numeric_limits<float>::quiet_NaN();
  };
  gpuFragmentMs.at(index) = sample(timers.blackholeFragment);
  gpuComputeMs.at(index) = sample(timers.blackholeCompute);
  gpuBloomMs.at(index) = sample(timers.bloom);
  gpuTonemapMs.at(index) = sample(timers.tonemap);
  gpuDepthMs.at(index) = sample(timers.depth);
  gpuGrmhdSliceMs.at(index) = sample(timers.grmhdSlice);
  gpuTesseractMs.at(index) = sample(timers.tesseract);
  offset = (offset + 1) % K_CAPACITY;
  if (count < K_CAPACITY) {
    ++count;
  }
}

std::string gpuTimingPath() {
  std::filesystem::create_directories("logs/perf");
  return "logs/perf/gpu_timing.csv";
}

namespace {

/// Streams a millisecond field, or nothing for a stage without a sample.
struct MsField {
  float ms = 0.0f;
};

std::ostream &operator<<(std::ostream &out, MsField field) {
  if (!physics::safeIsnan(field.ms)) {
    out << field.ms;
  }
  return out;
}

} // namespace

std::filesystem::path staleTimingLogPath(const std::string &path) {
  const std::filesystem::path original(path);
  for (int n = 1;; ++n) {
    std::filesystem::path candidate = original;
    candidate.replace_filename(original.stem().string() + ".stale-" + std::to_string(n) +
                               original.extension().string());
    if (!std::filesystem::exists(candidate)) {
      return candidate;
    }
  }
}

void appendGpuTimingSample(const std::string &path, int index, int width, int height,
                           float cpuFrameMs, const GpuTimerSet &timers, bool computeActive,
                           float kerrSpin, double timeSec) {
  bool exists = std::filesystem::exists(path);
  if (exists) {
    // A log started by a build with another column set moves aside, so every
    // row of the file matches its header.
    std::string header;
    {
      std::ifstream in(path);
      std::getline(in, header);
    }
    if (header != GPU_TIMING_CSV_HEADER) {
      std::error_code error;
      std::filesystem::rename(path, staleTimingLogPath(path), error);
      if (error) {
        return;
      }
      exists = false;
    }
  }
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << GPU_TIMING_CSV_HEADER << '\n';
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << timeSec << "," << width << "," << height << "," << cpuFrameMs << ","
      << MsField{timerSampleMs(timers.blackholeFragment)} << ","
      << MsField{timerSampleMs(timers.blackholeCompute)} << ","
      << MsField{timerSampleMs(timers.bloom)} << "," << MsField{timerSampleMs(timers.tonemap)}
      << "," << MsField{timerSampleMs(timers.depth)} << ","
      << MsField{timerSampleMs(timers.grmhdSlice)} << "," << (computeActive ? 1 : 0) << ","
      << kerrSpin << "," << MsField{timerSampleMs(timers.tesseract)} << "\n";
}

void writeTimingHistoryCsv(const TimingHistory &history, const std::string &path) {
  std::filesystem::create_directories("logs/perf");
  std::ofstream out(path);
  if (!out) {
    return;
  }
  out << "index,cpu_ms,gpu_fragment_ms,gpu_compute_ms,gpu_bloom_ms,gpu_tonemap_ms,gpu_depth_ms,"
         "gpu_grmhd_slice_ms,gpu_tesseract_ms\n";
  out << std::fixed << std::setprecision(6);

  int const count = history.count;
  int start = history.offset - count;
  if (start < 0) {
    start += TimingHistory::K_CAPACITY;
  }
  for (int i = 0; i < count; ++i) {
    int const rawIndex = (start + i) % TimingHistory::K_CAPACITY;
    auto const idx = static_cast<std::size_t>(rawIndex);
    out << i << "," << history.cpuMs.at(idx) << "," << MsField{history.gpuFragmentMs.at(idx)}
        << "," << MsField{history.gpuComputeMs.at(idx)} << ","
        << MsField{history.gpuBloomMs.at(idx)} << "," << MsField{history.gpuTonemapMs.at(idx)}
        << "," << MsField{history.gpuDepthMs.at(idx)} << ","
        << MsField{history.gpuGrmhdSliceMs.at(idx)} << ","
        << MsField{history.gpuTesseractMs.at(idx)} << "\n";
  }
}

} // namespace blackhole
