/**
 * @file compare_harness.cpp
 * @brief Diff statistics, texture readback, snapshot writers, and CSV
 *        summaries for the compute/fragment parity harness.
 */

#include "compare_harness.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <ios>
#include <system_error>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>

using namespace gl;

namespace blackhole {

DiffStats sampleTextureDiff(GLuint texA, GLuint texB, int width, int height, int sampleSize) {
  DiffStats stats;
  if (texA == 0 || texB == 0 || width <= 0 || height <= 0 || sampleSize <= 0) {
    return stats;
  }

  const int sampleW = std::min(sampleSize, width);
  const int sampleH = std::min(sampleSize, height);
  const int offsetX = (width - sampleW) / 2;
  const int offsetY = (height - sampleH) / 2;
  const auto pixelCount = static_cast<std::size_t>(sampleW) * static_cast<std::size_t>(sampleH);
  const std::size_t channelCount = pixelCount * 4;

  std::vector<float> dataA(channelCount, 0.0f);
  std::vector<float> dataB(channelCount, 0.0f);

  glGetTextureSubImage(texA, 0, offsetX, offsetY, 0, sampleW, sampleH, 1, GL_RGBA, GL_FLOAT,
                       static_cast<GLsizei>(channelCount * sizeof(float)), dataA.data());
  glGetTextureSubImage(texB, 0, offsetX, offsetY, 0, sampleW, sampleH, 1, GL_RGBA, GL_FLOAT,
                       static_cast<GLsizei>(channelCount * sizeof(float)), dataB.data());

  double total = 0.0;
  double totalSq = 0.0;
  double maxAbs = 0.0;
  for (std::size_t i = 0; i < channelCount; i += 4) {
    for (std::size_t c = 0; c < 3; ++c) {
      double const diff =
          std::abs(static_cast<double>(dataA.at(i + c)) - static_cast<double>(dataB.at(i + c)));
      total += diff;
      totalSq += diff * diff;
      maxAbs = std::max(maxAbs, diff);
    }
  }

  const auto denom = static_cast<double>(pixelCount * 3);
  if (denom > 0.0) {
    stats.meanAbs = static_cast<float>(total / denom);
    stats.rms = static_cast<float>(std::sqrt(totalSq / denom));
    stats.maxAbs = static_cast<float>(maxAbs);
    stats.valid = true;
  }

  return stats;
}

bool readTextureRGBA(GLuint texture, int width, int height, std::vector<float> &out) {
  if (texture == 0 || width <= 0 || height <= 0) {
    return false;
  }
  const std::size_t channelCount =
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height) * 4u;
  out.assign(channelCount, 0.0f);
  glGetTextureSubImage(texture, 0, 0, 0, 0, width, height, 1, GL_RGBA, GL_FLOAT,
                       static_cast<GLsizei>(channelCount * sizeof(float)), out.data());
  return true;
}

bool writePfmRgb(const std::string &path, const std::vector<float> &rgba, int width, int height) {
  if (width <= 0 || height <= 0) {
    return false;
  }
  std::size_t const expected =
      static_cast<std::size_t>(width) * static_cast<std::size_t>(height) * 4u;
  if (rgba.size() < expected) {
    return false;
  }

  std::filesystem::path const outPath(path);
  std::error_code dirEc;
  if (outPath.has_parent_path()) {
    std::filesystem::create_directories(outPath.parent_path(), dirEc);
    if (dirEc) {
      std::fprintf(stderr, "Failed to create directory for raw export %s: %s\n",
                   outPath.string().c_str(), dirEc.message().c_str());
      return false;
    }
  }

  std::ofstream out(path, std::ios::binary);
  if (!out.is_open()) {
    return false;
  }

  out << "PF\n" << width << " " << height << "\n-1.0\n";
  std::vector<float> row(static_cast<std::size_t>(width) * 3u, 0.0f);
  for (int y = height - 1; y >= 0; --y) {
    for (int x = 0; x < width; ++x) {
      std::size_t const src =
          (static_cast<std::size_t>(y) * static_cast<std::size_t>(width) +
           static_cast<std::size_t>(x)) * 4u;
      std::size_t const dst = static_cast<std::size_t>(x) * 3u;
      row[dst + 0] = rgba[src + 0];
      row[dst + 1] = rgba[src + 1];
      row[dst + 2] = rgba[src + 2];
    }
    out.write(reinterpret_cast<const char *>(row.data()),
              static_cast<std::streamsize>(row.size() * sizeof(float)));
  }
  return static_cast<bool>(out);
}

DiffStats computeDiffStats(const std::vector<float> &a, const std::vector<float> &b) {
  DiffStats stats;
  if (a.size() != b.size() || a.empty()) {
    return stats;
  }

  double total = 0.0;
  double totalSq = 0.0;
  double maxAbs = 0.0;
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    for (std::size_t c = 0; c < 3; ++c) {
      double const diff =
          std::abs(static_cast<double>(a.at(i + c)) - static_cast<double>(b.at(i + c)));
      total += diff;
      totalSq += diff * diff;
      maxAbs = std::max(maxAbs, diff);
    }
  }

  const auto denom = static_cast<double>(
      (a.size() / 4) *
      3); // NOLINT(bugprone-integer-division) -- intentional: pixel count * 3 channels
  if (denom > 0.0) {
    stats.meanAbs = static_cast<float>(total / denom);
    stats.rms = static_cast<float>(std::sqrt(totalSq / denom));
    stats.maxAbs = static_cast<float>(maxAbs);
    stats.valid = true;
  }
  return stats;
}

std::size_t countDiffOutliers(const std::vector<float> &a, const std::vector<float> &b,
                              float threshold) {
  if (a.size() != b.size() || a.empty() || threshold <= 0.0f) {
    return 0;
  }
  std::size_t count = 0;
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    double const dr = std::abs(static_cast<double>(a.at(i)) - static_cast<double>(b.at(i)));
    double const dg = std::abs(static_cast<double>(a.at(i + 1)) - static_cast<double>(b.at(i + 1)));
    double const db = std::abs(static_cast<double>(a.at(i + 2)) - static_cast<double>(b.at(i + 2)));
    if (std::max({dr, dg, db}) > static_cast<double>(threshold)) {
      ++count;
    }
  }
  return count;
}

bool writePpm(const std::string &path, const std::vector<float> &rgba, int width, int height,
              float scale) {
  if (rgba.empty() || width <= 0 || height <= 0) {
    return false;
  }
  std::ofstream out(path, std::ios::binary);
  if (!out) {
    return false;
  }
  out << "P6\n" << width << " " << height << "\n255\n";
  for (std::size_t i = 0; i + 3 < rgba.size(); i += 4) {
    auto clampChannel = [&](float v) -> unsigned char {
      float const scaled = std::clamp(v * scale, 0.0f, 1.0f);
      return static_cast<unsigned char>(scaled * 255.0f);
    };
    unsigned char rgb[3] = {clampChannel(rgba.at(i)), clampChannel(rgba.at(i + 1)),
                            clampChannel(rgba.at(i + 2))};
    out.write(reinterpret_cast<const char *>(rgb), 3);
  }
  return true;
}

bool writeDiffPpm(const std::string &path, const std::vector<float> &a, const std::vector<float> &b,
                  int width, int height, float scale) {
  if (a.size() != b.size() || a.empty() || width <= 0 || height <= 0) {
    return false;
  }
  std::ofstream out(path, std::ios::binary);
  if (!out) {
    return false;
  }
  out << "P6\n" << width << " " << height << "\n255\n";
  for (std::size_t i = 0; i + 3 < a.size(); i += 4) {
    auto clampChannel = [&](float v) -> unsigned char {
      float const scaled = std::clamp(v * scale, 0.0f, 1.0f);
      return static_cast<unsigned char>(scaled * 255.0f);
    };
    float const dr = std::abs(a.at(i) - b.at(i));
    float const dg = std::abs(a.at(i + 1) - b.at(i + 1));
    float const db = std::abs(a.at(i + 2) - b.at(i + 2));
    unsigned char rgb[3] = {clampChannel(dr), clampChannel(dg), clampChannel(db)};
    out.write(reinterpret_cast<const char *>(rgb), 3);
  }
  return true;
}

std::string compareSnapshotPath(int index, const std::string &tag) {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_" + std::to_string(index) + "_" + tag + ".ppm";
}

std::string compareSummaryPath() {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_summary.csv";
}

std::string compareUniformsPath() {
  std::filesystem::create_directories("logs/compare");
  return "logs/compare/compare_uniforms.csv";
}

void appendCompareSummary(const std::string &path, int index, const std::string &primaryTag,
                          const std::string &secondaryTag, int width, int height,
                          const DiffStats &stats, float diffScale, bool wroteOutputs,
                          bool wroteDiff, float threshold, bool exceeded, double timeSec,
                          float kerrSpin, bool grbEnabled, float grbTime, int outlierCount,
                          int outlierLimit, float outlierFrac) {
  if (!stats.valid) {
    return;
  }
  const bool exists = std::filesystem::exists(path);
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << "index,primary,secondary,width,height,mean_abs,rms,max_abs,diff_scale,threshold,"
           "exceeded,"
           "write_outputs,write_diff,time_sec,kerr_spin,grb_enabled,grb_time,outlier_count,"
           "outlier_limit,outlier_frac\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << primaryTag << "," << secondaryTag << "," << width << "," << height << ","
      << stats.meanAbs << "," << stats.rms << "," << stats.maxAbs << "," << diffScale << ","
      << threshold << "," << (exceeded ? 1 : 0) << "," << (wroteOutputs ? 1 : 0) << ","
      << (wroteDiff ? 1 : 0) << "," << timeSec << "," << kerrSpin << "," << (grbEnabled ? 1 : 0)
      << "," << grbTime << "," << outlierCount << "," << outlierLimit << "," << outlierFrac << "\n";
}

void appendCompareUniforms(const std::string &path, int index, const std::string &label,
                           const InteropUniforms &interop, bool compareBaseline,
                           bool compareOverrides, bool backgroundEnabled, bool noiseEnabled,
                           bool grmhdEnabled, bool spectralEnabled, bool grbEnabled,
                           bool photonSphereEnabled) {
  const bool exists = std::filesystem::exists(path);
  std::ofstream out(path, std::ios::app);
  if (!out) {
    return;
  }
  if (!exists) {
    out << "index,label,camera_x,camera_y,camera_z,fov_scale,time_sec,depth_far,"
           "schwarzschild_radius,isco_radius,kerr_spin,max_steps,step_size,adisk_enabled,"
           "enable_redshift,use_luts,use_spectral_lut,use_grb_modulation,background_enabled,"
           "noise_enabled,grmhd_enabled,spectral_enabled,grb_enabled,photon_sphere_enabled,"
           "compare_baseline,compare_overrides\n";
  }
  out << std::fixed << std::setprecision(6);
  out << index << "," << label << "," << interop.cameraPos.x << "," << interop.cameraPos.y << ","
      << interop.cameraPos.z << "," << interop.fovScale << "," << interop.timeSec << ","
      << interop.depthFar << "," << interop.schwarzschildRadius << "," << interop.iscoRadius << ","
      << interop.kerrSpin << "," << interop.maxSteps << "," << interop.stepSize << ","
      << interop.adiskEnabled << "," << interop.enableRedshift << "," << interop.useLUTs << ","
      << interop.useSpectralLUT << "," << interop.useGrbModulation << ","
      << (backgroundEnabled ? 1 : 0) << "," << (noiseEnabled ? 1 : 0) << ","
      << (grmhdEnabled ? 1 : 0) << "," << (spectralEnabled ? 1 : 0) << "," << (grbEnabled ? 1 : 0)
      << "," << (photonSphereEnabled ? 1 : 0) << "," << (compareBaseline ? 1 : 0) << ","
      << (compareOverrides ? 1 : 0) << "\n";
}

} // namespace blackhole
