#ifndef BLACKHOLE_RENDER_OUTPUT_METRICS_H
#define BLACKHOLE_RENDER_OUTPUT_METRICS_H

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <numbers>
#include <span>
#include <stdexcept>
#include <vector>

#include "render/terminal_counts.h"

namespace blackhole {

struct ImageMetrics {
  double boundaryRadius = 0.0;
  double boundaryDiameter = 0.0;
  double verticalDiameter = 0.0;
  double luminanceBoundaryRadius = 0.0;
  double luminanceBoundaryDiameter = 0.0;
  double centerOffsetX = 0.0;
  double centerOffsetY = 0.0;
  double circularity = 0.0;
  double limbRadius = 0.0;
  double limbContrast = 0.0;
  double limbWidth = 0.0;
  double centralToRing = 0.0;
  double finiteFraction = 0.0;
  double minimum = 0.0;
  double maximum = 0.0;
  double capturedFraction = 0.0;
  double escapedFraction = 0.0;
  double exhaustedFraction = 0.0;
  double invalidFraction = 0.0;
  std::vector<double> radialLuminance;
  std::uint64_t luminanceHash = 14695981039346656037ULL;
  std::uint64_t terminalHash = 14695981039346656037ULL;
};

struct ImageComparison {
  double mae = 0.0;
  double psnr = 0.0;
  double structure = 0.0;
};

// The oracle projects an asymptotic impact parameter with the vertical field
// of view and the pinhole camera distance used by the reference scenes.
[[nodiscard]] inline double criticalRadiusPixels(double mass, double distance,
                                                 double verticalFovDegrees, int imageHeight) {
  const double impact = 3.0 * std::numbers::sqrt3 * mass;
  const double angle = std::atan(impact / distance);
  return static_cast<double>(imageHeight) * std::tan(angle) /
         (2.0 * std::tan(verticalFovDegrees * std::numbers::pi / 360.0));
}

[[nodiscard]] inline ImageMetrics measureImage(std::span<const float> luminance,
                                               std::span<const std::uint8_t> terminals, int width,
                                               int height) {
  const std::size_t pixels = static_cast<std::size_t>(width) * static_cast<std::size_t>(height);
  if (width <= 0 || height <= 0 || luminance.size() != pixels || terminals.size() != pixels) {
    throw std::invalid_argument("image and terminal dimensions differ");
  }
  ImageMetrics result;
  result.minimum = std::numeric_limits<double>::max();
  result.maximum = std::numeric_limits<double>::lowest();
  result.radialLuminance.resize(static_cast<std::size_t>(std::max(width, height)), 0.0);
  std::vector<std::size_t> radialCount(result.radialLuminance.size(), 0);
  double capturedX = 0.0;
  double capturedY = 0.0;
  std::size_t captured = 0;
  std::size_t escaped = 0;
  std::size_t exhausted = 0;
  std::size_t invalid = 0;
  std::size_t finite = 0;
  for (std::size_t index = 0; index < pixels; ++index) {
    const int x = static_cast<int>(index % static_cast<std::size_t>(width));
    const int y = static_cast<int>(index / static_cast<std::size_t>(width));
    const auto terminal = terminals[index];
    result.terminalHash = (result.terminalHash ^ terminal) * 1099511628211ULL;
    if (terminal == BH_TERMINAL_HORIZON) {
      ++captured;
      capturedX += static_cast<double>(x) + 0.5;
      capturedY += static_cast<double>(y) + 0.5;
    } else if (terminal == BH_TERMINAL_ESCAPE) {
      ++escaped;
    } else if (terminal == BH_TERMINAL_MAX_STEPS) {
      ++exhausted;
    } else if (terminal == BH_TERMINAL_NON_FINITE || terminal == BH_TERMINAL_INVARIANT_FAILURE ||
               terminal >= K_TERMINAL_CLASS_COUNT) {
      ++invalid;
    }
    const auto value = static_cast<double>(luminance[index]);
    if (!std::isfinite(value)) {
      continue;
    }
    ++finite;
    result.minimum = std::min(result.minimum, value);
    result.maximum = std::max(result.maximum, value);
    const auto quantized = static_cast<std::uint64_t>(std::clamp(value, 0.0, 1.0e6) * 4096.0);
    result.luminanceHash = (result.luminanceHash ^ quantized) * 1099511628211ULL;
    const double dx = static_cast<double>(x) + 0.5 - (static_cast<double>(width) / 2.0);
    const double dy = static_cast<double>(y) + 0.5 - (static_cast<double>(height) / 2.0);
    const auto radius = static_cast<std::size_t>(std::hypot(dx, dy));
    if (radius < result.radialLuminance.size()) {
      result.radialLuminance[radius] += value;
      ++radialCount[radius];
    }
  }
  result.finiteFraction = static_cast<double>(finite) / static_cast<double>(pixels);
  result.capturedFraction = static_cast<double>(captured) / static_cast<double>(pixels);
  result.escapedFraction = static_cast<double>(escaped) / static_cast<double>(pixels);
  result.exhaustedFraction = static_cast<double>(exhausted) / static_cast<double>(pixels);
  result.invalidFraction = static_cast<double>(invalid) / static_cast<double>(pixels);
  if (finite == 0) {
    result.minimum = 0.0;
    result.maximum = 0.0;
  }
  if (captured > 0) {
    result.centerOffsetX = (capturedX / static_cast<double>(captured)) - (width / 2.0);
    result.centerOffsetY = (capturedY / static_cast<double>(captured)) - (height / 2.0);
  }
  for (std::size_t radius = 0; radius < radialCount.size(); ++radius) {
    if (radialCount[radius] > 0) {
      result.radialLuminance[radius] /= static_cast<double>(radialCount[radius]);
    }
  }
  const int midY = height / 2;
  const int midX = width / 2;
  double left = 0.0;
  double right = 0.0;
  double top = 0.0;
  double bottom = 0.0;
  for (int x = 0; x < width; ++x) {
    const auto pixel = (static_cast<std::size_t>(midY) * static_cast<std::size_t>(width)) +
                       static_cast<std::size_t>(x);
    if (terminals[pixel] == BH_TERMINAL_HORIZON) {
      left = std::max(left, static_cast<double>(midX - x));
      right = std::max(right, static_cast<double>(x - midX));
    }
  }
  for (int y = 0; y < height; ++y) {
    const auto pixel = (static_cast<std::size_t>(y) * static_cast<std::size_t>(width)) +
                       static_cast<std::size_t>(midX);
    if (terminals[pixel] == BH_TERMINAL_HORIZON) {
      bottom = std::max(bottom, static_cast<double>(midY - y));
      top = std::max(top, static_cast<double>(y - midY));
    }
  }
  result.boundaryRadius = (left + right + top + bottom) / 4.0;
  result.boundaryDiameter = left + right;
  result.verticalDiameter = top + bottom;
  const auto gradientStart = static_cast<std::size_t>(std::max(1.0, result.boundaryRadius - 8.0));
  const auto gradientEnd = std::min(result.radialLuminance.size() - 1,
                                    static_cast<std::size_t>(result.boundaryRadius + 8.0));
  double strongestGradient = -1.0;
  for (std::size_t radius = gradientStart; radius <= gradientEnd; ++radius) {
    const double gradient =
        std::abs(result.radialLuminance[radius] - result.radialLuminance[radius - 1]);
    if (gradient > strongestGradient) {
      strongestGradient = gradient;
      result.luminanceBoundaryRadius = static_cast<double>(radius) - 0.5;
    }
  }
  result.luminanceBoundaryDiameter = 2.0 * result.luminanceBoundaryRadius;
  result.circularity =
      std::max(left + right, top + bottom) > 0.0
          ? std::abs((left + right) - (top + bottom)) / std::max(left + right, top + bottom)
          : 0.0;
  const auto inner = static_cast<std::size_t>(std::max(0.0, result.boundaryRadius));
  const auto outer = std::min(result.radialLuminance.size(),
                              static_cast<std::size_t>((result.boundaryRadius * 1.8) + 4.0));
  if (inner < outer) {
    const auto peak =
        std::max_element(result.radialLuminance.begin() + static_cast<std::ptrdiff_t>(inner),
                         result.radialLuminance.begin() + static_cast<std::ptrdiff_t>(outer));
    result.limbRadius = static_cast<double>(std::distance(result.radialLuminance.begin(), peak));
    const double baseline =
        std::max(result.radialLuminance.front(),
                 result.radialLuminance[std::min(outer, result.radialLuminance.size() - 1)]);
    result.limbContrast = *peak - baseline;
    result.centralToRing = *peak > 0.0 ? result.radialLuminance.front() / *peak : 0.0;
    for (std::size_t radius = inner; radius < outer; ++radius) {
      if (result.radialLuminance[radius] > baseline + (result.limbContrast * 0.5)) {
        result.limbWidth += 1.0;
      }
    }
  }
  return result;
}

[[nodiscard]] inline ImageComparison compareImages(std::span<const float> reference,
                                                   std::span<const float> candidate) {
  if (reference.empty() || reference.size() != candidate.size()) {
    throw std::invalid_argument("comparison images differ");
  }
  double error = 0.0;
  double squared = 0.0;
  double meanReference = 0.0;
  double meanCandidate = 0.0;
  for (std::size_t index = 0; index < reference.size(); ++index) {
    const double delta =
        static_cast<double>(reference[index]) - static_cast<double>(candidate[index]);
    error += std::abs(delta);
    squared += delta * delta;
    meanReference += static_cast<double>(reference[index]);
    meanCandidate += static_cast<double>(candidate[index]);
  }
  const auto count = static_cast<double>(reference.size());
  meanReference /= count;
  meanCandidate /= count;
  double varianceReference = 0.0;
  double varianceCandidate = 0.0;
  double covariance = 0.0;
  for (std::size_t index = 0; index < reference.size(); ++index) {
    const double a = static_cast<double>(reference[index]) - meanReference;
    const double b = static_cast<double>(candidate[index]) - meanCandidate;
    varianceReference += a * a;
    varianceCandidate += b * b;
    covariance += a * b;
  }
  varianceReference /= count;
  varianceCandidate /= count;
  covariance /= count;
  constexpr double stabilizer = 0.01 * 0.01;
  return {.mae = error / count,
          .psnr = squared == 0.0 ? 120.0 : 10.0 * std::log10(count / squared),
          .structure =
              (((2.0 * meanReference * meanCandidate) + stabilizer) *
               ((2.0 * covariance) + stabilizer)) /
              (((meanReference * meanReference) + (meanCandidate * meanCandidate) + stabilizer) *
               (varianceReference + varianceCandidate + stabilizer))};
}

} // namespace blackhole

#endif
