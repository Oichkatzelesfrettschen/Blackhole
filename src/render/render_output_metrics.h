#ifndef BLACKHOLE_RENDER_OUTPUT_METRICS_H
#define BLACKHOLE_RENDER_OUTPUT_METRICS_H

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <limits>
#include <numbers>
#include <optional>
#include <span>
#include <stdexcept>
#include <vector>

#include "render/terminal_counts.h"

namespace blackhole {

struct ImageMetrics {
  double boundaryRadius = 0.0;
  double boundaryDiameter = 0.0;
  double verticalDiameter = 0.0;
  double boundingWidth = 0.0;   ///< Captured bounding box, pixel edge to pixel edge.
  double boundingHeight = 0.0;
  double boundingCenterX = 0.0; ///< Box center minus image center; +x right, +y down.
  double boundingCenterY = 0.0;
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

/// Oracle-predicted critical curve that anchors the radial profile: center
/// offset from the image center (+x right, +y down) and radius, in pixels.
struct ProfileAnchor {
  double centerX = 0.0;
  double centerY = 0.0;
  double radius = 0.0;
};

struct ImageComparison {
  double mae = 0.0;
  double psnr = 0.0;
  double structure = 0.0;
};

// Screen radius, in pixels, of the Schwarzschild critical curve seen by the
// reference camera. kerrInitGeodesic (shader/include/kerr.glsl) takes the pixel
// direction as the coordinate spatial velocity at radius r, so a ray at angle
// psi from the inward radial carries k^r = -cos(psi), r k^phi = sin(psi), and
// the null condition fixes E = f k^t with f = 1 - 2M/r. Its impact parameter is
//   b(psi) = r sin(psi) / sqrt(cos^2(psi) + f sin^2(psi)),
// and b = 3 sqrt(3) M solves to sin^2(psi) = b^2 / (r^2 + (1 - f) b^2). The
// pinhole then maps tan(psi) onto the image with fovScale = tan(fov / 2).
[[nodiscard]] inline double criticalRadiusPixels(double mass, double distance,
                                                 double verticalFovDegrees, int imageHeight) {
  const double impact = 3.0 * std::numbers::sqrt3 * mass;
  const double lapseSquared = 1.0 - (2.0 * mass / distance);
  const double sineSquared =
      (impact * impact) / ((distance * distance) + ((1.0 - lapseSquared) * impact * impact));
  const double tangent = std::sqrt(sineSquared / (1.0 - sineSquared));
  return static_cast<double>(imageHeight) * tangent /
         (2.0 * std::tan(verticalFovDegrees * std::numbers::pi / 360.0));
}

namespace detail {

// Diameters along the row and column through (centerX, centerY), edge to edge.
inline void measureExtents(ImageMetrics &result, std::span<const std::uint8_t> terminals,
                           int width, int height, double centerX, double centerY) {
  const auto index = [width](int x, int y) {
    return (static_cast<std::size_t>(y) * static_cast<std::size_t>(width)) +
           static_cast<std::size_t>(x);
  };
  const int row = std::clamp(static_cast<int>(centerY), 0, height - 1);
  const int column = std::clamp(static_cast<int>(centerX), 0, width - 1);
  int minX = width;
  int maxX = -1;
  int minY = height;
  int maxY = -1;
  for (int x = 0; x < width; ++x) {
    if (terminals[index(x, row)] == BH_TERMINAL_HORIZON) {
      minX = std::min(minX, x);
      maxX = std::max(maxX, x);
    }
  }
  for (int y = 0; y < height; ++y) {
    if (terminals[index(column, y)] == BH_TERMINAL_HORIZON) {
      minY = std::min(minY, y);
      maxY = std::max(maxY, y);
    }
  }
  result.boundaryDiameter = maxX >= minX ? static_cast<double>(maxX - minX + 1) : 0.0;
  result.verticalDiameter = maxY >= minY ? static_cast<double>(maxY - minY + 1) : 0.0;
  result.boundaryRadius = (result.boundaryDiameter + result.verticalDiameter) / 4.0;
  const double widest = std::max(result.boundaryDiameter, result.verticalDiameter);
  result.circularity =
      widest > 0.0 ? std::abs(result.boundaryDiameter - result.verticalDiameter) / widest : 0.0;
}

// The limb is a local maximum of the radial profile near the critical radius,
// measured against the profile three bins inside and outside it; a hard matte
// steps from dark to sky with no such maximum.
inline void measureLimb(ImageMetrics &result, double limbCenter, bool anyCaptured) {
  const auto bins = result.radialLuminance.size();
  constexpr std::size_t shoulder = 3;
  const auto limbStart =
      static_cast<std::size_t>(std::max(static_cast<double>(shoulder), limbCenter - 2.0));
  const auto limbEnd =
      std::min(bins - 1 - shoulder, static_cast<std::size_t>(limbCenter + 8.0));
  if (anyCaptured && limbStart <= limbEnd) {
    std::size_t peak = limbStart;
    for (std::size_t radius = limbStart; radius <= limbEnd; ++radius) {
      if (result.radialLuminance[radius] > result.radialLuminance[peak]) {
        peak = radius;
      }
    }
    const double peakValue = result.radialLuminance[peak];
    const double baseline = std::max(result.radialLuminance[peak - shoulder],
                                     result.radialLuminance[peak + shoulder]);
    result.limbRadius = static_cast<double>(peak);
    result.limbContrast = peakValue - baseline;
    result.centralToRing = peakValue > 0.0 ? result.radialLuminance.front() / peakValue : 0.0;
    if (result.limbContrast > 0.0) {
      const double halfMaximum = baseline + (result.limbContrast * 0.5);
      std::size_t lower = peak;
      while (lower > 0 && result.radialLuminance[lower - 1] > halfMaximum) {
        --lower;
      }
      std::size_t upper = peak;
      while (upper + 1 < bins && result.radialLuminance[upper + 1] > halfMaximum) {
        ++upper;
      }
      result.limbWidth = static_cast<double>(upper - lower + 1);
    }
  }
}

} // namespace detail

// Pixel (x, y) covers [x, x + 1) x [y, y + 1), so its center sits at x + 0.5
// and a run of captured pixels xmin..xmax spans xmax - xmin + 1 pixels edge to
// edge. The radial profile is centered on the anchor when one is given, since
// an emitting disk that occludes part of the shadow biases the captured
// centroid; otherwise on the captured centroid, so a shadow displaced by spin
// keeps its limb in one radial bin.
[[nodiscard]] inline ImageMetrics measureImage(std::span<const float> luminance,
                                               std::span<const std::uint8_t> terminals, int width,
                                               int height,
                                               std::optional<ProfileAnchor> anchor = std::nullopt) {
  const std::size_t pixels = static_cast<std::size_t>(width) * static_cast<std::size_t>(height);
  if (width <= 0 || height <= 0 || luminance.size() != pixels || terminals.size() != pixels) {
    throw std::invalid_argument("image and terminal dimensions differ");
  }
  const auto at = [width](int x, int y) {
    return (static_cast<std::size_t>(y) * static_cast<std::size_t>(width)) +
           static_cast<std::size_t>(x);
  };
  ImageMetrics result;
  result.minimum = std::numeric_limits<double>::max();
  result.maximum = std::numeric_limits<double>::lowest();
  double capturedX = 0.0;
  double capturedY = 0.0;
  std::size_t captured = 0;
  std::size_t escaped = 0;
  std::size_t exhausted = 0;
  std::size_t invalid = 0;
  std::size_t finite = 0;
  int boxMinX = width;
  int boxMaxX = -1;
  int boxMinY = height;
  int boxMaxY = -1;
  for (std::size_t index = 0; index < pixels; ++index) {
    const int x = static_cast<int>(index % static_cast<std::size_t>(width));
    const int y = static_cast<int>(index / static_cast<std::size_t>(width));
    const auto terminal = terminals[index];
    result.terminalHash = (result.terminalHash ^ terminal) * 1099511628211ULL;
    if (terminal == BH_TERMINAL_HORIZON) {
      ++captured;
      capturedX += static_cast<double>(x) + 0.5;
      capturedY += static_cast<double>(y) + 0.5;
      boxMinX = std::min(boxMinX, x);
      boxMaxX = std::max(boxMaxX, x);
      boxMinY = std::min(boxMinY, y);
      boxMaxY = std::max(boxMaxY, y);
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
  }
  const auto count = static_cast<double>(pixels);
  result.finiteFraction = static_cast<double>(finite) / count;
  result.capturedFraction = static_cast<double>(captured) / count;
  result.escapedFraction = static_cast<double>(escaped) / count;
  result.exhaustedFraction = static_cast<double>(exhausted) / count;
  result.invalidFraction = static_cast<double>(invalid) / count;
  if (finite == 0) {
    result.minimum = 0.0;
    result.maximum = 0.0;
  }
  double centerX = static_cast<double>(width) / 2.0;
  double centerY = static_cast<double>(height) / 2.0;
  if (captured > 0) {
    centerX = capturedX / static_cast<double>(captured);
    centerY = capturedY / static_cast<double>(captured);
    result.centerOffsetX = centerX - (static_cast<double>(width) / 2.0);
    result.centerOffsetY = centerY - (static_cast<double>(height) / 2.0);
    result.boundingWidth = static_cast<double>(boxMaxX - boxMinX + 1);
    result.boundingHeight = static_cast<double>(boxMaxY - boxMinY + 1);
    result.boundingCenterX =
        (static_cast<double>(boxMinX + boxMaxX + 1) - static_cast<double>(width)) / 2.0;
    result.boundingCenterY =
        (static_cast<double>(boxMinY + boxMaxY + 1) - static_cast<double>(height)) / 2.0;
  }
  if (anchor) {
    centerX = (static_cast<double>(width) / 2.0) + anchor->centerX;
    centerY = (static_cast<double>(height) / 2.0) + anchor->centerY;
  }

  result.radialLuminance.resize(static_cast<std::size_t>(std::max(width, height)), 0.0);
  std::vector<std::size_t> radialCount(result.radialLuminance.size(), 0);
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const auto value = static_cast<double>(luminance[at(x, y)]);
      const auto radius = static_cast<std::size_t>(
          std::hypot(static_cast<double>(x) + 0.5 - centerX, static_cast<double>(y) + 0.5 - centerY));
      if (std::isfinite(value) && radius < result.radialLuminance.size()) {
        result.radialLuminance[radius] += value;
        ++radialCount[radius];
      }
    }
  }
  for (std::size_t radius = 0; radius < radialCount.size(); ++radius) {
    if (radialCount[radius] > 0) {
      result.radialLuminance[radius] /= static_cast<double>(radialCount[radius]);
    }
  }

  detail::measureExtents(result, terminals, width, height, centerX, centerY);

  const auto bins = result.radialLuminance.size();
  const auto gradientStart = static_cast<std::size_t>(std::max(1.0, result.boundaryRadius - 8.0));
  const auto gradientEnd =
      std::min(bins - 1, static_cast<std::size_t>(result.boundaryRadius + 8.0));
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

  detail::measureLimb(result, anchor ? anchor->radius : result.boundaryRadius, captured > 0);
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
