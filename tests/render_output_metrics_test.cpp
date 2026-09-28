#include <cmath>
#include <cstddef>
#include <cstdint>
#include <vector>

#include <gtest/gtest.h>

#include "../shader/include/ray_terminal.h"
#include "render/render_output_metrics.h"

namespace {

// A captured disk of radius 12 about pixel (32, 32) inside a ring of
// luminance 0.8 out to radius 15, on a 65x65 sky of luminance 0.1.
struct SyntheticShadow {
  static constexpr int K_WIDTH = 65;
  std::vector<float> luminance;
  std::vector<std::uint8_t> terminals;
};

SyntheticShadow ringedShadow() {
  constexpr int width = SyntheticShadow::K_WIDTH;
  constexpr std::size_t pixels = static_cast<std::size_t>(width) * static_cast<std::size_t>(width);
  SyntheticShadow image{.luminance = std::vector<float>(pixels, 0.1f),
                        .terminals = std::vector<std::uint8_t>(pixels, BH_TERMINAL_ESCAPE)};
  for (int y = 0; y < width; ++y) {
    for (int x = 0; x < width; ++x) {
      const double radius = std::hypot(x - 32.0, y - 32.0);
      const auto index = (static_cast<std::size_t>(y) * static_cast<std::size_t>(width)) +
                         static_cast<std::size_t>(x);
      if (radius <= 12.0) {
        image.terminals[index] = BH_TERMINAL_HORIZON;
        image.luminance[index] = 0.01f;
      } else if (radius < 15.0) {
        image.luminance[index] = 0.8f;
      }
    }
  }
  return image;
}

} // namespace

TEST(RenderOutputMetrics, SyntheticCircularCaptureAndLimb) {
  const auto image = ringedShadow();
  const auto metrics = blackhole::measureImage(image.luminance, image.terminals,
                                               SyntheticShadow::K_WIDTH, SyntheticShadow::K_WIDTH);
  // Pixel centers within 12 of (32.5, 32.5) span 25 pixels edge to edge.
  EXPECT_NEAR(metrics.boundaryRadius, 12.5, 1e-9);
  EXPECT_NEAR(metrics.boundingWidth, 25.0, 1e-9);
  EXPECT_NEAR(metrics.boundingCenterX, 0.0, 1e-9);
  EXPECT_NEAR(metrics.luminanceBoundaryRadius, 12.5, 1.0);
  EXPECT_NEAR(metrics.centerOffsetX, 0.0, 0.1);
  EXPECT_NEAR(metrics.centerOffsetY, 0.0, 0.1);
  EXPECT_NEAR(metrics.circularity, 0.0, 0.01);
  EXPECT_GT(metrics.limbContrast, 0.5);
  EXPECT_LT(metrics.centralToRing, 0.1);
  EXPECT_EQ(metrics.finiteFraction, 1.0);
  EXPECT_GT(metrics.capturedFraction, 0.0);
  EXPECT_NE(metrics.terminalHash, 0u);
}

TEST(RenderOutputMetrics, StructuralComparisonRespondsToChangedPixels) {
  const std::vector<float> reference = {0.0f, 0.2f, 0.8f, 1.0f};
  const std::vector<float> changed = {0.0f, 0.3f, 0.7f, 1.0f};
  const auto identity = blackhole::compareImages(reference, reference);
  const auto difference = blackhole::compareImages(reference, changed);
  EXPECT_DOUBLE_EQ(identity.mae, 0.0);
  EXPECT_NEAR(identity.structure, 1.0, 1e-12);
  EXPECT_GT(difference.mae, 0.0);
  EXPECT_LT(difference.psnr, identity.psnr);
  EXPECT_LT(difference.structure, identity.structure);
}

TEST(RenderOutputMetrics, HardMatteHasNoLocalizedEmissionLimb) {
  constexpr int width = 65;
  constexpr std::size_t pixels = static_cast<std::size_t>(width) * static_cast<std::size_t>(width);
  std::vector<float> luminance(pixels, 0.1f);
  std::vector<std::uint8_t> terminals(pixels, BH_TERMINAL_ESCAPE);
  for (int y = 0; y < width; ++y) {
    for (int x = 0; x < width; ++x) {
      if (std::hypot(x - 32.0, y - 32.0) <= 12.0) {
        const auto index = (static_cast<std::size_t>(y) * static_cast<std::size_t>(width)) +
                           static_cast<std::size_t>(x);
        terminals[index] = BH_TERMINAL_HORIZON;
        luminance[index] = 0.0f;
      }
    }
  }
  const auto metrics = blackhole::measureImage(luminance, terminals, width, width);
  EXPECT_LE(metrics.limbContrast, 1e-6);
}

TEST(RenderOutputMetrics, LimbFollowsDisplacedShadow) {
  // A shadow 10 pixels right of the image center keeps its ring in one radial
  // bin of the centroid-centered profile.
  constexpr int width = 81;
  constexpr std::size_t pixels = static_cast<std::size_t>(width) * static_cast<std::size_t>(width);
  std::vector<float> luminance(pixels, 0.1f);
  std::vector<std::uint8_t> terminals(pixels, BH_TERMINAL_ESCAPE);
  for (int y = 0; y < width; ++y) {
    for (int x = 0; x < width; ++x) {
      const double radius = std::hypot(x - 50.0, y - 40.0);
      const auto index = (static_cast<std::size_t>(y) * static_cast<std::size_t>(width)) +
                         static_cast<std::size_t>(x);
      if (radius <= 12.0) {
        terminals[index] = BH_TERMINAL_HORIZON;
        luminance[index] = 0.0f;
      } else if (radius < 14.0) {
        luminance[index] = 0.8f;
      }
    }
  }
  const auto metrics = blackhole::measureImage(luminance, terminals, width, width);
  EXPECT_NEAR(metrics.centerOffsetX, 10.0, 1e-9);
  EXPECT_NEAR(metrics.boundingCenterX, 10.0, 1e-9);
  EXPECT_GT(metrics.limbContrast, 0.5);
  EXPECT_GE(metrics.limbWidth, 1.0);
  EXPECT_LE(metrics.limbWidth, 3.0);
}

TEST(RenderOutputMetrics, DiskSidesAndNearSideEdgeUseDiskTerminals) {
  constexpr int width = 8;
  constexpr int height = 8;
  std::vector<float> luminance(width * height, 10.0f);
  std::vector<std::uint8_t> terminals(width * height, BH_TERMINAL_ESCAPE);
  const auto markDisk = [&](int column, int row, float value) {
    const auto index = static_cast<std::size_t>(row * width + column);
    terminals[index] = BH_TERMINAL_DISK_HIT;
    luminance[index] = value;
  };
  markDisk(1, 2, 0.8f);
  markDisk(2, 6, 0.6f);
  markDisk(5, 2, 0.2f);
  markDisk(6, 6, 0.4f);
  markDisk(4, 5, 0.3f);
  const auto metrics = blackhole::measureDiskImage(luminance, terminals, width, height);
  EXPECT_EQ(metrics.leftDiskPixels, 2u);
  EXPECT_EQ(metrics.rightDiskPixels, 3u);
  EXPECT_NEAR(metrics.leftMeanLuminance, 0.7, 1e-6);
  EXPECT_NEAR(metrics.rightMeanLuminance, 0.3, 1e-6);
  EXPECT_DOUBLE_EQ(metrics.nearSideInnerEdgePixels, 1.5);
}
