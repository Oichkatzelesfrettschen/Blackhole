#include <cmath>
#include <cstddef>
#include <cstdint>
#include <vector>

#include <gtest/gtest.h>

#include "../shader/include/ray_terminal.h"
#include "render/render_output_metrics.h"

TEST(RenderOutputMetrics, SyntheticCircularCaptureAndLimb) {
  constexpr int width = 65;
  constexpr int height = 65;
  constexpr std::size_t pixels = static_cast<std::size_t>(width) * static_cast<std::size_t>(height);
  std::vector<float> luminance(pixels, 0.1f);
  std::vector<std::uint8_t> terminals(pixels, BH_TERMINAL_ESCAPE);
  for (int y = 0; y < height; ++y) {
    for (int x = 0; x < width; ++x) {
      const double radius = std::hypot(x - 32.0, y - 32.0);
      const auto index = (static_cast<std::size_t>(y) * static_cast<std::size_t>(width)) +
                         static_cast<std::size_t>(x);
      if (radius <= 12.0) {
        terminals[index] = BH_TERMINAL_HORIZON;
        luminance[index] = 0.01f;
      } else if (radius < 15.0) {
        luminance[index] = 0.8f;
      }
    }
  }
  const auto metrics = blackhole::measureImage(luminance, terminals, width, height);
  EXPECT_NEAR(metrics.boundaryRadius, 12.0, 0.5);
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
