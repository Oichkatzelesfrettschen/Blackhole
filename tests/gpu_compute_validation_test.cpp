/**
 * @file gpu_compute_validation_test.cpp
 * @brief CPU storage and tile-coverage fixtures for RGBA32F compute output.
 *
 * Shader compilation, GPU occupancy, register allocation, asynchronous execution,
 * and frame latency require separate shader validation or a device run.
 */

#include <algorithm>
#include <array>
#include <cstddef>
#include <iostream>
#include <limits>
#include <vector>

namespace {

// geodesic_trace.comp writes one RGBA32F image texel per in-bounds invocation.
using OutputPixel = std::array<float, 4>;
static_assert(sizeof(float) == 4 && std::numeric_limits<float>::is_iec559);
static_assert(sizeof(OutputPixel) == 16);

constexpr std::size_t tileCount(std::size_t extent, std::size_t tileSize) {
  return extent / tileSize + (extent % tileSize == 0 ? 0U : 1U);
}

static_assert(tileCount(1920, 32) == 60);
static_assert(tileCount(1080, 32) == 34);
static_assert(tileCount(0, 32) == 0);
static_assert(tileCount(33, 32) == 2);
static_assert(std::size_t{1920} * 1080 * sizeof(OutputPixel) == 33177600);

bool testTileCoverage(std::size_t width, std::size_t height) {
  constexpr std::size_t tileSize = 32;
  std::vector<unsigned int> visits(width * height, 0);
  for (std::size_t tileY = 0; tileY < tileCount(height, tileSize); ++tileY) {
    for (std::size_t tileX = 0; tileX < tileCount(width, tileSize); ++tileX) {
      for (std::size_t localY = 0; localY < tileSize; ++localY) {
        for (std::size_t localX = 0; localX < tileSize; ++localX) {
          const auto pixelX = tileX * tileSize + localX;
          const auto pixelY = tileY * tileSize + localY;
          if (pixelX < width && pixelY < height) {
            ++visits.at(pixelY * width + pixelX);
          }
        }
      }
    }
  }
  return std::ranges::all_of(visits, [](unsigned int count) { return count == 1; });
}

bool testOutputPacking() {
  const std::array<OutputPixel, 3> pixels{{
      {0.5f, 0.4f, 0.3f, 1.0f}, {0.2f, 0.1f, 0.0f, 0.5f}, {1.0f, 0.0f, 0.5f, 0.0f}}};
  std::vector<float> packed;
  packed.reserve(pixels.size() * pixels.front().size());
  for (const auto &pixel : pixels) {
    packed.insert(packed.end(), pixel.begin(), pixel.end());
  }
  const std::array<float, 12> expected{
      0.5f, 0.4f, 0.3f, 1.0f, 0.2f, 0.1f, 0.0f, 0.5f, 1.0f, 0.0f, 0.5f, 0.0f};
  return std::ranges::equal(packed, expected);
}

} // namespace

int main() {
  const std::array<std::array<std::size_t, 2>, 6> frames{{
      {0, 0}, {1, 1}, {32, 32}, {33, 31}, {65, 67}, {1920, 1080}}};
  const bool coverageOk = std::ranges::all_of(frames, [](const auto &frame) {
    return testTileCoverage(frame.at(0), frame.at(1));
  });
  const bool packingOk = testOutputPacking();
  std::cout << "CPU RGBA32F fixture packing: " << (packingOk ? "PASS" : "FAIL") << '\n'
            << "CPU tile-coverage fixtures: " << (coverageOk ? "PASS" : "FAIL") << '\n'
            << "GPU shader execution and performance remain unqualified by this executable.\n";
  return coverageOk && packingOk ? 0 : 1;
}
