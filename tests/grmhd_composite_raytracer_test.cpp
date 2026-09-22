/**
 * @file grmhd_composite_raytracer_test.cpp
 * @brief CPU GRMHD interpolation and composite arithmetic fixtures.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <iostream>
#include <vector>

#include "physics/timeseries_interpolation.h"

// Test 1: Ray + GRMHD field blending
namespace {

bool testCompositeBlending() {
  std::cout << "Test 1: Ray and GRMHD Field Blending\n";

  // Synthetic ray color for the CPU blending fixture.
  struct RayColor {
    float r, g, b, a;
  } const ray = {.r = 0.5f, .g = 0.4f, .b = 0.3f, .a = 1.0f};

  // GRMHD field sample
  struct GRMHDField {
    float rho, uu, bMag, temp;
  } const field = {.rho = 0.1f, .uu = 0.05f, .bMag = 1.0f, .temp = 1e6f};

  // Synchrotron fraction: B^2 / (T + 1)
  float const synchFrac = std::min(1.0f, field.bMag * field.bMag / (field.temp + 1.0f));

  // Synchrotron color: density-weighted
  float const syncIntensity = synchFrac * (field.rho + 0.5f);
  RayColor const syncColor = {
      .r = syncIntensity, .g = syncIntensity * 0.8f, .b = syncIntensity * 0.6f, .a = 1.0f};

  // Composite: 70% ray, 30% synchrotron
  RayColor composite{};
  composite.r = (0.7f * ray.r) + (0.3f * syncColor.r);
  composite.g = (0.7f * ray.g) + (0.3f * syncColor.g);
  composite.b = (0.7f * ray.b) + (0.3f * syncColor.b);

  bool const blendingOk = (composite.r >= 0.0f && composite.r <= 1.0f && composite.g >= 0.0f &&
                           composite.g <= 1.0f && composite.b >= 0.0f && composite.b <= 1.0f);

  std::cout << "  Ray color: (" << ray.r << ", " << ray.g << ", " << ray.b << ")\n"
            << "  Synch fraction: " << synchFrac << "\n"
            << "  Composite: (" << composite.r << ", " << composite.g << ", " << composite.b
            << ")\n"
            << "  Status: " << (blendingOk ? "PASS" : "FAIL") << "\n\n";

  return blendingOk;
}

// Test 2: Synchrotron fraction computation
bool testSynchrotronFraction() {
  std::cout << "Test 2: Synchrotron Fraction Computation\n";

  struct GRMHDField {
    float bMag, temp;
  };

  // Test cases: low B, high T -> low synchrotron
  GRMHDField const weak = {.bMag = 0.1f, .temp = 1e7f};
  float const weakSync = std::min(1.0f, weak.bMag * weak.bMag / (weak.temp + 1.0f));

  // High B, low T -> high synchrotron
  GRMHDField const strong = {.bMag = 10.0f, .temp = 1e3f};
  float const strongSync = std::min(1.0f, strong.bMag * strong.bMag / (strong.temp + 1.0f));

  bool const orderingOk = (weakSync < strongSync);

  std::cout << "  Weak field (B=0.1, T=1e7): " << weakSync << "\n"
            << "  Strong field (B=10, T=1e3): " << strongSync << "\n"
            << "  Ordering correct: " << (orderingOk ? "true" : "false") << "\n"
            << "  Status: " << (orderingOk ? "PASS" : "FAIL") << "\n\n";

  return orderingOk;
}

// Test 3: Composite output buffer layout
bool testOutputBufferLayout() {
  std::cout << "Test 3: Composite Output Buffer Layout\n";

  // Frame: 1920x1080
  constexpr uint32_t width = 1920;
  constexpr uint32_t height = 1080;
  constexpr uint32_t pixelCount = width * height; // 2,073,600

  // RGBA float32 output: 4 floats per pixel
  constexpr uint32_t bytesPerPixel = 4 * sizeof(float);       // 16 bytes
  constexpr uint32_t bufferSize = pixelCount * bytesPerPixel; // 33.2MB
  static_assert(bytesPerPixel == 16);
  static_assert(bufferSize == 33177600);

  // Simulate output buffer
  std::vector<float> compositeBuffer(static_cast<std::size_t>(pixelCount) * 4U, 0.0f);

  // Fill sample pixels
  for (uint32_t i = 0; i < 100; ++i) {
    compositeBuffer.at((i * 4) + 0) = 0.5f; // R
    compositeBuffer.at((i * 4) + 1) = 0.4f; // G
    compositeBuffer.at((i * 4) + 2) = 0.3f; // B
    compositeBuffer.at((i * 4) + 3) = 1.0f; // A
  }

  const std::array<float, 4> expectedPixel{0.5f, 0.4f, 0.3f, 1.0f};
  bool layoutOk = true;
  for (std::size_t pixel = 0; pixel < 100; ++pixel) {
    for (std::size_t channel = 0; channel < expectedPixel.size(); ++channel) {
      layoutOk = (compositeBuffer.at(pixel * 4 + channel) == expectedPixel.at(channel)) && layoutOk;
    }
  }
  layoutOk = std::all_of(compositeBuffer.begin() + 400, compositeBuffer.end(),
                         [](float value) { return value == 0.0f; }) && layoutOk;

  std::cout << "  Display: " << width << "x" << height << "\n"
            << "  Pixels: " << pixelCount << "\n"
            << "  Buffer size: " << (bufferSize / 1024 / 1024) << " MB\n"
            << "  Layout correct: " << (layoutOk ? "true" : "false") << "\n"
            << "  Status: " << (layoutOk ? "PASS" : "FAIL") << "\n\n";

  return layoutOk;
}

// Test 4: Ray depth-based GRMHD sampling
bool testDepthBasedSampling() {
  std::cout << "Test 4: Depth-Based GRMHD Field Sampling\n";

  struct Ray {
    float depth; // -1 = escaped, 0 = horizon, >0 = distance
  };

  // Test rays
  Ray const escaped = {-1.0f};
  Ray const horizon = {0.0f};
  Ray const disk = {5.0f};

  // Sampling decision: only sample if 0 < depth < horizon_radius * 10
  auto shouldSample = [](const Ray &r) { return r.depth > 0.0f && r.depth < 1e6f; };

  bool const decisionsOk = (!shouldSample(escaped) && !shouldSample(horizon) && shouldSample(disk));

  std::cout << "  Escaped ray (depth=-1): " << (shouldSample(escaped) ? "sample" : "skip") << "\n"
            << "  Horizon ray (depth=0): " << (shouldSample(horizon) ? "sample" : "skip") << "\n"
            << "  Disk ray (depth=5): " << (shouldSample(disk) ? "sample" : "skip") << "\n"
            << "  Decisions correct: " << (decisionsOk ? "true" : "false") << "\n"
            << "  Status: " << (decisionsOk ? "PASS" : "FAIL") << "\n\n";

  return decisionsOk;
}

// Test 5: Bounds of the simplified magnetic-intensity fixture.
bool testIntensityBounds() {
  std::cout << "Test 5: Simplified Intensity Bounds\n";

  // Synchrotron power: P ~ B^2 * n * (E/E_c)^((p-1)/2) where p is spectral index
  // Simplified: intensity ~ B^2 * density

  float const b = 10.0f;  // Magnetic field (Gauss)
  float const rho = 0.1f; // Density (cgs)

  // Intensity proportional to B^2 * rho
  float const intensity = b * b * rho;

  // Bound the fixture intensity; the bound alone does not prove conservation.
  bool const conservationOk = (intensity > 0.0f && intensity < 1e6f);

  std::cout << "  B field: " << b << " Gauss\n"
            << "  Density: " << rho << " cgs\n"
            << "  Synchrotron intensity: " << intensity << "\n"
            << "  Intensity within fixture bounds: " << (conservationOk ? "true" : "false") << "\n"
            << "  Status: " << (conservationOk ? "PASS" : "FAIL") << "\n\n";

  return conservationOk;
}

// Test 6: Weighted blending of two synthetic intensity samples.
bool testWeightedBlend() {
  std::cout << "Test 6: Weighted Intensity Blend\n";

  float const rayColor = 0.5f;

  // GRMHD field contributes local synchrotron (not Doppler-dependent)
  float const grmhdColor = 0.3f;

  // A positive ray weight raises the result above the dimmer GRMHD sample.
  float const composite = (0.7f * rayColor) + (0.3f * grmhdColor);

  // Check: composite brightness > GRMHD alone
  bool const dopplerOk = (composite > grmhdColor);

  std::cout << "  Synthetic ray: " << rayColor << "\n"
            << "  GRMHD (local): " << grmhdColor << "\n"
            << "  Composite: " << composite << "\n"
            << "  Exceeds dimmer sample: " << (dopplerOk ? "true" : "false") << "\n"
            << "  Status: " << (dopplerOk ? "PASS" : "FAIL") << "\n\n";

  return dopplerOk;
}

// Test 7: CPU temporal interpolation feeding composite arithmetic.
bool testPipelineIntegration() {
  std::cout << "Test 7: CPU Temporal Interpolation and Composite Arithmetic\n";
  const std::array<double, 3> times{0.0, 1.0, 2.0};
  const std::array<double, 3> density{0.1, 0.3, 0.5};
  const auto metadata = physics::buildTimeseriesMetadata(times.data(), 3);
  const double interpolated = physics::interpolateField(metadata, density.data(), 0.5, false);
  const double composite = 0.7 * 0.5 + 0.3 * interpolated;
  // Density is linear in code time; the blend has an independent decimal oracle.
  const bool integrationOk = std::abs(interpolated - 0.2) < 1e-12 &&
                             std::abs(composite - 0.41) < 1e-12;
  std::cout << "  Interpolated density: " << interpolated << '\n'
            << "  Composite intensity: " << composite << '\n'
            << "  Status: " << (integrationOk ? "PASS" : "FAIL") << "\n\n";

  return integrationOk;
}

// ============================================================================
// Main Test Driver
// ============================================================================

} // namespace

int main() {
    std::cout << "\n====================================================\n"
              << "CPU GRMHD COMPOSITE FIXTURES\n"
              << "GPU rendering and physical conservation remain unqualified.\n"
              << "====================================================\n\n";

    int passed = 0;
    int const total = 7;

    if (testCompositeBlending()) {
      passed++;
    }
    if (testSynchrotronFraction()) {
      passed++;
    }
    if (testOutputBufferLayout()) {
      passed++;
    }
    if (testDepthBasedSampling()) {
      passed++;
    }
    if (testIntensityBounds()) {
      passed++;
    }
    if (testWeightedBlend()) {
      passed++;
    }
    if (testPipelineIntegration()) {
      passed++;
    }

    std::cout << "====================================================\n"
              << "RESULTS: " << passed << "/" << total << " tests passed\n"
              << "====================================================\n\n";

    return (passed == total) ? 0 : 1;
}
