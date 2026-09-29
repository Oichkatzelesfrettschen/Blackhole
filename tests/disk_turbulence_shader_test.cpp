/**
 * @file disk_turbulence_shader_test.cpp
 * @brief Shipped disk_turbulence.glsl evaluated in a compute dispatch.
 *
 * bhDiskTurbulenceFactor multiplies the Page-Thorne disk emissivity, so its
 * mean over the disk must stay 1 for the azimuthally averaged flux to remain
 * the physical profile, and sigma = 0 must return exactly 1 for the smooth
 * disk the rendered-output oracles describe. The dispatch samples radii
 * log-uniformly from 6 M to 40 M, all azimuths, and coordinate times across
 * several winding periods. Falsifiers: a noise normalization off by the
 * measured standard deviation (the mean drifts by exp(sigma^2 (k^2 - 1) / 2)),
 * a cross-fade whose weights do not sum to 1 (the texture pulses in time), or
 * a sigma = 0 path that still evaluates the noise. Skips without GL 4.6.
 */

#include <cmath>
#include <cstddef>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <gtest/gtest.h>

#include "physics/safe_limits.h"
#include "support/gl_compute_harness.h"

using namespace gl;

namespace {

constexpr std::size_t K_SAMPLES = std::size_t{64} * std::size_t{256};
constexpr std::size_t K_STRIDE = 2;

const char *const K_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
#include "include/disk_turbulence.glsl"
void main() {
  uint i = gl_GlobalInvocationID.x;
  float u = fract(float(i) * 0.6180340);
  float v = fract(float(i) * 0.7548777);
  float w = fract(float(i) * 0.5698403);
  float rM = 6.0 * exp(v * log(40.0 / 6.0));
  float phi = 6.2831853 * u;
  float tM = 1000.0 * w;
  result[2 * i] = bhDiskTurbulenceFactor(rM, phi, 0.0, tM, 0.6);
  result[2 * i + 1] = bhDiskTurbulenceFactor(rM, phi, 0.0, tM, 0.0);
}
)";

class DiskTurbulenceShaderTest : public ::testing::Test {
protected:
  static bhtest::HiddenGlContext *context;
  static void SetUpTestSuite() { context = new bhtest::HiddenGlContext(); }
  static void TearDownTestSuite() {
    delete context;
    context = nullptr;
  }
  void SetUp() override {
    if (!context->available()) {
      GTEST_SKIP() << "no GL 4.6 context available (headless environment)";
    }
  }
};

bhtest::HiddenGlContext *DiskTurbulenceShaderTest::context = nullptr;

TEST_F(DiskTurbulenceShaderTest, MeanStaysOneAndZeroWidthIsExact) {
  const GLuint program = bhtest::createComputeProgram(K_SHADER);
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * K_STRIDE * K_SAMPLES), nullptr,
                    GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
  const std::vector<float> out =
      bhtest::runComputeProgram(program, ssbo, K_STRIDE * K_SAMPLES, K_SAMPLES / 64);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);

  double sum = 0.0;
  double sumSquares = 0.0;
  for (std::size_t i = 0; i < K_SAMPLES; ++i) {
    const auto factor = static_cast<double>(out.at(K_STRIDE * i));
    ASSERT_TRUE(physics::safeIsfinite(factor) && factor > 0.0) << "sample " << i;
    EXPECT_EQ(out.at((K_STRIDE * i) + 1), 1.0F) << "sigma 0 must leave the disk smooth";
    sum += factor;
    sumSquares += factor * factor;
  }
  const double mean = sum / static_cast<double>(K_SAMPLES);
  const double spread = std::sqrt((sumSquares / static_cast<double>(K_SAMPLES)) - (mean * mean));
  // The log-normal mean is 1; the replica measured 0.997 at sigma 0.6.
  EXPECT_NEAR(mean, 1.0, 0.05);
  // A log-normal with unit-variance exponent and sigma 0.6 has standard
  // deviation sqrt(exp(0.36) - 1) = 0.66; a texture that stopped varying
  // would fall far below the bound.
  EXPECT_GT(spread, 0.4);
  EXPECT_LT(spread, 1.0);
}

} // namespace
