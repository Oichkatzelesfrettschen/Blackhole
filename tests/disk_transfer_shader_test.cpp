/**
 * @file disk_transfer_shader_test.cpp
 * @brief Shipped disk_transfer.glsl against the double-precision C++.
 *
 * A compute dispatch evaluates dtPageThorneShape, dtDiskTransferG and
 * dtBlackbodyChroma from shader/include/disk_transfer.glsl over a grid of
 * spins (including a retrograde disk), radii from 1.1 to 20 r_isco, photon
 * lambda of 0 and +-0.8 r, and three temperatures. Each result must match
 * physics::pageThorneFluxShape, physics::diskTransferG and
 * physics::blackbodyChromaLinearSrgb evaluated at the shader's own float
 * radius. Falsifiers: a transcription slip in a root coefficient, a wrong
 * sign of a in u^t or Omega, or a swapped sRGB matrix row.
 * Skips without a GL 4.6 context.
 */

#include <array>
#include <cmath>
#include <cstddef>
#include <vector>

#include <gtest/gtest.h>

#include "physics/disk_transfer.h"
#include "physics/page_thorne.h"
#include "support/gl_compute_harness.h"

using namespace gl;

namespace {

constexpr int K_CASES = 60; // 5 spins x 4 radii x 3 lambdas
constexpr int K_STRIDE = 6;
constexpr std::array<float, 5> K_SPINS = {0.0F, 0.5F, 0.9F, 0.998F, -0.5F};
constexpr std::array<float, 3> K_TEMPERATURES = {3000.0F, 6500.0F, 12000.0F};

const char *const K_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
#include "include/disk_transfer.glsl"
const float SPINS[5] = float[5](0.0, 0.5, 0.9, 0.998, -0.5);
const float RATIOS[4] = float[4](1.1, 1.6, 4.0, 20.0);
const float LAMBDAS[3] = float[3](0.0, 0.8, -0.8);
const float TEMPS[3] = float[3](3000.0, 6500.0, 12000.0);
void main() {
  int i = int(gl_GlobalInvocationID.x);
  if (i >= 60) {
    return;
  }
  float a = SPINS[i / 12];
  float r = RATIOS[(i / 3) % 4] * isco_radius(a);
  float lambda = LAMBDAS[i % 3] * r;
  vec3 chroma = dtBlackbodyChroma(TEMPS[i % 3]);
  result[6 * i + 0] = r;
  result[6 * i + 1] = dtPageThorneShape(r, a);
  result[6 * i + 2] = dtDiskTransferG(r, a, lambda);
  result[6 * i + 3] = chroma.r;
  result[6 * i + 4] = chroma.g;
  result[6 * i + 5] = chroma.b;
}
)";

class DiskTransferShaderTest : public ::testing::Test {
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

bhtest::HiddenGlContext *DiskTransferShaderTest::context = nullptr;

TEST_F(DiskTransferShaderTest, MatchesDoublePrecisionReference) {
  const GLuint program = bhtest::createComputeProgram(K_SHADER);
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * K_STRIDE * K_CASES), nullptr,
                    GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
  const std::vector<float> out =
      bhtest::runComputeProgram(program, ssbo, static_cast<std::size_t>(K_STRIDE * K_CASES), 1);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);

  constexpr std::array<double, 3> K_LAMBDAS = {0.0, 0.8, -0.8};
  for (int i = 0; i < K_CASES; ++i) {
    const auto at = [&](int k) {
      return static_cast<double>(out[static_cast<std::size_t>((K_STRIDE * i) + k)]);
    };
    const double a = static_cast<double>(K_SPINS.at(static_cast<std::size_t>(i / 12)));
    const double r = at(0);
    const double lambda = K_LAMBDAS.at(static_cast<std::size_t>(i % 3)) * r;

    // Float cancellation in the logarithmic bracket grows toward the
    // zero-torque edge; 1.1 r_isco is the closest radius sampled.
    const double shape = physics::pageThorneFluxShape(r, a);
    EXPECT_NEAR(at(1) / shape, 1.0, 2e-3) << "a=" << a << " r=" << r;

    const double g = physics::diskTransferG(r, a, lambda);
    EXPECT_NEAR(at(2) / g, 1.0, 1e-5) << "a=" << a << " r=" << r << " lambda=" << lambda;

    const std::array<double, 3> rgb = physics::blackbodyChromaLinearSrgb(
        static_cast<double>(K_TEMPERATURES.at(static_cast<std::size_t>(i % 3))));
    for (int c = 0; c < 3; ++c) {
      EXPECT_NEAR(at(3 + c), rgb.at(static_cast<std::size_t>(c)), 1e-4) << "channel " << c;
    }
  }
}

} // namespace
