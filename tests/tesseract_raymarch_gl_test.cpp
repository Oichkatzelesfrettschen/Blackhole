/**
 * @file tesseract_raymarch_gl_test.cpp
 * @brief Falsifiable capture-based checks that the tesseract scene reads as a
 *        dark void crossed by a thin lattice and dense, glowing strands.
 *
 * Acceptance checks of docs/plans/tesseract-interstellar-visuals.md against
 * the raw linear frame the tonemap reads: a void-dominated frame (lit
 * coverage inside a band, not the retired wireframe's near-empty frame and
 * not a filled beige corridor), strands as the brightest element (amber, over
 * the bloom threshold that beams stay under), and no speckle. Skips without a
 * GL 4.6 context.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <memory>
#include <numbers>
#include <string>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>
#include <gtest/gtest.h>

#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/vector_float3.hpp>

#include "render.h"
#include "render/render_state.h"
#include "render/tesseract/tesseract_renderer.h"
#include "shader.h"

using namespace gl;

namespace {

using blackhole::RenderState;
using blackhole::TesseractRecordFrame;

constexpr int WIDTH = 320;
constexpr int HEIGHT = 180;
// A pixel below this linear-HDR max channel reads as void, not lit lattice.
constexpr float COVERAGE_FLOOR = 0.02f;
// Void-dominated but not empty. Falsifiers: a filled cardboard corridor or
// wall reads above MAX_LIT_COVERAGE; the retired thin-line wireframe or a
// frame where strands vanished reads below MIN_LIT_COVERAGE.
constexpr float MIN_LIT_COVERAGE = 0.10f;
constexpr float MAX_LIT_COVERAGE = 0.45f;
// Beam shading is BEAM_COLOR * (0.03 + 0.22 lambert) in shader/tesseract.frag,
// at most 0.085 in linear HDR. The mean of the brightest 1% of pixels above
// BRIGHT_STRAND_FLOOR (over twice that ceiling) can only come from strands.
// Falsifier: strands dimmed to beam level, or beams promoted to emissive,
// pull the mean under the floor or make it hue-neutral.
constexpr float BRIGHT_STRAND_FLOOR = 0.2f;
constexpr float AMBER_HUE_LOW_DEG = 15.0f;
constexpr float AMBER_HUE_HIGH_DEG = 55.0f;
// Speckle: a pixel whose max channel departs from the median of its 8
// neighbors by more than this, in linear HDR, is an outlier. Sphere-trace
// misses inside a fiber and stray hits in the void both produce such
// pixels; smooth fiber edges and soft falloff do not at this resolution.
constexpr float OUTLIER_DELTA = 0.35f;
// Upper bound on the outlier fraction. Falsifier: a discontinuous SDF (a
// fract()-based shear) or an under-stepped march scatters isolated pixels
// well past this; the measured frame sits at 0.0002, so the bound has 25x margin.
constexpr float MAX_OUTLIER_FRACTION = 0.005f;

class TesseractRaymarchGlTest : public ::testing::Test {
protected:
  static void SetUpTestSuite() {
    if (glfwInit() == 0) {
      return;
    }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    window = glfwCreateWindow(64, 64, "Tesseract Raymarch", nullptr, nullptr);
    if (window == nullptr) {
      glfwTerminate();
      return;
    }
    glfwMakeContextCurrent(window);
    glbinding::initialize(glfwGetProcAddress);
    setShaderBaseDir(std::string(BH_SOURCE_DIR) + "/");
  }

  static void TearDownTestSuite() {
    if (window != nullptr) {
      glfwDestroyWindow(window);
      window = nullptr;
    }
    glfwTerminate();
  }

  void SetUp() override {
    if (window == nullptr) {
      GTEST_SKIP() << "no GL 4.6 context available (headless environment)";
    }
  }

  static GLFWwindow *window;
};

GLFWwindow *TesseractRaymarchGlTest::window = nullptr;

// Hue in degrees [0, 360) of a linear RGB color, the same formula
// tess::hueDegrees uses in src/render/tesseract/tesseract_geometry.cpp.
float hueDegreesOf(float r, float g, float b) {
  const float maxC = std::max({r, g, b});
  const float minC = std::min({r, g, b});
  const float delta = maxC - minC;
  if (delta <= 1e-6f) {
    return 0.0f;
  }
  float hue = 0.0f;
  if (maxC == r) {
    hue = 60.0f * std::fmod((g - b) / delta, 6.0f);
  } else if (maxC == g) {
    hue = 60.0f * (((b - r) / delta) + 2.0f);
  } else {
    hue = 60.0f * (((r - g) / delta) + 4.0f);
  }
  return hue < 0.0f ? hue + 360.0f : hue;
}

std::vector<float> renderDefaultScene() {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  const GLuint target = createColorTexture32f(WIDTH, HEIGHT);
  rs.targets.texBlackhole = target;
  rs.targets.renderWidth = WIDTH;
  rs.targets.renderHeight = HEIGHT;
  const glm::mat3 basis(glm::vec3(1.0f, 0.0f, 0.0f), glm::vec3(0.0f, 1.0f, 0.0f),
                        glm::vec3(0.0f, 0.0f, -1.0f));
  blackhole::renderTesseractScene(
      rs, basis, glm::vec3(0.0f, 0.0f, -1.0f), 0.0f,
      TesseractRecordFrame{.outputClockSeconds = 1.5, .camera = {.fovDeg = 45.0f}});
  std::vector<float> rgba(static_cast<std::size_t>(WIDTH) * HEIGHT * 4);
  glGetTextureImage(target, 0, GL_RGBA, GL_FLOAT, static_cast<GLsizei>(rgba.size() * sizeof(float)),
                    rgba.data());
  rs.tesseract.renderer.shutdown();
  glDeleteTextures(1, &target);
  return rgba;
}

float maxChannelAt(const std::vector<float> &rgba, std::size_t pixel) {
  return std::max({rgba.at(4 * pixel), rgba.at((4 * pixel) + 1), rgba.at((4 * pixel) + 2)});
}

TEST_F(TesseractRaymarchGlTest, VoidDominatedFrameWithStrandsAsTheBrightestElement) {
  const std::vector<float> rgba = renderDefaultScene();
  const std::size_t pixelCount = rgba.size() / 4;

  std::vector<float> maxChannels(pixelCount);
  std::size_t litCount = 0;
  for (std::size_t i = 0; i < pixelCount; ++i) {
    maxChannels.at(i) = maxChannelAt(rgba, i);
    litCount += maxChannels.at(i) > COVERAGE_FLOOR ? 1 : 0;
  }
  const float coverage = static_cast<float>(litCount) / static_cast<float>(pixelCount);
  std::printf("lit coverage %.3f of %zu pixels\n", static_cast<double>(coverage), pixelCount);
  EXPECT_GE(coverage, MIN_LIT_COVERAGE);
  EXPECT_LE(coverage, MAX_LIT_COVERAGE);

  // Brightest 1% of pixels: strand-colored (amber hue) and brighter than any
  // beam can be.
  std::vector<std::size_t> order(pixelCount);
  for (std::size_t i = 0; i < pixelCount; ++i) {
    order.at(i) = i;
  }
  const std::size_t topCount = pixelCount / 100;
  std::ranges::partial_sort(order, order.begin() + static_cast<std::ptrdiff_t>(topCount),
                            [&](std::size_t a, std::size_t b) {
                              return maxChannels.at(a) > maxChannels.at(b);
                            });
  double sinSum = 0.0;
  double cosSum = 0.0;
  double topMean = 0.0;
  for (std::size_t k = 0; k < topCount; ++k) {
    const std::size_t i = order.at(k);
    const double hueRad = static_cast<double>(hueDegreesOf(rgba.at(4 * i), rgba.at((4 * i) + 1),
                                                           rgba.at((4 * i) + 2))) *
                          (std::numbers::pi / 180.0);
    sinSum += std::sin(hueRad);
    cosSum += std::cos(hueRad);
    topMean += static_cast<double>(maxChannels.at(i));
  }
  topMean /= static_cast<double>(topCount);
  double meanHueDeg = std::atan2(sinSum, cosSum) * (180.0 / std::numbers::pi);
  if (meanHueDeg < 0.0) {
    meanHueDeg += 360.0;
  }
  std::printf("brightest 1%%: mean max channel %.3f, circular mean hue %.1f degrees\n", topMean,
              meanHueDeg);
  EXPECT_GT(topMean, static_cast<double>(BRIGHT_STRAND_FLOOR));
  EXPECT_GE(meanHueDeg, AMBER_HUE_LOW_DEG);
  EXPECT_LE(meanHueDeg, AMBER_HUE_HIGH_DEG);

  // Speckle: outliers against the median of the 8 neighbors.
  std::size_t outliers = 0;
  std::size_t interior = 0;
  for (int y = 1; y < HEIGHT - 1; ++y) {
    for (int x = 1; x < WIDTH - 1; ++x) {
      std::array<float, 8> around{};
      std::size_t n = 0;
      for (int dy = -1; dy <= 1; ++dy) {
        for (int dx = -1; dx <= 1; ++dx) {
          if (dx != 0 || dy != 0) {
            around.at(n++) = maxChannels.at((static_cast<std::size_t>(y + dy) * WIDTH) +
                                            static_cast<std::size_t>(x + dx));
          }
        }
      }
      std::ranges::nth_element(around, around.begin() + 4);
      const float median = around.at(4);
      const float value = maxChannels.at((static_cast<std::size_t>(y) * WIDTH) +
                                         static_cast<std::size_t>(x));
      ++interior;
      outliers += std::abs(value - median) > OUTLIER_DELTA ? 1 : 0;
    }
  }
  const float outlierFraction = static_cast<float>(outliers) / static_cast<float>(interior);
  std::printf("outlier fraction %.4f (%zu of %zu)\n", static_cast<double>(outlierFraction),
              outliers, interior);
  EXPECT_LE(outlierFraction, MAX_OUTLIER_FRACTION);
}

} // namespace
