/**
 * @file tesseract_raymarch_gl_test.cpp
 * @brief Falsifiable capture-based checks that the tesseract scene reads as a
 *        lit lattice, not the retired wireframe.
 *
 * Acceptance checks 1 and 2 of docs/plans/tesseract-interstellar-visuals.md:
 * a thin-line wireframe cannot cover much of the frame with lit pixels, and
 * its edge color was cool blue, not the new amber/gold palette. Skips without
 * a GL 4.6 context.
 */

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
// A pixel below this linear-HDR max channel reads as background/fog, not a
// lit lattice surface.
constexpr float COVERAGE_FLOOR = 0.02f;
// The plan's falsifier: a thin-line wireframe stays under this fraction.
constexpr float MIN_LIT_COVERAGE = 0.35f;
constexpr float AMBER_HUE_LOW_DEG = 25.0f;
constexpr float AMBER_HUE_HIGH_DEG = 50.0f;

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

TEST_F(TesseractRaymarchGlTest, LatticeCoversMostOfTheFrameAndReadsAmber) {
  const std::vector<float> rgba = renderDefaultScene();
  const std::size_t pixelCount = rgba.size() / 4;

  std::size_t litCount = 0;
  double sinSum = 0.0;
  double cosSum = 0.0;
  for (std::size_t i = 0; i < pixelCount; ++i) {
    const float r = rgba.at(4 * i);
    const float g = rgba.at((4 * i) + 1);
    const float b = rgba.at((4 * i) + 2);
    const float maxChannel = std::max({r, g, b});
    if (maxChannel <= COVERAGE_FLOOR) {
      continue;
    }
    ++litCount;
    const double hueRad = static_cast<double>(hueDegreesOf(r, g, b)) * (std::numbers::pi / 180.0);
    sinSum += std::sin(hueRad);
    cosSum += std::cos(hueRad);
  }

  const float coverage = static_cast<float>(litCount) / static_cast<float>(pixelCount);
  std::printf("lit coverage %.3f of %zu pixels\n", static_cast<double>(coverage), pixelCount);
  EXPECT_GT(coverage, MIN_LIT_COVERAGE);

  ASSERT_GT(litCount, std::size_t{0});
  double meanHueDeg = std::atan2(sinSum, cosSum) * (180.0 / std::numbers::pi);
  if (meanHueDeg < 0.0) {
    meanHueDeg += 360.0;
  }
  std::printf("circular mean hue %.1f degrees\n", static_cast<double>(meanHueDeg));
  EXPECT_GE(meanHueDeg, AMBER_HUE_LOW_DEG);
  EXPECT_LE(meanHueDeg, AMBER_HUE_HIGH_DEG);
}

} // namespace
