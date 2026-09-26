/**
 * @file tesseract_exposure_gl_test.cpp
 * @brief The tesseract record exposure maps the raw scene into display range.
 *
 * renderTesseractScene draws the default scene at the record framing into a
 * float target, the raw frame the tonemap reads before bloom. Over the ribbon
 * pixels (max channel above ten times the clear color) the 99th percentile of
 * the per-pixel max channel, times TESSERACT_RECORD_EXPOSURE, through the
 * tonemap's ACES curve and the showcase-orbit gamma, must land near 0.9, and
 * the clear color must stay near black. Skips without a GL 4.6 context.
 */

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <iterator>
#include <memory>
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
using blackhole::TESSERACT_RECORD_EXPOSURE;
using blackhole::TesseractRecordFrame;

// The record resolution the showcase-orbit capture settles at.
constexpr int RECORD_WIDTH = 1343;
constexpr int RECORD_HEIGHT = 1056;
// showcase-orbit's display gamma; cinematic's 2.25 maps the same raw value
// slightly higher.
constexpr float SHOWCASE_GAMMA = 2.35f;
// The pass's clear color max channel (tesseract_renderer.cpp).
constexpr float CLEAR_MAX_CHANNEL = 0.012f;

// Narkowicz ACES, as shader/tonemapping.frag applies it.
float aces(float x) {
  const float mapped = (x * ((2.51f * x) + 0.03f)) / ((x * ((2.43f * x) + 0.59f)) + 0.14f);
  return std::clamp(mapped, 0.0f, 1.0f);
}

float display(float raw) {
  return std::pow(aces(raw * TESSERACT_RECORD_EXPOSURE), 1.0f / SHOWCASE_GAMMA);
}

class TesseractExposureGlTest : public ::testing::Test {
protected:
  static void SetUpTestSuite() {
    if (glfwInit() == 0) {
      return;
    }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    window = glfwCreateWindow(64, 64, "Tesseract Exposure", nullptr, nullptr);
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

GLFWwindow *TesseractExposureGlTest::window = nullptr;

// Max channel of every pixel of the default scene recorded at @p seconds
// through a @p fovDeg lens looking down -z.
std::vector<float> rawMaxChannel(double seconds, float fovDeg) {
  const auto stateStorage = std::make_unique<RenderState>();
  RenderState &rs = *stateStorage;
  const GLuint target = createColorTexture32f(RECORD_WIDTH, RECORD_HEIGHT);
  rs.targets.texBlackhole = target;
  rs.targets.renderWidth = RECORD_WIDTH;
  rs.targets.renderHeight = RECORD_HEIGHT;
  const glm::mat3 basis(glm::vec3(1.0f, 0.0f, 0.0f), glm::vec3(0.0f, 1.0f, 0.0f),
                        glm::vec3(0.0f, 0.0f, -1.0f));
  blackhole::renderTesseractScene(
      rs, basis, glm::vec3(0.0f, 0.0f, -1.0f), 0.0f,
      TesseractRecordFrame{.outputClockSeconds = seconds, .camera = {.fovDeg = fovDeg}});
  std::vector<float> rgba(static_cast<std::size_t>(RECORD_WIDTH) * RECORD_HEIGHT * 4);
  glGetTextureImage(target, 0, GL_RGBA, GL_FLOAT, static_cast<GLsizei>(rgba.size() * sizeof(float)),
                    rgba.data());
  rs.tesseract.renderer.shutdown();
  glDeleteTextures(1, &target);
  std::vector<float> maxChannel(rgba.size() / 4);
  for (std::size_t i = 0; i < maxChannel.size(); ++i) {
    maxChannel.at(i) = std::max({rgba.at(4 * i), rgba.at((4 * i) + 1), rgba.at((4 * i) + 2)});
  }
  return maxChannel;
}

// 99th percentile of the ribbon pixels, those above ten times the clear color.
float ribbonP99(const std::vector<float> &maxChannel) {
  std::vector<float> ribbon;
  std::ranges::copy_if(maxChannel, std::back_inserter(ribbon),
                       [](float value) { return value > 10.0f * CLEAR_MAX_CHANNEL; });
  if (ribbon.empty()) {
    return 0.0f;
  }
  const auto rank = static_cast<std::ptrdiff_t>(0.99 * static_cast<double>(ribbon.size() - 1));
  std::ranges::nth_element(ribbon, ribbon.begin() + rank);
  return *(ribbon.begin() + rank);
}

TEST_F(TesseractExposureGlTest, RecordExposureMapsRibbonsNearNinetyPercent) {
  // Four moments of the default animation through the showcase above-disk and
  // cinematic lenses.
  for (const float fov : {20.0f, 40.0f}) {
    for (const double seconds : {0.0, 1.5, 3.0, 4.5}) {
      const float p99 = ribbonP99(rawMaxChannel(seconds, fov));
      std::printf("fov %.0f t %.1f raw ribbon p99 %.4f -> display %.3f\n", static_cast<double>(fov),
                  seconds, static_cast<double>(p99), static_cast<double>(display(p99)));
      EXPECT_GE(display(p99), 0.85f) << fov << " " << seconds;
      EXPECT_LE(display(p99), 0.95f) << fov << " " << seconds;
    }
  }
  // The clear color stays near black.
  std::printf("clear max channel %.4f -> display %.3f\n", static_cast<double>(CLEAR_MAX_CHANNEL),
              static_cast<double>(display(CLEAR_MAX_CHANNEL)));
  EXPECT_LT(display(CLEAR_MAX_CHANNEL), 0.06f);
}

} // namespace
