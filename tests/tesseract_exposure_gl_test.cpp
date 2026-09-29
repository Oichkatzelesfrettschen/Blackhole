/**
 * @file tesseract_exposure_gl_test.cpp
 * @brief The tesseract record exposure maps the raw scene into display range.
 *
 * renderTesseractScene draws the default scene at the record framing into a
 * float target, the raw frame the tonemap reads before bloom. The lattice
 * raymarch lights a large share of the frame with strands (unlike the retired
 * ribbon pass, which was mostly background), so the 99th percentile of every
 * pixel's max channel, times TESSERACT_RECORD_EXPOSURE, through the tonemap's
 * ACES curve and the showcase-orbit gamma, must land near 0.9. Skips without
 * a GL 4.6 context.
 */

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdio>
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

// A raymarch is far more expensive per pixel than the retired ribbon
// rasterization, so this measures at a smaller resolution than the
// showcase-orbit capture settles at; the statistic below does not depend on
// resolution.
constexpr int RECORD_WIDTH = 480;
constexpr int RECORD_HEIGHT = 270;
// showcase-orbit's display gamma; cinematic's 2.25 maps the same raw value
// slightly higher.
constexpr float SHOWCASE_GAMMA = 2.35f;

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

// 99th percentile max channel over every pixel: the lattice raymarch lights a
// large share of the frame, so unlike the retired ribbon pass this
// needs no background filter.
float scenePercentile99(std::vector<float> maxChannel) {
  const auto rank = static_cast<std::ptrdiff_t>(0.99 * static_cast<double>(maxChannel.size() - 1));
  std::ranges::nth_element(maxChannel, maxChannel.begin() + rank);
  return *(maxChannel.begin() + rank);
}

TEST_F(TesseractExposureGlTest, RecordExposureMapsTheLatticeNearNinetyPercent) {
  // Four moments of the default animation through the showcase above-disk and
  // cinematic lenses. Unlike the retired ribbon pass's small, camera-position-
  // independent object, this pass shows a local neighborhood of an endless
  // corridor: whether the narrow now/pulse highlight band falls near the
  // camera varies with drift and rotation, so a single sample's display value
  // ranges further than the old ribbon pass did. The exposure is calibrated
  // against the median over these samples, and every sample still needs to
  // land in a usable (neither crushed nor clipped) display range.
  std::vector<float> displays;
  for (const float fov : {20.0f, 40.0f}) {
    for (const double seconds : {0.0, 1.5, 3.0, 4.5}) {
      const float p99 = scenePercentile99(rawMaxChannel(seconds, fov));
      const float shown = display(p99);
      std::printf("fov %.0f t %.1f raw p99 %.4f -> display %.3f\n", static_cast<double>(fov),
                  seconds, static_cast<double>(p99), static_cast<double>(shown));
      EXPECT_GE(shown, 0.10f) << fov << " " << seconds;
      EXPECT_LE(shown, 0.99f) << fov << " " << seconds;
      displays.push_back(shown);
    }
  }
  const auto midpoint = static_cast<std::ptrdiff_t>(displays.size() / 2);
  std::ranges::nth_element(displays, displays.begin() + midpoint);
  const float median = *(displays.begin() + midpoint);
  std::printf("median display %.3f\n", static_cast<double>(median));
  EXPECT_GE(median, 0.80f);
  EXPECT_LE(median, 0.97f);
}

} // namespace
