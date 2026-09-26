/**
 * @file tesseract_ribbon_gl_test.cpp
 * @brief Tesseract ribbons carry the same radiance at any subdivision count.
 *
 * shader/tesseract.vert draws each segment as a screen-space quad summed with
 * GL_ONE, GL_ONE blending. Interior joints must butt, with a half-width cap
 * only at a polyline's true endpoints, or every joint of a subdivided edge
 * double-counts a square of radiance and the edge brightens with the
 * subdivision count. These cases draw one straight edge as 1 and as 12
 * pieces through the real shaders and compare the integrated radiance and the
 * brightest pixel. They skip without a GL 4.6 context (headless CI).
 */

#include <algorithm>
#include <array>
#include <cstddef>
#include <numeric>
#include <string>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/boolean.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>
#include <gtest/gtest.h>

#include <glm/ext/vector_float4.hpp>

#include "render.h"
#include "render/tesseract/tesseract_geometry.h"
#include "shader.h"

using namespace gl;

namespace {

namespace tess = blackhole::tesseract;

constexpr int TARGET_WIDTH = 256;
constexpr int TARGET_HEIGHT = 64;
constexpr float LINE_WIDTH_PX = 6.0f;
constexpr std::array<float, 16> IDENTITY_MATRIX = {1.0f, 0.0f, 0.0f, 0.0f, 0.0f, 1.0f, 0.0f, 0.0f,
                                                   0.0f, 0.0f, 1.0f, 0.0f, 0.0f, 0.0f, 0.0f, 1.0f};

class TesseractRibbonGlTest : public ::testing::Test {
protected:
  static bool glAvailable;
  static GLFWwindow *window;
  static GLuint program;

  static void SetUpTestSuite() {
    glAvailable = false;
    if (glfwInit() == 0) {
      return;
    }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    window = glfwCreateWindow(TARGET_WIDTH, TARGET_HEIGHT, "Tesseract Ribbon", nullptr, nullptr);
    if (window == nullptr) {
      glfwTerminate();
      return;
    }
    glfwMakeContextCurrent(window);
    glbinding::initialize(glfwGetProcAddress);
    setShaderBaseDir(std::string(BH_SOURCE_DIR) + "/");
    program = createShaderProgram(std::string("shader/tesseract.vert"),
                                  std::string("shader/tesseract.frag"));
    glAvailable = program != 0;
  }

  static void TearDownTestSuite() {
    if (program != 0) {
      glDeleteProgram(program);
      program = 0;
    }
    if (window != nullptr) {
      glfwDestroyWindow(window);
      window = nullptr;
    }
    glfwTerminate();
  }

  void SetUp() override {
    if (!glAvailable) {
      GTEST_SKIP() << "no GL 4.6 context available (headless environment)";
    }
  }

  // Red channel of the target after drawing @p segments as tesseract edges.
  static std::vector<float> drawRed(const std::vector<tess::SegmentInstance> &segments) {
    const GLuint target = createColorTexture32f(TARGET_WIDTH, TARGET_HEIGHT);
    const GLuint fbo = createFramebuffer({.colorTexture = target,
                                          .width = TARGET_WIDTH,
                                          .height = TARGET_HEIGHT,
                                          .createDepthBuffer = false});
    GLuint vao = 0;
    GLuint vbo = 0;
    glCreateVertexArrays(1, &vao);
    glCreateBuffers(1, &vbo);
    glNamedBufferData(vbo,
                      static_cast<GLsizeiptr>(segments.size() * sizeof(tess::SegmentInstance)),
                      segments.data(), GL_STATIC_DRAW);
    glVertexArrayVertexBuffer(vao, 0, vbo, 0,
                              static_cast<GLsizei>(sizeof(tess::SegmentInstance)));
    glVertexArrayBindingDivisor(vao, 0, 1);
    for (GLuint attrib = 0; attrib < 3; ++attrib) {
      glEnableVertexArrayAttrib(vao, attrib);
      glVertexArrayAttribFormat(vao, attrib, 4, GL_FLOAT, GL_FALSE,
                                attrib * static_cast<GLuint>(4 * sizeof(float)));
      glVertexArrayAttribBinding(vao, attrib, 0);
    }

    glBindFramebuffer(GL_FRAMEBUFFER, fbo);
    glViewport(0, 0, TARGET_WIDTH, TARGET_HEIGHT);
    glDisable(GL_DEPTH_TEST);
    glClearColor(0.0f, 0.0f, 0.0f, 0.0f);
    glClear(GL_COLOR_BUFFER_BIT);
    glEnable(GL_BLEND);
    glBlendEquationSeparate(GL_FUNC_ADD, GL_FUNC_ADD);
    glBlendFuncSeparate(GL_ONE, GL_ONE, GL_ZERO, GL_ONE);

    glUseProgram(program);
    const auto loc = [](const char *name) { return glGetUniformLocation(program, name); };
    glUniformMatrix4fv(loc("rotation4"), 1, GL_FALSE, IDENTITY_MATRIX.data());
    glUniformMatrix4fv(loc("viewProjection"), 1, GL_FALSE, IDENTITY_MATRIX.data());
    glUniform2f(loc("resolution"), static_cast<float>(TARGET_WIDTH),
                static_cast<float>(TARGET_HEIGHT));
    glUniform1i(loc("projectionMode"), 0);
    glUniform1f(loc("perspectiveDistance"), 3.0f);
    glUniform1f(loc("sceneScale"), 1.0f);
    glUniform1f(loc("timeSpan"), 10.0f);
    glUniform1f(loc("litMoment"), 0.0f);
    glUniform1f(loc("lineWidthPx"), LINE_WIDTH_PX);
    glUniform1f(loc("litWidth"), 0.5f);
    glUniform1f(loc("pulseTime"), 0.0f);
    glUniform1f(loc("pulseWidth"), 0.35f);
    glUniform1i(loc("pulseEnabled"), 0);
    glUniform1i(loc("pulseStrand"), 0);
    glUniform1f(loc("edgeIntensity"), 1.0f);
    glUniform1f(loc("strandIntensity"), 1.0f);
    glUniform1f(loc("sliceIntensity"), 1.0f);
    glBindVertexArray(vao);
    glDrawArraysInstanced(GL_TRIANGLES, 0, 6, static_cast<GLsizei>(segments.size()));
    glBindVertexArray(0);
    glUseProgram(0);
    glDisable(GL_BLEND);

    std::vector<float> rgba(static_cast<std::size_t>(TARGET_WIDTH * TARGET_HEIGHT * 4));
    glGetTextureImage(target, 0, GL_RGBA, GL_FLOAT, static_cast<GLsizei>(rgba.size() * sizeof(float)),
                      rgba.data());
    glBindFramebuffer(GL_FRAMEBUFFER, 0);
    glDeleteBuffers(1, &vbo);
    glDeleteVertexArrays(1, &vao);
    glDeleteFramebuffers(1, &fbo);
    glDeleteTextures(1, &target);

    std::vector<float> red(rgba.size() / 4);
    for (std::size_t i = 0; i < red.size(); ++i) {
      red.at(i) = rgba.at(4 * i);
    }
    return red;
  }
};

bool TesseractRibbonGlTest::glAvailable = false;
GLFWwindow *TesseractRibbonGlTest::window = nullptr;
GLuint TesseractRibbonGlTest::program = 0;

// One horizontal edge in clip space, cut into @p pieces with the tags
// buildSceneSegments gives a subdivided polyline. The y offset keeps the
// ribbon center off a pixel boundary.
std::vector<tess::SegmentInstance> straightEdge(std::size_t pieces) {
  const glm::vec4 a(-0.75f, 0.03f, 0.0f, 0.0f);
  const glm::vec4 b(0.75f, 0.03f, 0.0f, 0.0f);
  std::vector<tess::SegmentInstance> out;
  const auto steps = static_cast<float>(pieces);
  for (std::size_t k = 0; k < pieces; ++k) {
    tess::SegmentInstance seg;
    seg.a = a + ((b - a) * (static_cast<float>(k) / steps));
    seg.b = a + ((b - a) * (static_cast<float>(k + 1) / steps));
    seg.meta = glm::vec4(-1.0f, -1.0f,
                         tess::packSegmentTag(tess::SegmentKind::TesseractEdge, k == 0,
                                              k + 1 == pieces),
                         -1.0f);
    out.push_back(seg);
  }
  return out;
}

double total(const std::vector<float> &red) {
  return std::accumulate(red.begin(), red.end(), 0.0);
}

float peak(const std::vector<float> &red) {
  return *std::ranges::max_element(red);
}

TEST_F(TesseractRibbonGlTest, RadianceIsIndependentOfSubdivision) {
  const std::vector<float> whole = drawRed(straightEdge(1));
  const std::vector<float> split = drawRed(straightEdge(12));
  const double wholeTotal = total(whole);
  ASSERT_GT(wholeTotal, 0.0);
  EXPECT_NEAR(total(split) / wholeTotal, 1.0, 0.02);
}

TEST_F(TesseractRibbonGlTest, JointsAreNoBrighterThanTheLine) {
  const std::vector<float> whole = drawRed(straightEdge(1));
  const std::vector<float> split = drawRed(straightEdge(12));
  ASSERT_GT(peak(whole), 0.0f);
  EXPECT_LE(peak(split), peak(whole) * 1.02f);
}

} // namespace
