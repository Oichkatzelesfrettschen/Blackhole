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
 * brightest pixel. A segment crossing the near plane must draw its visible
 * part, as the same segment pre-clipped on the CPU does. They skip without a
 * GL 4.6 context (headless CI).
 */

#include <algorithm>
#include <array>
#include <cmath>
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

#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/gtc/type_ptr.hpp>
#include <glm/trigonometric.hpp>

#include "render.h"
#include "render/tesseract/tesseract_geometry.h"
#include "shader.h"

using namespace gl;

namespace {

namespace tess = blackhole::tesseract;

constexpr int TARGET_WIDTH = 256;
constexpr int TARGET_HEIGHT = 64;
constexpr float LINE_WIDTH_PX = 6.0f;
// Red radiance of one edge ribbon on its centerline: tesseract.frag
// EDGE_COLOR.r at edgeIntensity 1, where the across profile peaks at 1.
constexpr float EDGE_PEAK_RED = 0.35f;
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

  // Red channel of the target after drawing @p segments as tesseract edges
  // through @p viewProjection.
  static std::vector<float> drawRed(const std::vector<tess::SegmentInstance> &segments,
                                    const glm::mat4 &viewProjection = glm::mat4(1.0f)) {
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
    for (GLuint attrib = 0; attrib < tess::SEGMENT_INSTANCE_ATTRIBUTES; ++attrib) {
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
    glUniformMatrix4fv(loc("viewProjection"), 1, GL_FALSE, glm::value_ptr(viewProjection));
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

// Edge segments through @p points with the tags and neighbors
// buildSceneSegments gives a polyline: caps at the two ends, and each
// segment's prev and next the points beyond its own.
std::vector<tess::SegmentInstance> polyline(const std::vector<glm::vec4> &points) {
  std::vector<tess::SegmentInstance> out;
  for (std::size_t k = 0; k + 1 < points.size(); ++k) {
    const bool first = k == 0;
    const bool last = k + 2 == points.size();
    tess::SegmentInstance seg;
    seg.a = points.at(k);
    seg.b = points.at(k + 1);
    seg.prev = first ? seg.a : points.at(k - 1);
    seg.next = last ? seg.b : points.at(k + 2);
    seg.meta = glm::vec4(
        -1.0f, -1.0f, tess::packSegmentTag(tess::SegmentKind::TesseractEdge, first, last), -1.0f);
    out.push_back(seg);
  }
  return out;
}

// One horizontal edge in clip space, cut into @p pieces. The y offset keeps
// the ribbon center off a pixel boundary.
std::vector<tess::SegmentInstance> straightEdge(std::size_t pieces) {
  const glm::vec4 a(-0.75f, 0.03f, 0.0f, 0.0f);
  const glm::vec4 b(0.75f, 0.03f, 0.0f, 0.0f);
  std::vector<glm::vec4> points;
  const auto steps = static_cast<float>(pieces);
  for (std::size_t k = 0; k <= pieces; ++k) {
    points.push_back(a + ((b - a) * (static_cast<float>(k) / steps)));
  }
  return polyline(points);
}

constexpr float ARC_RADIUS_PX = 60.0f;
constexpr float ARC_CENTER_Y_PX = -40.0f;
constexpr float ARC_START_DEG = 30.0f;
constexpr float ARC_SPAN_DEG = 120.0f;
// Pieces of the arc whose 40-degree bends the gap check probes.
constexpr std::size_t BENT_PIECES = 3;

// Angle in radians of point @p k of an arc cut into @p pieces.
float arcAngle(std::size_t k, std::size_t pieces) {
  return glm::radians(ARC_START_DEG +
                      (ARC_SPAN_DEG * static_cast<float>(k) / static_cast<float>(pieces)));
}

// A 120-degree arc of radius 60 px about (0, -40) px, cut into @p pieces,
// in clip coordinates of the TARGET_WIDTH x TARGET_HEIGHT target.
std::vector<tess::SegmentInstance> arc(std::size_t pieces) {
  const float halfWidthPx = 0.5f * static_cast<float>(TARGET_WIDTH);
  const float halfHeightPx = 0.5f * static_cast<float>(TARGET_HEIGHT);
  std::vector<glm::vec4> points;
  for (std::size_t k = 0; k <= pieces; ++k) {
    const float angle = arcAngle(k, pieces);
    points.emplace_back(ARC_RADIUS_PX * std::cos(angle) / halfWidthPx,
                        (ARC_CENTER_Y_PX + (ARC_RADIUS_PX * std::sin(angle))) / halfHeightPx, 0.0f,
                        0.0f);
  }
  return polyline(points);
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

// A curved run joins its pieces on shared miters: the inside of each bend is
// covered once, not twice, and the radiance per unit length matches a
// straight edge whatever the subdivision count.
TEST_F(TesseractRibbonGlTest, CurvedRunsJoinWithoutOverlapOrGaps) {
  const std::vector<float> coarse = drawRed(arc(6));
  const std::vector<float> fine = drawRed(arc(24));
  // One ribbon peaks at EDGE_PEAK_RED on its centerline; a doubly covered
  // pixel reads up to twice that.
  EXPECT_LE(peak(coarse), EDGE_PEAK_RED * 1.001f);
  EXPECT_LE(peak(fine), EDGE_PEAK_RED * 1.001f);
  // Chord lengths of the two tessellations differ by 0.5%.
  EXPECT_NEAR(total(coarse) / total(fine), 1.0, 0.02);

  // Outside each 40-degree bend of a 3-piece arc, 0.8 half widths from the
  // centerline, butt joints leave a wedge about 1.7 px wide uncovered; the
  // miter covers it.
  const std::vector<float> bent = drawRed(arc(BENT_PIECES));
  const float outward = ARC_RADIUS_PX + (0.8f * 0.5f * LINE_WIDTH_PX);
  for (std::size_t k = 1; k < BENT_PIECES; ++k) {
    const float angle = arcAngle(k, BENT_PIECES);
    const auto column = static_cast<int>(
        std::floor((outward * std::cos(angle)) + (0.5f * static_cast<float>(TARGET_WIDTH))));
    const auto row = static_cast<int>(std::floor(ARC_CENTER_Y_PX + (outward * std::sin(angle)) +
                                                 (0.5f * static_cast<float>(TARGET_HEIGHT))));
    const std::size_t index =
        (static_cast<std::size_t>(row) * TARGET_WIDTH) + static_cast<std::size_t>(column);
    EXPECT_GT(bent.at(index), 0.0f) << "joint " << k;
  }
}

// Near plane of eyeAtOrigin, the TESSERACT_NEAR_PLANE value.
constexpr float EYE_NEAR_PLANE = 0.05f;

// An eye at the origin looking down -z through an infinite-far perspective,
// as tesseractViewProjection builds it.
glm::mat4 eyeAtOrigin() {
  const float aspect = static_cast<float>(TARGET_WIDTH) / static_cast<float>(TARGET_HEIGHT);
  return glm::infinitePerspective(glm::radians(60.0f), aspect, EYE_NEAR_PLANE) *
         glm::lookAt(glm::vec3(0.0f), glm::vec3(0.0f, 0.0f, -1.0f), glm::vec3(0.0f, 1.0f, 0.0f));
}

// One uncapped edge segment from @p a to @p b, with no neighbors.
std::vector<tess::SegmentInstance> segment(const glm::vec4 &a, const glm::vec4 &b) {
  tess::SegmentInstance seg;
  seg.a = a;
  seg.b = b;
  seg.prev = a;
  seg.next = b;
  seg.meta = glm::vec4(-1.0f, -1.0f,
                       tess::packSegmentTag(tess::SegmentKind::TesseractEdge, false, false), -1.0f);
  return {seg};
}

TEST_F(TesseractRibbonGlTest, SegmentsCrossingTheNearPlaneKeepTheirVisiblePart) {
  // From behind the eye (z = +0.5) to well in front (z = -4); the near plane
  // at z = -0.05 cuts it at s = 0.55 / 4.5.
  const glm::vec4 behind(0.1f, 0.02f, 0.5f, 0.0f);
  const glm::vec4 ahead(0.1f, 0.02f, -4.0f, 0.0f);
  const float cut = 0.55f / 4.5f;
  const std::vector<float> crossing = drawRed(segment(behind, ahead), eyeAtOrigin());
  const std::vector<float> preclipped =
      drawRed(segment(behind + ((ahead - behind) * (cut + 1e-4f)), ahead), eyeAtOrigin());
  const double reference = total(preclipped);
  ASSERT_GT(reference, 0.0);
  EXPECT_NEAR(total(crossing) / reference, 1.0, 0.02);
  // A segment wholly behind the eye draws nothing.
  EXPECT_EQ(total(drawRed(segment(behind, glm::vec4(0.1f, 0.02f, 2.0f, 0.0f)), eyeAtOrigin())),
            0.0);
}

} // namespace
