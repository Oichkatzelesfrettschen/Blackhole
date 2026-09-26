/**
 * @file tesseract_gl_state_test.cpp
 * @brief GL state hygiene between the tesseract scene and the black-hole passes.
 *
 * The speculative label draws through HudOverlay, which alpha-blends; the
 * fullscreen black-hole pass writes depth into alpha. A leaked GL_BLEND
 * multiplied the black-hole RGB by that depth on every frame after a
 * tesseract frame. These tests pin the three guards: HudOverlay restores the
 * blend and depth state it found, renderToTexture writes its fragment output
 * verbatim whatever blend state it inherits, and the tesseract pass restores
 * every binding it touches. They also exercise the tesseract hot-reload
 * recompile. Tests skip without a GL 4.6 context (headless CI).
 */

#include <array>
#include <cstddef>
#include <filesystem>
#include <fstream>
#include <string>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/boolean.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>
#include <gtest/gtest.h>

#include <glm/ext/vector_float4.hpp>

#include "hud_overlay.h"
#include "render.h"
#include "render/tesseract/tesseract_renderer.h"
#include "shader.h"

using namespace gl;

namespace {

constexpr int TARGET_SIZE = 16;

class TesseractGlStateTest : public ::testing::Test {
protected:
  static bool glAvailable;

  static void SetUpTestSuite() {
    glAvailable = false;
    if (glfwInit() == 0) {
      return;
    }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    window = glfwCreateWindow(TARGET_SIZE, TARGET_SIZE, "Tesseract GL State", nullptr, nullptr);
    if (window == nullptr) {
      glfwTerminate();
      return;
    }
    glfwMakeContextCurrent(window);
    glbinding::initialize(glfwGetProcAddress);
    setShaderBaseDir(std::string(BH_SOURCE_DIR) + "/");
    glAvailable = true;
  }

  static void TearDownTestSuite() {
    if (window != nullptr) {
      clearRenderToTextureCache();
      glfwDestroyWindow(window);
      window = nullptr;
    }
    glfwTerminate();
  }

  void SetUp() override {
    if (!glAvailable) {
      GTEST_SKIP() << "no GL 4.6 context available (headless environment)";
    }
    glDisable(GL_BLEND);
    glBlendFuncSeparate(GL_ONE, GL_ZERO, GL_ONE, GL_ZERO);
    glBlendEquationSeparate(GL_FUNC_ADD, GL_FUNC_ADD);
    glDisable(GL_DEPTH_TEST);
  }

  static std::array<float, 4> readFirstTexel(GLuint texture) {
    std::vector<float> pixels(static_cast<std::size_t>(TARGET_SIZE * TARGET_SIZE * 4));
    glGetTextureImage(texture, 0, GL_RGBA, GL_FLOAT,
                      static_cast<GLsizei>(pixels.size() * sizeof(float)), pixels.data());
    return {pixels.at(0), pixels.at(1), pixels.at(2), pixels.at(3)};
  }

  static GLFWwindow *window;
};

bool TesseractGlStateTest::glAvailable = false;
GLFWwindow *TesseractGlStateTest::window = nullptr;

GLint integerState(GLenum name) {
  GLint value = 0;
  glGetIntegerv(name, &value);
  return value;
}

TEST_F(TesseractGlStateTest, HudOverlayRestoresDisabledBlend) {
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  const GLuint fbo = createFramebuffer({.colorTexture = target,
                                        .width = TARGET_SIZE,
                                        .height = TARGET_SIZE,
                                        .createDepthBuffer = false});
  glBindFramebuffer(GL_FRAMEBUFFER, fbo);
  HudOverlay overlay;
  overlay.setLines({HudOverlayLine{.text = "SPECULATIVE", .color = glm::vec4(1.0f)}});
  overlay.render(TARGET_SIZE, TARGET_SIZE);
  EXPECT_EQ(glIsEnabled(GL_BLEND), GL_FALSE);
  EXPECT_EQ(glIsEnabled(GL_DEPTH_TEST), GL_FALSE);
  overlay.shutdown();
  glBindFramebuffer(GL_FRAMEBUFFER, 0);
  glDeleteFramebuffers(1, &fbo);
  glDeleteTextures(1, &target);
}

TEST_F(TesseractGlStateTest, HudOverlayRestoresEnabledBlendFunction) {
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  const GLuint fbo = createFramebuffer({.colorTexture = target,
                                        .width = TARGET_SIZE,
                                        .height = TARGET_SIZE,
                                        .createDepthBuffer = false});
  glBindFramebuffer(GL_FRAMEBUFFER, fbo);
  glEnable(GL_BLEND);
  glEnable(GL_DEPTH_TEST);
  glBlendFuncSeparate(GL_ONE, GL_ONE, GL_ZERO, GL_ONE);
  HudOverlay overlay;
  overlay.setLines({HudOverlayLine{.text = "SPECULATIVE", .color = glm::vec4(1.0f)}});
  overlay.render(TARGET_SIZE, TARGET_SIZE);
  EXPECT_EQ(glIsEnabled(GL_BLEND), GL_TRUE);
  EXPECT_EQ(glIsEnabled(GL_DEPTH_TEST), GL_TRUE);
  EXPECT_EQ(integerState(GL_BLEND_SRC_RGB), static_cast<GLint>(GL_ONE));
  EXPECT_EQ(integerState(GL_BLEND_DST_RGB), static_cast<GLint>(GL_ONE));
  EXPECT_EQ(integerState(GL_BLEND_SRC_ALPHA), static_cast<GLint>(GL_ZERO));
  EXPECT_EQ(integerState(GL_BLEND_DST_ALPHA), static_cast<GLint>(GL_ONE));
  overlay.shutdown();
  glBindFramebuffer(GL_FRAMEBUFFER, 0);
  glDeleteFramebuffers(1, &fbo);
  glDeleteTextures(1, &target);
}

TEST_F(TesseractGlStateTest, RenderToTextureWritesAlphaDataVerbatimUnderInheritedBlend) {
  // A fullscreen pass whose alpha carries data, as blackhole_main.frag's
  // depth does. With a leaked SRC_ALPHA blend the RGB would read 0.5x.
  const std::filesystem::path frag =
      std::filesystem::path(BH_BINARY_DIR) / "tesseract_gl_state_alpha_data.frag";
  {
    std::ofstream out(frag);
    out << "#version 460 core\n"
           "out vec4 fragColor;\n"
           "void main() { fragColor = vec4(0.8, 0.4, 0.2, 0.5); }\n";
  }
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  glEnable(GL_BLEND);
  glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);
  RenderToTextureInfo rtti;
  rtti.fragShader = frag.string();
  rtti.targetTexture = target;
  rtti.width = TARGET_SIZE;
  rtti.height = TARGET_SIZE;
  renderToTexture(rtti);
  const std::array<float, 4> texel = readFirstTexel(target);
  EXPECT_FLOAT_EQ(texel.at(0), 0.8f);
  EXPECT_FLOAT_EQ(texel.at(1), 0.4f);
  EXPECT_FLOAT_EQ(texel.at(2), 0.2f);
  EXPECT_FLOAT_EQ(texel.at(3), 0.5f);
  glDeleteTextures(1, &target);
  std::filesystem::remove(frag);
}

TEST_F(TesseractGlStateTest, TesseractPassRestoresEveryBindingItTouches) {
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  const GLuint sentinelTexture = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  const GLuint drawFbo = createFramebuffer({.colorTexture = sentinelTexture,
                                            .width = TARGET_SIZE,
                                            .height = TARGET_SIZE,
                                            .createDepthBuffer = false});
  GLuint vao = 0;
  glCreateVertexArrays(1, &vao);
  glBindFramebuffer(GL_DRAW_FRAMEBUFFER, drawFbo);
  glBindFramebuffer(GL_READ_FRAMEBUFFER, 0);
  glBindVertexArray(vao);
  glViewport(1, 2, 3, 4);
  glEnable(GL_DEPTH_TEST);

  blackhole::TesseractRenderer renderer;
  blackhole::TesseractFrameInputs inputs;
  inputs.targetTexture = target;
  inputs.width = TARGET_SIZE;
  inputs.height = TARGET_SIZE;
  inputs.rotation = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1};
  renderer.render(inputs);

  EXPECT_EQ(glIsEnabled(GL_BLEND), GL_FALSE);
  EXPECT_EQ(glIsEnabled(GL_DEPTH_TEST), GL_TRUE);
  EXPECT_EQ(integerState(GL_DRAW_FRAMEBUFFER_BINDING), static_cast<GLint>(drawFbo));
  EXPECT_EQ(integerState(GL_READ_FRAMEBUFFER_BINDING), 0);
  EXPECT_EQ(integerState(GL_VERTEX_ARRAY_BINDING), static_cast<GLint>(vao));
  EXPECT_EQ(integerState(GL_CURRENT_PROGRAM), 0);
  std::array<GLint, 4> viewport{};
  glGetIntegerv(GL_VIEWPORT, viewport.data());
  EXPECT_EQ(viewport, (std::array<GLint, 4>{1, 2, 3, 4}));
  // The clear color's alpha 1 survives the additive ribbons.
  EXPECT_FLOAT_EQ(readFirstTexel(target).at(3), 1.0f);
  EXPECT_EQ(glGetError(), GL_NO_ERROR);

  renderer.shutdown();
  glBindVertexArray(0);
  glBindFramebuffer(GL_FRAMEBUFFER, 0);
  glDeleteVertexArrays(1, &vao);
  glDeleteFramebuffers(1, &drawFbo);
  glDeleteTextures(1, &sentinelTexture);
  glDeleteTextures(1, &target);
}

TEST_F(TesseractGlStateTest, ReloadShadersRecompilesTheLiveProgram) {
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  blackhole::TesseractRenderer renderer;
  // Before the first draw there is no program to replace.
  EXPECT_TRUE(renderer.reloadShaders());
  blackhole::TesseractFrameInputs inputs;
  inputs.targetTexture = target;
  inputs.width = TARGET_SIZE;
  inputs.height = TARGET_SIZE;
  inputs.rotation = {1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1};
  renderer.render(inputs);
  EXPECT_TRUE(renderer.reloadShaders());
  renderer.render(inputs);
  EXPECT_EQ(glGetError(), GL_NO_ERROR);
  renderer.shutdown();
  glDeleteTextures(1, &target);
}

} // namespace
