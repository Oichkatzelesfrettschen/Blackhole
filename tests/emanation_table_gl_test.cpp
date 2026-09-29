/**
 * @file emanation_table_gl_test.cpp
 * @brief The emanation texture the tesseract pass binds holds the CPU table.
 *
 * The pass bakes the N = 10 strutted emanation table of the selected strut
 * into an R16I texture (src/render/tesseract/emanation_table.h). Reading the
 * texture back must give the CPU table cell for cell, so the shader samples
 * the algebra and not an arbitrary mask: the filled-texel count equals the
 * DMZ count of the strut (259080 for a mandala strut, 87048 for S = 17), and
 * a strut change re-bakes. Skips without a GL 4.6 context.
 */

#include <cstddef>
#include <cstdint>
#include <string>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>
#include <gtest/gtest.h>

#include "render.h"
#include "render/tesseract/emanation_table.h"
#include "render/tesseract/tesseract_renderer.h"
#include "shader.h"

using namespace gl;

namespace {

using blackhole::TesseractFrameInputs;
using blackhole::TesseractRenderer;
namespace tess = blackhole::tesseract;

constexpr int TARGET_SIZE = 16;
constexpr int TABLE_SIZE = 510;

class EmanationTableGlTest : public ::testing::Test {
protected:
  static void SetUpTestSuite() {
    if (glfwInit() == 0) {
      return;
    }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    window = glfwCreateWindow(TARGET_SIZE, TARGET_SIZE, "Emanation Table", nullptr, nullptr);
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

GLFWwindow *EmanationTableGlTest::window = nullptr;

std::vector<std::int16_t> readTexture(GLuint texture) {
  std::vector<std::int16_t> texels(static_cast<std::size_t>(TABLE_SIZE) * TABLE_SIZE);
  glGetTextureImage(texture, 0, GL_RED_INTEGER, GL_SHORT,
                    static_cast<GLsizei>(texels.size() * sizeof(std::int16_t)), texels.data());
  return texels;
}

void expectTextureMatchesCpu(TesseractRenderer &renderer, GLuint target, int strut) {
  TesseractFrameInputs inputs;
  inputs.targetTexture = target;
  inputs.width = TARGET_SIZE;
  inputs.height = TARGET_SIZE;
  inputs.emanationStrut = strut;
  renderer.render(inputs);
  ASSERT_EQ(glGetError(), GL_NO_ERROR);
  ASSERT_EQ(renderer.emanationBakedStrut(), strut);
  ASSERT_NE(renderer.emanationTexture(), 0U);

  const tess::EmanationTable cpu = tess::createStruttedEt(tess::EMANATION_RENDER_LEVEL, strut);
  ASSERT_EQ(cpu.tone.k, TABLE_SIZE);
  const std::vector<std::int16_t> texels = readTexture(renderer.emanationTexture());
  std::size_t filled = 0;
  std::size_t mismatches = 0;
  for (std::size_t i = 0; i < texels.size(); ++i) {
    filled += texels[i] != 0 ? std::size_t{1} : std::size_t{0};
    mismatches += texels[i] != cpu.value[i] ? std::size_t{1} : std::size_t{0};
  }
  EXPECT_EQ(filled, cpu.dmzCount) << "S=" << strut;
  EXPECT_EQ(mismatches, 0U) << "S=" << strut;
  EXPECT_EQ(renderer.emanationDmzCount(), cpu.dmzCount) << "S=" << strut;
}

TEST_F(EmanationTableGlTest, BakedTextureHoldsTheCpuTableAcrossStrutChanges) {
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  {
    TesseractRenderer renderer;
    expectTextureMatchesCpu(renderer, target, 3);   // mandala: 259080 filled
    expectTextureMatchesCpu(renderer, target, 17);  // sky: 87048 filled
    expectTextureMatchesCpu(renderer, target, 129); // sky: 9096 filled
    EXPECT_EQ(renderer.emanationDmzCount(), 9096U);
    renderer.shutdown();
    EXPECT_EQ(renderer.emanationTexture(), 0U);
  }
  glDeleteTextures(1, &target);
}

} // namespace
