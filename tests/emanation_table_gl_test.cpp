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

#include <array>
#include <chrono>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <iterator>
#include <string>
#include <thread>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/bitfield.h>
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
  inputs.emanationBakeBlocking = true;
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

// Text of tesseract_panes.frag between "// <name>-begin" and "// <name>-end".
std::string shaderSection(const std::string &source, const std::string &name) {
  const std::string begin = "// " + name + "-begin\n";
  const std::size_t start = source.find(begin);
  const std::size_t end = source.find("// " + name + "-end");
  if (start == std::string::npos || end == std::string::npos || end < start) {
    return {};
  }
  return source.substr(start + begin.size(), end - start - begin.size());
}

struct MapQuery {
  std::int32_t level;
  std::int32_t index; ///< Index in the level-@c level table.
  std::int32_t cell;  ///< Level-10 cell whose display coordinate is asked for.
  float fold;
  float display; ///< Display coordinate the fold position is evaluated at.
  float unused0;
  float unused1;
  float unused2;
};

struct MapAnswer {
  std::int32_t expanded;
  float foldPosition;
  float displayPosition; ///< Of the expanded index.
  float cellDisplay;     ///< Of MapQuery::cell.
};

// Runs the shader's own index maps (the sections of tesseract_panes.frag between the
// emanation-map and emanation-display markers) in a compute shader over
// @p queries, so the GPU code is compared with the CPU model of the table.
std::vector<MapAnswer> runShaderMaps(const std::vector<MapQuery> &queries) {
  std::ifstream file(std::string(BH_SOURCE_DIR) + "/shader/tesseract_panes.frag");
  const std::string source((std::istreambuf_iterator<char>(file)),
                           std::istreambuf_iterator<char>());
  const std::string maps = shaderSection(source, "emanation-map");
  const std::string display = shaderSection(source, "emanation-display");
  EXPECT_FALSE(maps.empty());
  EXPECT_FALSE(display.empty());
  const std::string kernel =
      "#version 460\nconst int EMANATION_TOP_LEVEL = 10;\n" + maps + display + R"(
struct Query { int level; int index; int cell; float fold; float display; float u0; float u1; float u2; };
struct Answer { int expanded; float foldPosition; float displayPosition; float cellDisplay; };
layout(std430, binding = 0) readonly buffer Queries { Query queries[]; };
layout(std430, binding = 1) writeonly buffer Answers { Answer answers[]; };
layout(local_size_x = 64) in;
void main() {
  uint i = gl_GlobalInvocationID.x;
  if (i >= uint(queries.length())) {
    return;
  }
  Query q = queries[i];
  Answer a;
  a.expanded = emanationExpand(q.index, q.level);
  a.foldPosition = emanationFoldPosition(q.display, q.level, q.fold);
  a.displayPosition = emanationDisplayPosition(a.expanded, q.level, q.fold);
  a.cellDisplay = emanationDisplayPosition(q.cell, q.level, q.fold);
  answers[i] = a;
}
)";
  const GLuint shader = glCreateShader(GL_COMPUTE_SHADER);
  const char *text = kernel.c_str();
  glShaderSource(shader, 1, &text, nullptr);
  glCompileShader(shader);
  GLint compiled = 0;
  glGetShaderiv(shader, GL_COMPILE_STATUS, &compiled);
  if (compiled == 0) {
    std::vector<char> log(4096);
    glGetShaderInfoLog(shader, static_cast<GLsizei>(log.size()), nullptr, log.data());
    ADD_FAILURE() << "compute shader failed to compile: " << log.data();
    glDeleteShader(shader);
    return {};
  }
  const GLuint program = glCreateProgram();
  glAttachShader(program, shader);
  glLinkProgram(program);
  std::array<GLuint, 2> buffers{};
  glCreateBuffers(2, buffers.data());
  glNamedBufferData(buffers[0], static_cast<GLsizeiptr>(queries.size() * sizeof(MapQuery)),
                    queries.data(), GL_STATIC_DRAW);
  glNamedBufferData(buffers[1], static_cast<GLsizeiptr>(queries.size() * sizeof(MapAnswer)),
                    nullptr, GL_DYNAMIC_READ);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, buffers[0]);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, buffers[1]);
  glUseProgram(program);
  glDispatchCompute(static_cast<GLuint>((queries.size() + 63) / 64), 1, 1);
  glMemoryBarrier(GL_BUFFER_UPDATE_BARRIER_BIT | GL_SHADER_STORAGE_BARRIER_BIT);
  std::vector<MapAnswer> answers(queries.size());
  glGetNamedBufferSubData(
      buffers[1], 0, static_cast<GLsizeiptr>(answers.size() * sizeof(MapAnswer)), answers.data());
  glUseProgram(0);
  glDeleteBuffers(2, buffers.data());
  glDeleteProgram(program);
  glDeleteShader(shader);
  return answers;
}

// CPU model of the display coordinate of cell center x = index + 0.5 of a
// level with the given sizes when the central cross is squeezed by @p fold.
float modelDisplay(int level, int index, float fold) {
  const auto size = static_cast<float>(tess::toneRowSize(level));
  const auto below = static_cast<float>(tess::toneRowSize(level - 1));
  const float corner = 0.5F * below;
  const float x = static_cast<float>(index) + 0.5F;
  if (x >= size - corner) {
    return x - (fold * (size - below));
  }
  if (x >= corner) {
    return corner + ((x - corner) * (1.0F - fold));
  }
  return x;
}

// The shader's zoom-nesting maps agree with the Theorem 11 model on the CPU:
// expansion to level 10 is expandToLevel; the fold position of a cell's
// display coordinate returns the cell center; and a level-10 cell's display
// coordinate is that of its level-l index, or -1 exactly for cells the level lacks.
TEST_F(EmanationTableGlTest, ShaderNestingMapsMatchTheCpuModel) {
  std::vector<MapQuery> queries;
  for (int level = 6; level <= tess::EMANATION_RENDER_LEVEL; ++level) {
    for (const float fold : {0.0F, 0.35F, 0.9F}) {
      for (int index = 0; index < tess::toneRowSize(level); ++index) {
        queries.push_back({.level = level,
                           .index = index,
                           .cell = 0,
                           .fold = fold,
                           .display = modelDisplay(level, index, fold),
                           .unused0 = 0.0F,
                           .unused1 = 0.0F,
                           .unused2 = 0.0F});
      }
    }
  }
  const std::vector<MapAnswer> answers = runShaderMaps(queries);
  ASSERT_EQ(answers.size(), queries.size());
  std::size_t expandMismatches = 0;
  std::size_t foldMismatches = 0;
  std::size_t displayMismatches = 0;
  for (std::size_t i = 0; i < queries.size(); ++i) {
    const MapQuery &q = queries[i];
    const MapAnswer &a = answers[i];
    expandMismatches +=
        a.expanded == tess::expandToLevel(q.level, tess::EMANATION_RENDER_LEVEL, q.index)
            ? std::size_t{0}
            : std::size_t{1};
    foldMismatches += std::abs(a.foldPosition - (static_cast<float>(q.index) + 0.5F)) < 1e-3F
                          ? std::size_t{0}
                          : std::size_t{1};
    displayMismatches +=
        std::abs(a.displayPosition - q.display) < 1e-3F ? std::size_t{0} : std::size_t{1};
  }
  EXPECT_EQ(expandMismatches, 0U);
  EXPECT_EQ(foldMismatches, 0U);
  EXPECT_EQ(displayMismatches, 0U);

  // A level-10 cell has a display coordinate exactly when the level's expansion
  // reaches it; the others lie in a central cross the fold removed.
  std::vector<MapQuery> cells;
  std::vector<bool> expectedShown;
  const int top = tess::toneRowSize(tess::EMANATION_RENDER_LEVEL);
  for (int level = 6; level < tess::EMANATION_RENDER_LEVEL; ++level) {
    std::vector<bool> inImage(static_cast<std::size_t>(top), false);
    for (int index = 0; index < tess::toneRowSize(level); ++index) {
      inImage[static_cast<std::size_t>(
          tess::expandToLevel(level, tess::EMANATION_RENDER_LEVEL, index))] = true;
    }
    for (int cell = 0; cell < top; ++cell) {
      cells.push_back({.level = level,
                       .index = 0,
                       .cell = cell,
                       .fold = 0.0F,
                       .display = 0.0F,
                       .unused0 = 0.0F,
                       .unused1 = 0.0F,
                       .unused2 = 0.0F});
      expectedShown.push_back(inImage[static_cast<std::size_t>(cell)]);
    }
  }
  const std::vector<MapAnswer> cellAnswers = runShaderMaps(cells);
  ASSERT_EQ(cellAnswers.size(), cells.size());
  std::size_t visibilityMismatches = 0;
  for (std::size_t i = 0; i < cells.size(); ++i) {
    const bool shown = cellAnswers[i].cellDisplay >= 0.0F;
    visibilityMismatches += shown == expectedShown[i] ? std::size_t{0} : std::size_t{1};
  }
  EXPECT_EQ(visibilityMismatches, 0U);
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

// An interactive strut change builds the new table on a worker thread: the
// render that requests it keeps the previous table bound, and a later render
// uploads the finished table cell for cell.
TEST_F(EmanationTableGlTest, InteractiveStrutChangeKeepsTheOldTableUntilTheBuildFinishes) {
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  {
    TesseractRenderer renderer;
    expectTextureMatchesCpu(renderer, target, 17);
    TesseractFrameInputs inputs;
    inputs.targetTexture = target;
    inputs.width = TARGET_SIZE;
    inputs.height = TARGET_SIZE;
    inputs.emanationStrut = 129;
    renderer.render(inputs);
    ASSERT_EQ(glGetError(), GL_NO_ERROR);
    EXPECT_EQ(renderer.emanationBakedStrut(), 17) << "the change must not build on the render thread";
    // A level-10 build takes tens of milliseconds; 400 renders 10 ms apart
    // bound the wait at 4 s.
    for (int attempt = 0; attempt < 400 && renderer.emanationBakedStrut() != 129; ++attempt) {
      std::this_thread::sleep_for(std::chrono::milliseconds(10));
      renderer.render(inputs);
    }
    ASSERT_EQ(renderer.emanationBakedStrut(), 129);
    const tess::EmanationTable cpu = tess::createStruttedEt(tess::EMANATION_RENDER_LEVEL, 129);
    EXPECT_EQ(readTexture(renderer.emanationTexture()), cpu.value);
    EXPECT_EQ(renderer.emanationDmzCount(), 9096U);
    renderer.shutdown();
  }
  glDeleteTextures(1, &target);
}

// The trail the pass uploads is the CPU generator's walk, and every cell of it
// is a filled texel of the baked table.
TEST_F(EmanationTableGlTest, PulseWalkUploadedToTheShaderOnlyVisitsFilledCells) {
  const GLuint target = createColorTexture32f(TARGET_SIZE, TARGET_SIZE);
  {
    TesseractRenderer renderer;
    for (const int strut : {17, 129}) {
      for (const int step : {0, 5, 200}) {
        TesseractFrameInputs inputs;
        inputs.targetTexture = target;
        inputs.width = TARGET_SIZE;
        inputs.height = TARGET_SIZE;
        inputs.emanationStrut = strut;
        inputs.emanationWalk = true;
        inputs.emanationWalkStep = step;
        inputs.emanationBakeBlocking = true;
        renderer.render(inputs);
        ASSERT_EQ(glGetError(), GL_NO_ERROR);

        const tess::EmanationTable cpu =
            tess::createStruttedEt(tess::EMANATION_RENDER_LEVEL, strut);
        const std::vector<tess::WalkCell> walk =
            tess::xorTripleWalk(cpu, tess::EMANATION_WALK_LENGTH);
        const std::vector<std::int16_t> texels = readTexture(renderer.emanationTexture());
        const auto &trail = renderer.emanationTrail();
        ASSERT_EQ(trail.size(), static_cast<std::size_t>(blackhole::TESSERACT_EMANATION_TRAIL));
        for (std::size_t i = 0; i < trail.size(); ++i) {
          const auto length = static_cast<int>(walk.size());
          const int index = (((step - static_cast<int>(i)) % length) + length) % length;
          EXPECT_EQ(trail[i], walk[static_cast<std::size_t>(index)])
              << "S=" << strut << " step " << step;
          const auto texel = (static_cast<std::size_t>(trail[i].row) * TABLE_SIZE) +
                             static_cast<std::size_t>(trail[i].col);
          EXPECT_NE(texels[texel], 0) << "S=" << strut << " step " << step << " trail " << i;
        }
      }
    }
    TesseractFrameInputs off;
    off.targetTexture = target;
    off.width = TARGET_SIZE;
    off.height = TARGET_SIZE;
    off.emanationWalk = false;
    renderer.render(off);
    EXPECT_TRUE(renderer.emanationTrail().empty());
    renderer.shutdown();
  }
  glDeleteTextures(1, &target);
}

} // namespace
