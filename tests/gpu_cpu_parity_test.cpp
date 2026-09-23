/**
 * gpu_cpu_parity_test.cpp
 *
 * GPU/CPU parity for the verified physics surface: each case evaluates a
 * function from the src/physics/verified headers on the CPU and its
 * transpiled twin from the shader/include/verified GLSL modules in a
 * 1x1x1 compute dispatch, then compares within float32 tolerance. GLSL
 * has no native include directive, so
 * expandIncludes() inlines the verified modules from
 * BH_SHADER_INCLUDE_DIR before compilation.
 *
 * The suite SKIPs (does not fail) when no GL 4.6 context can be created
 * -- headless CI without a display -- and FAILS on any shader compile or
 * link error once a context exists: a parity claim over a shader that
 * does not compile is no claim at all.
 */

#include <cmath>
#include <cstddef>
#include <fstream>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>
#include <gtest/gtest.h>

#include "physics/verified/cosmology.hpp"
#include "physics/verified/eos.hpp"
#include "physics/verified/schwarzschild.hpp"

using namespace gl;

#ifndef BH_SHADER_INCLUDE_DIR
#error "BH_SHADER_INCLUDE_DIR must point at shader/include"
#endif

namespace {

constexpr float TOLERANCE_SINGLE = 1e-6F;

/// Inline `#include "verified/x.glsl"` directives from the shader tree.
/// The verified modules carry only commented-out include lines
/// themselves, so one expansion level suffices.
std::string expandIncludes(const std::string &source) {
  static const std::regex includeRe(R"~(#include\s+"([^"]+)")~");
  std::string out;
  std::sregex_iterator it(source.begin(), source.end(), includeRe);
  std::sregex_iterator const end;
  std::size_t last = 0;
  for (; it != end; ++it) {
    out.append(source, last, static_cast<std::size_t>(it->position()) - last);
    const std::string path = std::string(BH_SHADER_INCLUDE_DIR) + "/" + (*it)[1].str();
    const std::ifstream file(path);
    if (!file) {
      throw std::runtime_error("cannot open GLSL include: " + path);
    }
    std::ostringstream content;
    content << file.rdbuf();
    out += content.str();
    last = static_cast<std::size_t>(it->position() + it->length());
  }
  out.append(source, last);
  return out;
}

} // namespace

class GPUCPUParityTest : public ::testing::Test {
private:
  GLFWwindow *window_ = nullptr;

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
    GLFWwindow *probe = glfwCreateWindow(1, 1, "GPU Parity Probe", nullptr, nullptr);
    if (probe == nullptr) {
      glfwTerminate();
      return;
    }
    glfwMakeContextCurrent(probe);
    glbinding::initialize(glfwGetProcAddress);
    glfwDestroyWindow(probe);
    glAvailable = true;
  }

  static void TearDownTestSuite() {
    if (glAvailable) {
      glfwTerminate();
    }
  }

  void SetUp() override {
    if (!glAvailable) {
      GTEST_SKIP() << "no GL 4.6 context available (headless environment)";
    }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    window_ = glfwCreateWindow(1, 1, "GPU Parity Test", nullptr, nullptr);
    ASSERT_NE(window_, nullptr);
    glfwMakeContextCurrent(window_);
  }

  void TearDown() override {
    if (window_ != nullptr) {
      glfwDestroyWindow(window_);
      window_ = nullptr;
    }
  }

  static GLuint createComputeProgram(const std::string &rawSource) {
    const std::string source = expandIncludes(rawSource);
    GLuint const shader = glCreateShader(GL_COMPUTE_SHADER);
    const char *srcPtr = source.c_str();
    glShaderSource(shader, 1, &srcPtr, nullptr);
    glCompileShader(shader);

    GLint status = 0;
    glGetShaderiv(shader, GL_COMPILE_STATUS, &status);
    if (status == 0) {
      GLint length = 0;
      glGetShaderiv(shader, GL_INFO_LOG_LENGTH, &length);
      std::string log(static_cast<std::size_t>(length), '\0');
      glGetShaderInfoLog(shader, length, nullptr, log.data());
      glDeleteShader(shader);
      throw std::runtime_error("compute shader compilation failed:\n" + log);
    }

    GLuint const program = glCreateProgram();
    glAttachShader(program, shader);
    glLinkProgram(program);
    glGetProgramiv(program, GL_LINK_STATUS, &status);
    if (status == 0) {
      GLint length = 0;
      glGetProgramiv(program, GL_INFO_LOG_LENGTH, &length);
      std::string log(static_cast<std::size_t>(length), '\0');
      glGetProgramInfoLog(program, length, nullptr, log.data());
      glDeleteProgram(program);
      glDeleteShader(shader);
      throw std::runtime_error("compute program linking failed:\n" + log);
    }

    glDeleteShader(shader);
    return program;
  }

  /// Dispatch 1x1x1 and read back `count` floats from the SSBO.
  static std::vector<float> runComputeShader(GLuint program, GLuint outputBuffer,
                                             std::size_t count) {
    glUseProgram(program);
    glDispatchCompute(1, 1, 1);
    glMemoryBarrier(GL_SHADER_STORAGE_BARRIER_BIT);

    auto *ptr = static_cast<float *>(glMapNamedBufferRange(
        outputBuffer, 0, static_cast<GLsizeiptr>(sizeof(float) * count), GL_MAP_READ_BIT));
    if (ptr == nullptr) {
      throw std::runtime_error("glMapNamedBufferRange returned null");
    }
    std::vector<float> result(ptr, ptr + count);
    glUnmapNamedBuffer(outputBuffer);
    return result;
  }

  /// Compile `body`, run it, and return result[0] of an 8-float SSBO.
  static float evalScalarShader(const std::string &body) {
    GLuint const program = createComputeProgram(body);
    GLuint ssbo = 0;
    glCreateBuffers(1, &ssbo);
    glNamedBufferData(ssbo, sizeof(float) * 8, nullptr, GL_DYNAMIC_DRAW);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
    const float value = runComputeShader(program, ssbo, 8)[0];
    glDeleteBuffers(1, &ssbo);
    glDeleteProgram(program);
    return value;
  }
};

bool GPUCPUParityTest::glAvailable = false;

// ============================================================================
// Schwarzschild metric parity
// ============================================================================

TEST_F(GPUCPUParityTest, SchwarzschildGTT) {
  double const cpuResult = verified::schwarzschildGTt(10.0, 1.0);
  float const gpuResult = evalScalarShader(R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };
        #include "verified/schwarzschild.glsl"
        void main() {
            result[0] = schwarzschild_g_tt(10.0, 1.0);
        }
    )");
  float const relError = std::abs(gpuResult - static_cast<float>(cpuResult)) /
                         std::abs(static_cast<float>(cpuResult));
  EXPECT_LE(relError, TOLERANCE_SINGLE)
      << "g_tt CPU " << cpuResult << " vs GPU " << gpuResult;
}

TEST_F(GPUCPUParityTest, SchwarzschildGRR) {
  double const cpuResult = verified::schwarzschildGRr(10.0, 1.0);
  float const gpuResult = evalScalarShader(R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };
        #include "verified/schwarzschild.glsl"
        void main() {
            result[0] = schwarzschild_g_rr(10.0, 1.0);
        }
    )");
  float const relError = std::abs(gpuResult - static_cast<float>(cpuResult)) /
                         std::abs(static_cast<float>(cpuResult));
  EXPECT_LE(relError, TOLERANCE_SINGLE)
      << "g_rr CPU " << cpuResult << " vs GPU " << gpuResult;
}

TEST_F(GPUCPUParityTest, SchwarzschildChristoffelTTR) {
  double const cpuResult = verified::christoffelTTr(10.0, 1.0);
  float const gpuResult = evalScalarShader(R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };
        #include "verified/schwarzschild.glsl"
        void main() {
            result[0] = christoffel_t_tr(10.0, 1.0);
        }
    )");
  float const absError = std::abs(gpuResult - static_cast<float>(cpuResult));
  EXPECT_LE(absError, TOLERANCE_SINGLE)
      << "Gamma^t_tr CPU " << cpuResult << " vs GPU " << gpuResult;
}

// ============================================================================
// Equation-of-state parity
// ============================================================================

TEST_F(GPUCPUParityTest, PolytropePressure) {
  verified::PolytropeParams const p{1.0, 2.0}; // K = 1, gamma = 2
  double const cpuResult = verified::polytropePressure(p, 1.5);
  float const gpuResult = evalScalarShader(R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };
        #include "verified/eos.glsl"
        void main() {
            PolytropeParams p;
            p.K = 1.0;
            p.gamma = 2.0;
            result[0] = polytrope_pressure(p, 1.5);
        }
    )");
  float const relError = std::abs(gpuResult - static_cast<float>(cpuResult)) /
                         std::abs(static_cast<float>(cpuResult));
  EXPECT_LE(relError, TOLERANCE_SINGLE)
      << "polytrope pressure CPU " << cpuResult << " vs GPU " << gpuResult;
}

// ============================================================================
// Cosmology parity
// ============================================================================

TEST_F(GPUCPUParityTest, HubbleParameter) {
  // Planck 2018 flat LCDM at z = 0.1
  double const cpuResult = verified::hubbleParameter(67.36, 0.3153, 0.1);
  float const gpuResult = evalScalarShader(R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };
        #include "verified/cosmology.glsl"
        void main() {
            result[0] = hubble_parameter(67.36, 0.3153, 0.1);
        }
    )");
  float const relError = std::abs(gpuResult - static_cast<float>(cpuResult)) /
                         std::abs(static_cast<float>(cpuResult));
  EXPECT_LE(relError, TOLERANCE_SINGLE)
      << "H(0.1) CPU " << cpuResult << " vs GPU " << gpuResult;
}

// ============================================================================
// Null-constraint parity through the geodesic four-norm
// ============================================================================

TEST_F(GPUCPUParityTest, SchwarzschildNullConstraint) {
  // Radial null ray at r = 100, M = 1: v_r = f(r) * v_t makes
  // g_ab v^a v^b = 0 exactly (f = 1 - 2M/r).
  GLuint const program = createComputeProgram(R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };

        #include "verified/schwarzschild.glsl"
        #include "verified/rk4.glsl"
        #include "verified/geodesic.glsl"

        void main() {
            float r = 100.0;
            float M = 1.0;
            float theta = 1.5707963;
            MetricComponents g = MetricComponents(
                schwarzschild_g_tt(r, M),
                schwarzschild_g_rr(r, M),
                schwarzschild_g_thth(r),
                schwarzschild_g_phph(r, theta),
                0.0);
            float f = f_schwarzschild(r, M);
            StateVector s = StateVector(0.0, r, theta, 0.0,
                                        1.0, f, 0.0, 0.0);
            result[0] = abs(four_norm(g, s));
        }
    )");
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, sizeof(float) * 8, nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
  const float gpuNorm = runComputeShader(program, ssbo, 8)[0];
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);

  EXPECT_LE(gpuNorm, 1e-5F) << "null four-norm on GPU: " << gpuNorm;
}

int main(int argc, char **argv) {
  ::testing::InitGoogleTest(&argc, argv);
  return RUN_ALL_TESTS();
}
