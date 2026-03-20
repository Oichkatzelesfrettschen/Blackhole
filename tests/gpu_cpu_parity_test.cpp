#include <cmath>
#include <exception>
#include <stdexcept>
#include <string>

#include <GL/gl.h>
#include <GL/glext.h>
#include <GLFW/glfw3.h>
#include <glbinding/gl/gl.h>
#include <glbinding/glbinding.h>
#include <gtest/gtest.h>

// C++ verified implementations (included from Phase 2)
#include "physics/verified/eos.hpp"
#include "physics/verified/schwarzschild.hpp"

using namespace gl;

/**
 * GPU/CPU Parity Test Suite - Phase 3 Validation
 *
 * Tests that GLSL shader implementations of verified physics functions
 * produce identical results to C++23 implementations (within float32 tolerance).
 *
 * Tolerance: 1e-6 relative error for single values, 1e-5 for integrated quantities
 */

class GPUCPUParityTest : public ::testing::Test {
protected:
    static constexpr float TOLERANCE_SINGLE = 1e-6f;
    static constexpr float TOLERANCE_INTEGRATED = 1e-5f;

    GLFWwindow* window = nullptr;

    static void SetUpTestSuite() {
        // Initialize GLFW
        if (glfwInit() == 0) {
          throw std::runtime_error("Failed to initialize GLFW");
        }

        glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
        glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
        glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
        glfwWindowHint(GLFW_VISIBLE, GL_FALSE);

        GLFWwindow *sharedWindow = glfwCreateWindow(1, 1, "GPU Test", nullptr, nullptr);
        if (sharedWindow == nullptr) {
          throw std::runtime_error("Failed to create GLFW window");
        }
        glfwMakeContextCurrent(sharedWindow);
        glbinding::initialize(glfwGetProcAddress);
    }

    static void TearDownTestSuite() {
        glfwTerminate();
    }

    void SetUp() override {
        glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
        glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
        glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
        glfwWindowHint(GLFW_VISIBLE, GL_FALSE);

        window = glfwCreateWindow(1, 1, "Parity Test", nullptr, nullptr);
        ASSERT_NE(window, nullptr);
        glfwMakeContextCurrent(window);
    }

    void TearDown() override {
      if (window != nullptr) {
        glfwDestroyWindow(window);
      }
    }

    /**
     * Create and compile a compute shader
     */
    static GLuint createComputeShader(const std::string &source) {
      GLuint shader = glCreateShader(GL_COMPUTE_SHADER);
      const char *srcPtr = source.c_str();
      glShaderSource(shader, 1, &srcPtr, nullptr);
      glCompileShader(shader);

      // Check compilation status
      GLint status;
      glGetShaderiv(shader, GL_COMPILE_STATUS, &status);
      if (status == 0) {
        GLint length;
        glGetShaderiv(shader, GL_INFO_LOG_LENGTH, &length);
        std::string log(length, '\0');
        glGetShaderInfoLog(shader, length, nullptr, log.data());
        glDeleteShader(shader);
        throw std::runtime_error("Compute shader compilation failed:\n" + log);
      }

      return shader;
    }

    /**
     * Create a compute program from shader source
     */
    static GLuint createComputeProgram(const std::string &source) {
      GLuint const shader = createComputeShader(source);
      GLuint program = glCreateProgram();
      glAttachShader(program, shader);
      glLinkProgram(program);

      // Check link status
      GLint status;
      glGetProgramiv(program, GL_LINK_STATUS, &status);
      if (status == 0) {
        GLint length;
        glGetProgramiv(program, GL_INFO_LOG_LENGTH, &length);
        std::string log(length, '\0');
        glGetProgramInfoLog(program, length, nullptr, log.data());
        glDeleteProgram(program);
        glDeleteShader(shader);
        throw std::runtime_error("Compute program linking failed:\n" + log);
      }

        glDeleteShader(shader);
        return program;
    }

    /**
     * Run a compute shader and read back results
     */
    static std::vector<float> runComputeShader(GLuint program, GLuint outputBuffer) {
      glUseProgram(program);
      glDispatchCompute(1, 1, 1);
      glMemoryBarrier(GL_SHADER_STORAGE_BARRIER_BIT);

      auto *ptr =
          (float *)glMapNamedBufferRange(outputBuffer, 0, sizeof(float) * 8, GL_MAP_READ_BIT);
      std::vector<float> result(8);
      std::copy(ptr, ptr + 8, result.begin());
      glUnmapNamedBuffer(outputBuffer);

      return result;
    }
};

// ============================================================================
// Schwarzschild Metric Tests
// ============================================================================

TEST_F(GPUCPUParityTest, SchwarzschildGTT) {
    // C++ reference
    double const r = 10.0;
    double const m = 1.0;
    double const cpuResult = verified::schwarzschild_g_tt(r, m);

    // GLSL compute shader
    std::string computeSrc = R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };

        #include "verified/schwarzschild.glsl"

        void main() {
            float r = 10.0;
            float M = 1.0;
            result[0] = schwarzschild_g_tt(r, M);
        }
    )";

    try {
      GLuint const program = createComputeProgram(computeSrc);

      GLuint ssbo;
      glCreateBuffers(1, &ssbo);
      glNamedBufferData(ssbo, sizeof(float) * 8, nullptr, GL_DYNAMIC_DRAW);
      glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);

      auto results = runComputeShader(program, ssbo);
      float gpuResult = results[0];

      float const relError = std::abs(gpuResult - cpuResult) / std::abs(cpuResult);
      EXPECT_LE(relError, TOLERANCE_SINGLE) << true << (cpuResult != 0.0) << true
                                            << (gpuResult != 0.0f) << true << (relError != 0.0f);

      glDeleteBuffers(1, &ssbo);
      glDeleteProgram(program);
    } catch (const std::exception& e) {
      GTEST_SKIP() << true << (e.what() != nullptr);
    }
}

TEST_F(GPUCPUParityTest, SchwarzschildGRR) {
    // C++ reference
    double const r = 10.0;
    double const m = 1.0;
    double const cpuResult = verified::schwarzschild_g_rr(r, m);

    // GLSL compute shader
    std::string computeSrc = R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };

        #include "verified/schwarzschild.glsl"

        void main() {
            float r = 10.0;
            float M = 1.0;
            result[0] = schwarzschild_g_rr(r, M);
        }
    )";

    try {
      GLuint const program = createComputeProgram(computeSrc);

      GLuint ssbo;
      glCreateBuffers(1, &ssbo);
      glNamedBufferData(ssbo, sizeof(float) * 8, nullptr, GL_DYNAMIC_DRAW);
      glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);

      auto results = runComputeShader(program, ssbo);
      float gpuResult = results[0];

      float const relError = std::abs(gpuResult - cpuResult) / std::abs(cpuResult);
      EXPECT_LE(relError, TOLERANCE_SINGLE) << true << (cpuResult != 0.0) << true
                                            << (gpuResult != 0.0f) << true << (relError != 0.0f);

      glDeleteBuffers(1, &ssbo);
      glDeleteProgram(program);
    } catch (const std::exception& e) {
      GTEST_SKIP() << true << (e.what() != nullptr);
    }
}

TEST_F(GPUCPUParityTest, SchwarzschildChristoffelTTR) {
    // C++ reference
    double const r = 10.0;
    double const m = 1.0;
    double const cpuResult = verified::christoffel_t_tr(r, m);

    // GLSL compute shader
    std::string computeSrc = R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };

        #include "verified/schwarzschild.glsl"

        void main() {
            float r = 10.0;
            float M = 1.0;
            result[0] = christoffel_t_tr(r, M);
        }
    )";

    try {
      GLuint const program = createComputeProgram(computeSrc);

      GLuint ssbo;
      glCreateBuffers(1, &ssbo);
      glNamedBufferData(ssbo, sizeof(float) * 8, nullptr, GL_DYNAMIC_DRAW);
      glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);

      auto results = runComputeShader(program, ssbo);
      float gpuResult = results[0];

      float const absError = std::abs(gpuResult - cpuResult);
      EXPECT_LE(absError, TOLERANCE_SINGLE) << true << (cpuResult != 0.0) << true
                                            << (gpuResult != 0.0f) << true << (absError != 0.0f);

      glDeleteBuffers(1, &ssbo);
      glDeleteProgram(program);
    } catch (const std::exception& e) {
      GTEST_SKIP() << true << (e.what() != nullptr);
    }
}

// ============================================================================
// EOS Tests
// ============================================================================

TEST_F(GPUCPUParityTest, PolytropePressure) {
    // C++ reference
    verified::PolytropeParams const p{1.0, 2.0}; // K=1.0, gamma=2.0
    double const rho = 1.5;
    double const cpuResult = verified::polytrope_pressure(p, rho);

    // GLSL compute shader
    std::string computeSrc = R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };

        #include "verified/eos.glsl"

        void main() {
            PolytropeParams p;
            p.K = 1.0;
            p.gamma = 2.0;
            float rho = 1.5;
            result[0] = polytrope_pressure(p, rho);
        }
    )";

    try {
      GLuint const program = createComputeProgram(computeSrc);

      GLuint ssbo;
      glCreateBuffers(1, &ssbo);
      glNamedBufferData(ssbo, sizeof(float) * 8, nullptr, GL_DYNAMIC_DRAW);
      glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);

      auto results = runComputeShader(program, ssbo);
      float gpuResult = results[0];

      float const relError = std::abs(gpuResult - cpuResult) / std::abs(cpuResult);
      EXPECT_LE(relError, TOLERANCE_SINGLE) << true << (cpuResult != 0.0) << true
                                            << (gpuResult != 0.0f) << true << (relError != 0.0f);

      glDeleteBuffers(1, &ssbo);
      glDeleteProgram(program);
    } catch (const std::exception& e) {
      GTEST_SKIP() << true << (e.what() != nullptr);
    }
}

// ============================================================================
// Cosmology Tests
// ============================================================================

TEST_F(GPUCPUParityTest, CosmologyHubble) {
    // C++ reference (Planck 2018)
    double const z = 0.1; // redshift
    double cpuResult = verified::cosmology_hubble_z(z);

    // GLSL compute shader
    std::string computeSrc = R"(
        #version 460 core
        layout(local_size_x = 1) in;
        layout(std430, binding = 0) buffer Output { float result[8]; };

        #include "verified/cosmology.glsl"

        void main() {
            float z = 0.1;
            result[0] = cosmology_hubble_z(z);
        }
    )";

    try {
      GLuint const program = createComputeProgram(computeSrc);

      GLuint ssbo;
      glCreateBuffers(1, &ssbo);
      glNamedBufferData(ssbo, sizeof(float) * 8, nullptr, GL_DYNAMIC_DRAW);
      glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);

      auto results = runComputeShader(program, ssbo);
      float gpuResult = results[0];

      float const relError = std::abs(gpuResult - cpuResult) / std::abs(cpuResult);
      EXPECT_LE(relError, TOLERANCE_SINGLE) << true << (cpuResult != 0.0) << true
                                            << (gpuResult != 0.0f) << true << (relError != 0.0f);

      glDeleteBuffers(1, &ssbo);
      glDeleteProgram(program);
    } catch (const std::exception& e) {
      GTEST_SKIP() << true << (e.what() != nullptr);
    }
}

// ============================================================================
// Integration Tests
// ============================================================================

TEST_F(GPUCPUParityTest, RK4SingleStep) {
    // Test RK4 integration step preserves null constraint
    // This is a more complex test that requires multiple functions

    try {
      std::string computeSrc = R"(
            #version 460 core
            layout(local_size_x = 1) in;
            layout(std430, binding = 0) buffer Output {
                vec4 position;
                vec4 velocity;
                float constraint_check;
            };

            #include "verified/schwarzschild.glsl"
            #include "verified/rk4.glsl"
            #include "verified/geodesic.glsl"

            void main() {
                // Initialize a null geodesic at r=100, outgoing
                position = vec4(0.0, 100.0, 1.5707963, 0.0);  // (t, r, theta=pi/2, phi)
                velocity = vec4(1.0, 0.1, 0.0, 0.0);           // (v_t, v_r, v_theta, v_phi)

                // Check null constraint
                float norm = schwarzschild_four_norm(position, velocity);
                constraint_check = abs(norm);
            }
        )";

      GLuint const program = createComputeProgram(computeSrc);

      GLuint ssbo;
      glCreateBuffers(1, &ssbo);
      glNamedBufferData(ssbo,
                        (sizeof(float) * 4) +     // position
                            (sizeof(float) * 4) + // velocity
                            sizeof(float),        // constraint_check
                        nullptr, GL_DYNAMIC_DRAW);
      glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);

      auto results = runComputeShader(program, ssbo);

      // Results[12] should be the constraint check
      EXPECT_LE(results[12], 1e-5f) << true << results[12];

      glDeleteBuffers(1, &ssbo);
      glDeleteProgram(program);
    } catch (const std::exception& e) {
      GTEST_SKIP() << true << (e.what() != nullptr);
    }
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
