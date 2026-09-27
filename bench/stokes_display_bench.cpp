/**
 * @file stokes_display_bench.cpp
 * @brief Paired GPU timings for angular and Cartesian polarization display.
 *
 * The dispatch reads deterministic Stokes samples and writes one RGB result
 * per invocation. Timings cover the display kernel and its buffer traffic;
 * they do not measure complete ray tracing or predict application frame rate.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <exception>
#include <iomanip>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include "support/gl_compute_harness.h"

namespace {
using namespace gl;

constexpr std::size_t SAMPLE_COUNT = 1024UZ * 1024UZ;
constexpr GLuint GROUP_COUNT = static_cast<GLuint>(SAMPLE_COUNT / 256);
constexpr int WARMUP_PAIRS = 8;
constexpr int TIMED_PAIRS = 31;

// Frozen angular definition permits comparison against the production include
// without maintaining a second Cartesian implementation inside the benchmark.
constexpr const char *ANGULAR_SOURCE = R"(
vec3 stokesDisplayColor(vec4 stokes, vec3 baseColor) {
    float I = max(stokes.x, 0.0);
    if (I < 1.0e-10) { return baseColor * 0.0; }
    float P_lin = sqrt(stokes.y * stokes.y + stokes.z * stokes.z) / I;
    P_lin = clamp(P_lin, 0.0, 1.0);
    float chi = 0.5 * atan(stokes.z, stokes.y);
    float tintR = 1.0 + P_lin * 0.4 * cos(2.0 * chi);
    float tintG = 1.0 + P_lin * 0.4 * sin(2.0 * chi);
    float tintB = 1.0 + clamp(stokes.w / I, -0.5, 0.5) * 0.2;
    return clamp(baseColor * vec3(tintR, tintG, tintB), 0.0, 10.0);
}
)";

std::string shaderSource(bool angular) {
  return std::string(R"(#version 460 core
layout(local_size_x = 256) in;
struct Sample { vec4 stokes; vec4 color; };
layout(std430, binding = 0) readonly buffer Input { Sample samples[]; };
layout(std430, binding = 1) writeonly buffer Output { vec4 result[]; };
)") + (angular ? ANGULAR_SOURCE : "#include \"include/stokes_transport.glsl\"\n") +
         R"(
void main() {
    uint index = gl_GlobalInvocationID.x;
    result[index] = vec4(stokesDisplayColor(samples[index].stokes,
                                           samples[index].color.rgb), 1.0);
}
)";
}

struct Resources {
  Resources() = default;
  Resources(const Resources &) = delete;
  Resources &operator=(const Resources &) = delete;
  Resources(Resources &&) = delete;
  Resources &operator=(Resources &&) = delete;
  std::array<GLuint, 2> programs{};
  std::array<GLuint, 3> buffers{};
  GLuint query = 0;
  ~Resources() {
    for (GLuint const program : programs) {
      glDeleteProgram(program);
    }
    glDeleteBuffers(static_cast<GLsizei>(buffers.size()), buffers.data());
    glDeleteQueries(1, &query);
  }
};

void checkGl() {
  if (glGetError() != GL_NO_ERROR) {
    throw std::runtime_error("OpenGL reported an error");
  }
}

double median(std::vector<double> values) {
  std::ranges::sort(values);
  return values.at(values.size() / 2);
}

void runBenchmark() {
  const bhtest::HiddenGlContext context;
  if (!context.available()) {
    throw std::runtime_error("GL 4.6 context unavailable; benchmark requires execution");
  }
  std::cout << "renderer=" << glGetString(GL_RENDERER) << '\n'
            << "version=" << glGetString(GL_VERSION) << '\n';
  Resources resources;
  resources.programs[0] = bhtest::createComputeProgram(shaderSource(true));
  resources.programs[1] = bhtest::createComputeProgram(shaderSource(false));

  using Sample = std::array<float, 8>;
  std::vector<Sample> samples(SAMPLE_COUNT);
  std::uint32_t randomState = 0x31415926U;
  auto randomUnit = [&randomState]() {
    randomState = randomState * 1664525U + 1013904223U;
    return static_cast<float>(randomState >> 8U) / 16777216.0F;
  };
  for (std::size_t index = 0; index < samples.size(); ++index) {
    float const intensity = 0.01F + 3.0F * randomUnit();
    float const directionQ = 2.0F * randomUnit() - 1.0F;
    float const directionU = 2.0F * randomUnit() - 1.0F;
    float const fraction = 0.9F * randomUnit();
    float const norm = std::max(std::hypot(directionQ, directionU), 1.0e-6F);
    // |V| <= 0.1 I and linear fraction <= 0.9 keep total polarization <= I.
    float const circular = (0.2F * randomUnit() - 0.1F) * intensity;
    float const polarizedScale = index % 16 == 0 ? 0.0F : fraction * intensity / norm;
    samples[index] = {intensity,
                      directionQ * polarizedScale,
                      directionU * polarizedScale,
                      circular,
                      0.5F * intensity,
                      intensity,
                      1.5F * intensity,
                      0.0F};
  }
  glCreateBuffers(static_cast<GLsizei>(resources.buffers.size()), resources.buffers.data());
  glNamedBufferData(resources.buffers[0], static_cast<GLsizeiptr>(samples.size() * sizeof(Sample)),
                    samples.data(), GL_STATIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, resources.buffers[0]);
  auto const outputBytes = static_cast<GLsizeiptr>(SAMPLE_COUNT * sizeof(float) * 4);
  for (std::size_t index = 1; index < resources.buffers.size(); ++index) {
    glNamedBufferData(resources.buffers[index], outputBytes, nullptr, GL_DYNAMIC_READ);
  }
  glGenQueries(1, &resources.query);
  checkGl();

  auto dispatch = [&](std::size_t lane, bool timed) {
    glUseProgram(resources.programs[lane]);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, resources.buffers[lane + 1]);
    if (timed) {
      glBeginQuery(GL_TIME_ELAPSED, resources.query);
    }
    glDispatchCompute(GROUP_COUNT, 1, 1);
    glMemoryBarrier(GL_SHADER_STORAGE_BARRIER_BIT);
    if (!timed) {
      glFinish();
      checkGl();
      return 0.0;
    }
    glEndQuery(GL_TIME_ELAPSED);
    GLuint64 elapsed = 0;
    glGetQueryObjectui64v(resources.query, GL_QUERY_RESULT, &elapsed);
    checkGl();
    if (elapsed == 0) {
      throw std::runtime_error("GPU timer returned zero elapsed nanoseconds");
    }
    return static_cast<double>(elapsed) / 1.0e6;
  };

  std::array<std::vector<double>, 2> timings;
  std::vector<double> pairedRatios;
  for (int pair = -WARMUP_PAIRS; pair < TIMED_PAIRS; ++pair) {
    auto const first = static_cast<std::size_t>((pair + WARMUP_PAIRS) % 2);
    std::array<double, 2> elapsed{};
    elapsed[first] = dispatch(first, pair >= 0);
    elapsed[1 - first] = dispatch(1 - first, pair >= 0);
    if (pair >= 0) {
      timings[0].push_back(elapsed[0]);
      timings[1].push_back(elapsed[1]);
      pairedRatios.push_back(elapsed[0] / elapsed[1]);
    }
  }

  std::array<std::vector<float>, 2> outputs;
  glMemoryBarrier(GL_BUFFER_UPDATE_BARRIER_BIT);
  for (std::size_t lane = 0; lane < outputs.size(); ++lane) {
    outputs[lane].resize(SAMPLE_COUNT * 4);
    glGetNamedBufferSubData(resources.buffers[lane + 1], 0, outputBytes, outputs[lane].data());
  }
  checkGl();
  double maximumDifference = 0.0;
  for (std::size_t index = 0; index < SAMPLE_COUNT; ++index) {
    for (std::size_t channel = 0; channel < 4; ++channel) {
      std::size_t const offset = index * 4 + channel;
      if (!std::isfinite(outputs[1][offset])) {
        throw std::runtime_error("Cartesian display produced a nonfinite value");
      }
      if (samples[index][1] == 0.0F) {
        continue; // Angular GLSL atan(y,x) is undefined when x is zero.
      }
      if (!std::isfinite(outputs[0][offset])) {
        throw std::runtime_error("Angular display produced a nonfinite defined-domain value");
      }
      maximumDifference =
          std::max(maximumDifference, std::abs(static_cast<double>(outputs[0][offset]) -
                                               static_cast<double>(outputs[1][offset])));
    }
  }
  std::cout << std::setprecision(9) << "samples=" << SAMPLE_COUNT
            << " warmup_pairs=" << WARMUP_PAIRS << " timed_pairs=" << TIMED_PAIRS << '\n'
            << "angular_median_ms=" << median(timings[0]) << '\n'
            << "cartesian_median_ms=" << median(timings[1]) << '\n'
            << "median_paired_angular_over_cartesian=" << median(pairedRatios) << '\n'
            << "defined_angle_max_absolute_difference=" << maximumDifference << '\n'
            << "zero_Q_angular_values_excluded=true\n"
            << "scope=display_kernel_and_buffer_traffic_only\n";
  if (maximumDifference > 5.0e-6) {
    throw std::runtime_error("display difference exceeds 5e-6");
  }
}
} // namespace

int main() {
  try {
    runBenchmark();
    return 0;
  } catch (std::exception const &error) {
    std::cerr << "stokes_display_bench: " << error.what() << '\n';
    return 1;
  }
}
