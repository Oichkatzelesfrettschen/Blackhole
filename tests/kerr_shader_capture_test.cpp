/**
 * @file kerr_shader_capture_test.cpp
 * @brief Shipped kerr.glsl traces Kerr photons to Bardeen's capture edges.
 *
 * A compute dispatch runs kerrInitGeodesic and kerrStep from
 * shader/include/kerr.glsl for a fan of equatorial pixel directions from a
 * camera at r = 30 M. Each ray reports the physical impact parameter of the
 * arriving photon (b = -Lz of the traced time-reversed ray) and whether it
 * escaped or fell in. Every ray with |b| more than 0.5% above Bardeen's
 * critical value on its side must escape and every ray more than 0.5% below
 * it must be captured.
 *
 * Pole crossings are checked by symmetry at a = 0 and against the double
 * precision CPU integrator at a = 0.9.
 *
 * Falsifiers: an lz^2/sin^2 polar potential shortens R by Delta lz^2 and
 * moves both edges inward; a first-order step on sqrt(max(R, 0)) stalls
 * deflected rays at their turning point so none escape; tracing the emitted
 * rather than the arriving photon swaps the prograde and retrograde edges;
 * an unprojected float32 leapfrog loses vr^2 = R over the r^2 dynamic range
 * and bounces near-radial rays back out.
 * Skips without a GL 4.6 context.
 */

#include <algorithm>
#include <cmath>
#include <numbers>
#include <string>
#include <vector>

#include <gtest/gtest.h>

#include "physics/constants.h"
#include "physics/kerr.h"
#include "support/gl_compute_harness.h"

using namespace gl;

namespace {

constexpr int K_RAYS = 1024;
constexpr int K_LOCAL = 64;

// Equatorial critical impact parameter (Bardeen 1973, M = 1), signed so that
// b > 0 is prograde for a > 0.
double equatorialCriticalImpact(double a, bool prograde) {
  if (std::abs(a) < 1e-12) {
    return (prograde ? 1.0 : -1.0) * 3.0 * std::sqrt(3.0);
  }
  const double s = prograde ? -std::abs(a) : std::abs(a);
  const double rPh = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(s)));
  const double r2 = rPh * rPh;
  const double bAbs =
      std::abs(((r2 * rPh) - (3.0 * r2) + (a * a * rPh) + (a * a)) / (std::abs(a) * (rPh - 1.0)));
  const double sign = (a >= 0.0) == prograde ? 1.0 : -1.0;
  return sign * bAbs;
}

const char *const K_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
uniform float physicalSpin;
uniform float maxAngle;
uniform int rayCount;
#include "include/kerr.glsl"
void main() {
  int i = int(gl_GlobalInvocationID.x);
  if (i >= rayCount) {
    return;
  }
  float r_s = 2.0;
  float a = 0.5 * physicalSpin * r_s;
  float alpha = maxAngle * (2.0 * (float(i) + 0.5) / float(rayCount) - 1.0);
  vec3 pos = vec3(30.0, 0.0, 0.0);
  vec3 dir = vec3(-cos(alpha), sin(alpha), 0.0);
  float aTrace = kerrTraceSpin(a);
  KerrConsts c;
  KerrRay ray;
  kerrInitGeodesic(pos, dir, r_s, aTrace, c, ray);
  float rHorizon = kerrOuterHorizon(r_s, a);
  float fate = 0.0;
  for (int step = 0; step < 400000; ++step) {
    if (ray.r <= rHorizon * 1.001) { fate = -1.0; break; }
    if (ray.r > 60.0 && ray.vr > 0.0) { fate = 1.0; break; }
    kerrStep(ray, r_s, aTrace, c, 2.0e-3 / (1.0 + ray.r * ray.r));
  }
  result[2 * i] = -c.Lz;
  result[2 * i + 1] = fate;
}
)";

// Final escape direction of a fan of rays from a camera at r = 30 M in the
// equatorial plane: `plane` 0 fans in the equatorial (xy) plane, 1 in the
// meridional (xz) plane. Rays escape at r = escapeR with a step that keeps
// dr/r bounded far out.
const char *const K_FAN_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
uniform float physicalSpin;
uniform int rayCount;
uniform int plane;
uniform float escapeR;
#include "include/kerr.glsl"
void main() {
  int i = int(gl_GlobalInvocationID.x);
  if (i >= rayCount) {
    return;
  }
  float r_s = 2.0;
  float a = 0.5 * physicalSpin * r_s;
  float alpha = 0.3 * (2.0 * (float(i) + 0.5) / float(rayCount) - 1.0);
  vec3 pos = vec3(30.0, 0.0, 0.0);
  vec3 dir = plane == 0 ? vec3(-cos(alpha), sin(alpha), 0.0) : vec3(-cos(alpha), 0.0, sin(alpha));
  float aTrace = kerrTraceSpin(a);
  KerrConsts c;
  KerrRay ray;
  kerrInitGeodesic(pos, dir, r_s, aTrace, c, ray);
  float rHorizon = kerrOuterHorizon(r_s, a);
  float fate = 0.0;
  for (int step = 0; step < 2000000; ++step) {
    if (ray.r <= rHorizon * 1.001) { fate = -1.0; break; }
    if (ray.r > escapeR && ray.vr > 0.0) { fate = 1.0; break; }
    kerrStep(ray, r_s, aTrace, c, 2.0e-3 / (1.0 + ray.r * ray.r) * max(1.0, ray.r / 5.0));
  }
  result[4 * i] = fate;
  result[4 * i + 1] = ray.n.x;
  result[4 * i + 2] = ray.n.y;
  result[4 * i + 3] = ray.n.z;
}
)";

const char *const K_ONSHELL_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
uniform int rayCount;
#include "include/kerr.glsl"
float hash(float n) { return fract(sin(n) * 43758.5453); }
void main() {
  int i = int(gl_GlobalInvocationID.x);
  if (i >= rayCount) {
    return;
  }
  float fi = float(i);
  float r_s = 2.0;
  float a = (2.0 * hash(fi + 0.1) - 1.0) * 0.99;
  vec3 pos = normalize(vec3(hash(fi + 1.3) - 0.5, hash(fi + 2.7) - 0.5, hash(fi + 3.1) - 0.5))
             * (6.0 + 40.0 * hash(fi + 4.9));
  vec3 dir = normalize(vec3(hash(fi + 5.3) - 0.5, hash(fi + 6.1) - 0.5, hash(fi + 7.7) - 0.5));
  KerrConsts c;
  KerrRay ray;
  kerrInitGeodesic(pos, dir, r_s, a, c, ray);
  float P = (ray.r * ray.r + a * a) - a * c.Lz;
  float Qe = c.Q + (c.Lz - a) * (c.Lz - a);
  float R = P * P - kerrDelta(ray.r, a, r_s) * Qe;
  result[3 * i] = abs(R - ray.vr * ray.vr) / max(P * P, 1.0);
  float scale = max(abs(c.Q) + a * a + c.Lz * c.Lz, 1.0);
  float w2 = c.Q + c.Lz * c.Lz + a * a * ray.n.z * ray.n.z;
  result[3 * i + 1] = abs(dot(ray.w, ray.w) - w2) / scale;
  result[3 * i + 2] = abs(cross(ray.n, ray.w).z - c.Lz) / sqrt(scale);
}
)";

// The production trace, bhTraceGeodesic from interop_trace.glsl with its
// adaptive step, escape radius, and step budget, driven through the
// declarations of shader/geodesic_trace.comp (its main() is replaced). The
// renderer's default schedule (stepSize 0.1, 300 steps, depthFar 100) must
// place the capture edge within 2% of Bardeen's value.
std::string rendererScheduleShader() {
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  return comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
uniform int rayCount;
void main() {
  int i = int(gl_GlobalInvocationID.y) * int(gl_NumWorkGroups.x) * 16 +
          int(gl_GlobalInvocationID.x);
  if (i >= rayCount) {
    return;
  }
  float alpha = 0.3 * (2.0 * (float(i) + 0.5) / float(rayCount) - 1.0);
  Ray ray;
  ray.position = vec3(30.0, 0.0, 0.0);
  ray.velocity = vec3(-cos(alpha), sin(alpha), 0.0);
  ray.affineParameter = 0.0;
  KerrConsts c;
  KerrRay kr;
  kerrInitGeodesic(ray.position, ray.velocity, 2.0, kerrTraceSpin(0.5 * kerrSpin * 2.0), c, kr);
  HitResult hit = bhTraceGeodesic(ray, 2.0, 100.0, 300, 0.1);
  float fate = hit.hitHorizon ? -1.0 : 1.0;
  bool maxSteps = (hit.debugFlags & BH_DEBUG_FLAG_MAXSTEPS) != 0;
  result[3 * i] = -c.Lz;
  result[3 * i + 1] = fate;
  result[3 * i + 2] = maxSteps ? 1.0 : 0.0;
}
)";
}

class KerrShaderCaptureTest : public ::testing::Test {
protected:
  static bhtest::HiddenGlContext *context;
  static void SetUpTestSuite() { context = new bhtest::HiddenGlContext(); }
  static void TearDownTestSuite() {
    delete context;
    context = nullptr;
  }
  void SetUp() override {
    if (!context->available()) {
      GTEST_SKIP() << "no GL 4.6 context available (headless environment)";
    }
  }

  static std::vector<float> dispatchFan(float physicalSpin, int plane, float escapeR) {
    const GLuint program = bhtest::createComputeProgram(K_FAN_SHADER);
    glUseProgram(program);
    glUniform1f(glGetUniformLocation(program, "physicalSpin"), physicalSpin);
    glUniform1i(glGetUniformLocation(program, "rayCount"), K_RAYS);
    glUniform1i(glGetUniformLocation(program, "plane"), plane);
    glUniform1f(glGetUniformLocation(program, "escapeR"), escapeR);
    GLuint ssbo = 0;
    glCreateBuffers(1, &ssbo);
    glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 4 * K_RAYS), nullptr,
                      GL_DYNAMIC_DRAW);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
    std::vector<float> out =
        bhtest::runComputeProgram(program, ssbo, 4 * K_RAYS, K_RAYS / K_LOCAL);
    glDeleteBuffers(1, &ssbo);
    glDeleteProgram(program);
    return out;
  }

  static std::vector<float> dispatch(const char *source, float physicalSpin) {
    const GLuint program = bhtest::createComputeProgram(source);
    glUseProgram(program);
    const GLint spinLoc = glGetUniformLocation(program, "physicalSpin");
    if (spinLoc >= 0) {
      glUniform1f(spinLoc, physicalSpin);
    }
    const GLint maxAngle = glGetUniformLocation(program, "maxAngle");
    if (maxAngle >= 0) {
      glUniform1f(maxAngle, 0.3F);
    }
    glUniform1i(glGetUniformLocation(program, "rayCount"), K_RAYS);
    GLuint ssbo = 0;
    glCreateBuffers(1, &ssbo);
    glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 3 * K_RAYS), nullptr,
                      GL_DYNAMIC_DRAW);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
    std::vector<float> out =
        bhtest::runComputeProgram(program, ssbo, 3 * K_RAYS, K_RAYS / K_LOCAL);
    glDeleteBuffers(1, &ssbo);
    glDeleteProgram(program);
    return out;
  }
};

bhtest::HiddenGlContext *KerrShaderCaptureTest::context = nullptr;

TEST_F(KerrShaderCaptureTest, CaptureEdgesMatchBardeenWithPhysicalHandedness) {
  constexpr double K_MARGIN = 0.005;
  for (const float spin : {0.0F, 0.01F, 0.5F, 0.9F, 0.99F, -0.9F}) {
    const std::vector<float> out = dispatch(K_SHADER, spin);
    const double bPro = equatorialCriticalImpact(static_cast<double>(spin), true);
    const double bRetro = equatorialCriticalImpact(static_cast<double>(spin), false);
    int checked = 0;
    for (int i = 0; i < K_RAYS; ++i) {
      const auto b = static_cast<double>(out[static_cast<std::size_t>(2 * i)]);
      const float fate = out[static_cast<std::size_t>((2 * i) + 1)];
      const double bc = ((b >= 0.0) == (bPro >= 0.0)) ? bPro : bRetro;
      const double ratio = b / bc;
      if (ratio > 1.0 + K_MARGIN) {
        EXPECT_EQ(fate, 1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
        ++checked;
      } else if (ratio < 1.0 - K_MARGIN) {
        EXPECT_EQ(fate, -1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
        ++checked;
      }
    }
    EXPECT_GT(checked, K_RAYS / 2) << "spin=" << spin;
  }
}

} // namespace

TEST_F(KerrShaderCaptureTest, MeridionalRaysMatchEquatorialTwinsAtZeroSpin) {
  // Schwarzschild is spherically symmetric: the meridional fan is the
  // equatorial fan rotated by 90 degrees about x, so every escaped ray must
  // leave along (n_x, 0, n_y) of its equatorial twin. Rays near the photon
  // sphere wind over the poles, so this fails when the angular motion
  // mirrors a ray at the axis instead of carrying it across.
  const std::vector<float> eq = dispatchFan(0.0F, 0, 200.0F);
  const std::vector<float> mer = dispatchFan(0.0F, 1, 200.0F);
  int compared = 0;
  for (int i = 0; i < K_RAYS; ++i) {
    const auto k = static_cast<std::size_t>(4 * i);
    ASSERT_EQ(eq[k], mer[k]) << "ray " << i;
    if (eq[k] == 1.0F) {
      EXPECT_NEAR(mer[k + 1], eq[k + 1], 2e-3F) << "ray " << i;
      EXPECT_NEAR(mer[k + 2], 0.0F, 2e-3F) << "ray " << i;
      EXPECT_NEAR(mer[k + 3], eq[k + 2], 2e-3F) << "ray " << i;
      ++compared;
    }
  }
  EXPECT_GT(compared, K_RAYS / 4);
}

TEST_F(KerrShaderCaptureTest, MeridionalRaysMatchDoublePrecisionReference) {
  // Meridional rays at a = 0.9 wind over the poles with small Lz (frame
  // dragging gives Lz = g_tphi k^t). The reference integrates the same
  // time-reversed ray (spin -a) with physics::kerrStepMino in double, with a
  // step bounded near the axis, to r = 2000 where the Kerr-Schild and
  // Boyer-Lindquist azimuths agree to about a / r.
  constexpr float K_SPIN = 0.9F;
  constexpr double K_ESCAPE = 2000.0;
  const std::vector<float> gpu = dispatchFan(K_SPIN, 1, static_cast<float>(K_ESCAPE));
  const double mass = physics::C2 / physics::G;
  const double aTrace = -static_cast<double>(K_SPIN);
  const double rPlus = 1.0 + std::sqrt(1.0 - (aTrace * aTrace));
  int compared = 0;
  for (int i = 0; i < K_RAYS; i += 4) {
    const double alpha =
        0.3 * ((2.0 * (static_cast<double>(i) + 0.5) / static_cast<double>(K_RAYS)) - 1.0);
    // Camera on +x at theta = pi/2, phi = 0: e_r = x, e_theta = -z, e_phi = y.
    physics::KerrNullGeodesic g = physics::kerrNullGeodesicFromBL(
        30.0, 0.5 * std::numbers::pi, 0.0, -std::cos(alpha), -std::sin(alpha) / 30.0, 0.0, mass,
        aTrace);
    physics::KerrGeodesicState s = g.state;
    double fate = 0.0;
    for (int step = 0; step < 20'000'000; ++step) {
      if (s.r <= rPlus * 1.001) {
        fate = -1.0;
        break;
      }
      if (s.r > K_ESCAPE && s.vr > 0.0) {
        fate = 1.0;
        break;
      }
      const double sin2 = std::sin(s.theta) * std::sin(s.theta);
      const double base = 2e-4 / (1.0 + (s.r * s.r)) * std::max(1.0, s.r / 5.0);
      const double axis = 0.02 * std::max(sin2, 1e-14) / std::max(std::abs(g.consts.lz), 1e-14);
      s = physics::kerrStepMino(s, mass, aTrace, g.consts, std::min(base, axis));
    }
    const auto k = static_cast<std::size_t>(4 * i);
    ASSERT_EQ(static_cast<double>(gpu[k]), fate) << "ray " << i << " alpha " << alpha;
    if (fate == 1.0) {
      const double nx = std::sin(s.theta) * std::cos(s.phi);
      const double ny = std::sin(s.theta) * std::sin(s.phi);
      const double nz = std::cos(s.theta);
      EXPECT_NEAR(static_cast<double>(gpu[k + 1]), nx, 3e-3) << "ray " << i;
      EXPECT_NEAR(static_cast<double>(gpu[k + 2]), ny, 3e-3) << "ray " << i;
      EXPECT_NEAR(static_cast<double>(gpu[k + 3]), nz, 3e-3) << "ray " << i;
      ++compared;
    }
  }
  EXPECT_GT(compared, K_RAYS / 16);
}

TEST_F(KerrShaderCaptureTest, InitializationIsOnShell) {
  // R(r0) = vr^2, |w|^2 = Q + Lz^2 + a^2 n_z^2, and (n x w) . z = Lz for
  // random positions, directions, and spins; float32 leaves residuals near
  // 1e-6.
  const std::vector<float> out = dispatch(K_ONSHELL_SHADER, 0.0F);
  for (int i = 0; i < K_RAYS; ++i) {
    for (int j = 0; j < 3; ++j) {
      EXPECT_LT(out[static_cast<std::size_t>((3 * i) + j)], 1e-4F) << "ray " << i << " check " << j;
    }
  }
}

TEST_F(KerrShaderCaptureTest, RendererScheduleMatchesBardeenWithinTwoPercent) {
  constexpr double K_MARGIN = 0.02;
  const GLuint program = bhtest::createComputeProgram(rendererScheduleShader());
  glUseProgram(program);
  glUniform1i(glGetUniformLocation(program, "rayCount"), K_RAYS);
  glUniform1f(glGetUniformLocation(program, "adiskEnabled"), 0.0F);
  glUniform1f(glGetUniformLocation(program, "bhDebugFlags"), 4.0F);
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 3 * K_RAYS), nullptr,
                    GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  for (const float spin : {0.0F, 0.62F, 0.9F}) {
    glUseProgram(program);
    glUniform1f(glGetUniformLocation(program, "kerrSpin"), spin);
    const std::vector<float> out =
        bhtest::runComputeProgram(program, ssbo, 3 * K_RAYS, K_RAYS / 256);
    const double bPro = equatorialCriticalImpact(static_cast<double>(spin), true);
    const double bRetro = equatorialCriticalImpact(static_cast<double>(spin), false);
    int maxStepRays = 0;
    for (int i = 0; i < K_RAYS; ++i) {
      const auto b = static_cast<double>(out[static_cast<std::size_t>(3 * i)]);
      const float fate = out[static_cast<std::size_t>((3 * i) + 1)];
      maxStepRays += out[static_cast<std::size_t>((3 * i) + 2)] > 0.5F ? 1 : 0;
      const double bc = ((b >= 0.0) == (bPro >= 0.0)) ? bPro : bRetro;
      const double ratio = b / bc;
      if (ratio > 1.0 + K_MARGIN) {
        EXPECT_EQ(fate, 1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
      } else if (ratio < 1.0 - K_MARGIN) {
        EXPECT_EQ(fate, -1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
      }
    }
    EXPECT_LT(maxStepRays, K_RAYS / 20) << "spin=" << spin;
  }
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}
