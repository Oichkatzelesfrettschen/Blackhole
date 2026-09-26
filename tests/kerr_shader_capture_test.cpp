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
 * Falsifiers: an lz^2/sin^2 polar potential shortens R by Delta lz^2 and
 * moves both edges inward; a first-order step on sqrt(max(R, 0)) stalls
 * deflected rays at their turning point so none escape; tracing the emitted
 * rather than the arriving photon swaps the prograde and retrograde edges;
 * an unprojected float32 leapfrog loses vr^2 = R over the r^2 dynamic range
 * and bounces near-radial rays back out.
 * Skips without a GL 4.6 context.
 */

#include <cmath>
#include <string>
#include <vector>

#include <gtest/gtest.h>

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
    glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 2 * K_RAYS), nullptr,
                      GL_DYNAMIC_DRAW);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
    std::vector<float> out =
        bhtest::runComputeProgram(program, ssbo, 2 * K_RAYS, K_RAYS / K_LOCAL);
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

// Critical impact parameter for rays with Lz = 0 (motion in a meridian
// plane): the spherical photon orbit with xi(r) = 0 (Bardeen 1973, M = 1),
// seen from the equator at b = sqrt(eta(r)).
double polarCriticalImpact(double a) {
  const auto xi = [a](double r) {
    const double delta = (r * r) - (2.0 * r) + (a * a);
    return (((r * r) + (a * a)) / a) - ((4.0 * r * delta) / (a * ((2.0 * r) - 2.0)));
  };
  double lo = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(-a)));
  double hi = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(a)));
  for (int i = 0; i < 200; ++i) {
    const double mid = 0.5 * (lo + hi);
    ((xi(lo) > 0.0) == (xi(mid) > 0.0) ? lo : hi) = mid;
  }
  const double r = 0.5 * (lo + hi);
  const double delta = (r * r) - (2.0 * r) + (a * a);
  const double dp = (2.0 * r) - 2.0;
  const double eta = (16.0 * r * r * delta / (dp * dp)) - (a * a);
  return std::sqrt(eta);
}

const char *const K_POLAR_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
uniform float physicalSpin;
uniform int rayCount;
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
  vec3 dir = vec3(-cos(alpha), 0.0, sin(alpha));
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
  result[2 * i] = sqrt(max(c.Q, 0.0));
  result[2 * i + 1] = fate;
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
  result[2 * i] = abs(R - ray.vr * ray.vr) / max(P * P, 1.0);
  float T = kerrPolarPotentialMu(ray.mu, a, c);
  result[2 * i + 1] = abs(T - ray.vmu * ray.vmu) / max(abs(c.Q) + a * a + c.Lz * c.Lz, 1.0);
}
)";

} // namespace

TEST_F(KerrShaderCaptureTest, PolarPlaneRaysCrossTheAxisAndMatchCriticalCurve) {
  // Lz = 0 rays wind over the poles near the photon orbit, so the mu =
  // cos(theta) polar motion must carry r and mu through the axis. Edges at
  // sqrt(eta_c) with xi_c = 0; the 0.5% margin covers float32 initialization.
  // The fate is independent of phi, so this gates r and mu, not the phi + pi
  // continuation across the axis.
  constexpr double K_MARGIN = 0.005;
  for (const float spin : {0.3F, 0.9F}) {
    const std::vector<float> out = dispatch(K_POLAR_SHADER, spin);
    const double bc = polarCriticalImpact(static_cast<double>(spin));
    int checked = 0;
    for (int i = 0; i < K_RAYS; ++i) {
      const auto b = static_cast<double>(out[static_cast<std::size_t>(2 * i)]);
      const float fate = out[static_cast<std::size_t>((2 * i) + 1)];
      if (b > bc * (1.0 + K_MARGIN)) {
        EXPECT_EQ(fate, 1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
        ++checked;
      } else if (b < bc * (1.0 - K_MARGIN)) {
        EXPECT_EQ(fate, -1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
        ++checked;
      }
    }
    EXPECT_GT(checked, K_RAYS / 2) << "spin=" << spin;
  }
}

TEST_F(KerrShaderCaptureTest, InitializationIsOnShell) {
  // R(r0) = vr^2 and Theta_mu(mu0) = vmu^2 for random positions, directions,
  // and spins; float32 leaves relative residuals near 1e-6.
  const std::vector<float> out = dispatch(K_ONSHELL_SHADER, 0.0F);
  for (int i = 0; i < K_RAYS; ++i) {
    EXPECT_LT(out[static_cast<std::size_t>(2 * i)], 1e-4F) << "ray " << i;
    EXPECT_LT(out[static_cast<std::size_t>((2 * i) + 1)], 1e-4F) << "ray " << i;
  }
}
