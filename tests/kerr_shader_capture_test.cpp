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
 * precision CPU integrator at a = 0.9. A camera on the spin axis, where the
 * azimuth is undefined, is checked by axial symmetry of its xz and yz fans,
 * against the CPU integrator, and against a camera 1e-4 off the axis.
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
#include <cstddef>
#include <numbers>
#include <string>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
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
    return (prograde ? 1.0 : -1.0) * 3.0 * std::numbers::sqrt3;
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

// A fan of rays from camPos (on or next to the spin axis above the hole) in
// the xz (`plane` 0) or yz (`plane` 1) plane, from straight down (alpha -> 0)
// through the transverse direction (alpha = pi/2 at i = rayCount / 2) to
// straight up. Each ray reports its fate, final direction n, and its initial
// constants and angular state.
constexpr int K_POLE_RAYS = 63;
constexpr int K_POLE_STRIDE = 12;
constexpr std::size_t K_POLE_FLOATS =
    static_cast<std::size_t>(K_POLE_STRIDE) * static_cast<std::size_t>(K_POLE_RAYS);
const char *const K_POLE_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
uniform float physicalSpin;
uniform int rayCount;
uniform int plane;
uniform float escapeR;
uniform vec3 camPos;
#include "include/kerr.glsl"
void main() {
  int i = int(gl_GlobalInvocationID.x);
  if (i >= rayCount) {
    return;
  }
  float r_s = 2.0;
  float a = 0.5 * physicalSpin * r_s;
  float alpha = 3.14159265358979 * float(i + 1) / float(rayCount + 1);
  vec3 dir = plane == 0 ? vec3(sin(alpha), 0.0, -cos(alpha)) : vec3(0.0, sin(alpha), -cos(alpha));
  float aTrace = kerrTraceSpin(a);
  KerrConsts c;
  KerrRay ray;
  kerrInitGeodesic(camPos, dir, r_s, aTrace, c, ray);
  int o = 12 * i;
  result[o + 4] = c.Q;
  result[o + 5] = c.Lz;
  result[o + 6] = ray.vr;
  result[o + 7] = ray.w.x;
  result[o + 8] = ray.w.y;
  result[o + 9] = ray.w.z;
  float rHorizon = kerrOuterHorizon(r_s, a);
  float fate = 0.0;
  for (int step = 0; step < 2000000; ++step) {
    if (ray.r <= rHorizon * 1.001) { fate = -1.0; break; }
    if (ray.r > escapeR && ray.vr > 0.0) { fate = 1.0; break; }
    kerrStep(ray, r_s, aTrace, c, 2.0e-3 / (1.0 + ray.r * ray.r) * max(1.0, ray.r / 5.0));
  }
  result[o] = fate;
  result[o + 1] = ray.n.x;
  result[o + 2] = ray.n.y;
  result[o + 3] = ray.n.z;
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

// Radiative transfer through a uniform shell r in [slabNear, slabFar] of
// source function 1 and absorption slabAlpha, traced inward from camPos along
// camDir with the production step schedule (bhAdaptiveStep) at stepSize,
// the production path length (kerrAffineStep), and rteStepVec3. Declarations
// come from shader/geodesic_trace.comp as in rendererScheduleShader. Reports
// intensity, transmittance, and the number of steps inside the shell.
std::string rteSlabShader() {
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  return comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
uniform float slabStepSize;
uniform float slabNear;
uniform float slabFar;
uniform float slabAlpha;
uniform vec3 slabCamPos;
uniform vec3 slabCamDir;
void main() {
  float r_s = 2.0;
  float a = 0.5 * kerrSpin * r_s;
  float rHorizon = kerrOuterHorizon(r_s, a);
  float aTrace = kerrTraceSpin(a);
  KerrConsts c;
  KerrRay kr;
  kerrInitGeodesic(slabCamPos, normalize(slabCamDir), r_s, aTrace, c, kr);
  float transmit = 1.0;
  vec3 accum = vec3(0.0);
  int inside = 0;
  for (int step = 0; step < 1000000; ++step) {
    if (kr.r < 0.5 * slabNear || kr.r <= rHorizon) {
      break;
    }
    KerrRay before = kr;
    float dlam = bhAdaptiveStep(kr.r, r_s, rHorizon, slabStepSize);
    kerrStep(kr, r_s, aTrace, c, dlam);
    if (kr.r >= slabNear && kr.r <= slabFar) {
      float ds = kerrAffineStep(before, kr, aTrace, dlam);
      accum += rteStepVec3(vec3(1.0), slabAlpha, slabAlpha, ds, transmit);
      ++inside;
    }
  }
  result[0] = accum.x;
  result[1] = transmit;
  result[2] = float(inside);
}
)";
}

// bhTraceGeodesic with the renderer's default schedule (stepSize 0.1, 300
// steps, depthFar 100) for a fan of equatorial rays from (30, 0, 0) with
// |alpha| <= 0.3, under the scene toggles gravitationalLensing and
// renderBlackHole. Reports fate (-1 captured, 1 escaped), the straight-line
// impact parameter 30 sin|alpha|, and the escape direction.
std::string sceneToggleShader() {
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
  HitResult hit = bhTraceGeodesic(ray, 2.0, 100.0, 300, 0.1);
  result[5 * i] = hit.hitHorizon ? -1.0 : 1.0;
  result[5 * i + 1] = 30.0 * abs(sin(alpha));
  result[5 * i + 2] = hit.escapedDir.x;
  result[5 * i + 3] = hit.escapedDir.y;
  result[5 * i + 4] = hit.escapedDir.z;
}
)";
}

// A b = 0 ray from (30, 0, 0) into the hole through bhTraceGeodesic +
// bhShadeHit and through bhTraceGeodesicRTE (no disk), with the Hawking glow
// uniforms of shader/geodesic_trace.comp. Reports both colors, the capture
// flag, and hawkingThermalGlow at the capture radius.
std::string hawkingShadeShader() {
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  return comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
void main() {
  Ray ray;
  ray.position = vec3(30.0, 0.0, 0.0);
  ray.velocity = vec3(-1.0, 0.0, 0.0);
  ray.affineParameter = 0.0;
  HitResult hit = bhTraceGeodesic(ray, 2.0, 100.0, 300, 0.1);
  vec3 shaded = bhShadeHit(hit, ray.position, 2.0).rgb;
  vec3 terminalPos;
  vec3 rte = bhTraceGeodesicRTE(ray, 2.0, 100.0, 300, 0.1, 0.5, terminalPos).rgb;
  vec3 expected = hawkingThermalGlow(blackHoleMass, length(hit.hitPoint), 2.0, hawkingTempScale,
                                     hawkingGlowIntensity, hawkingTempLUT, hawkingSpectrumLUT,
                                     useHawkingLUTs);
  result[0] = hit.hitHorizon ? 1.0 : 0.0;
  result[1] = shaded.r;
  result[2] = shaded.g;
  result[3] = shaded.b;
  result[4] = rte.r;
  result[5] = expected.r;
  result[6] = expected.g;
  result[7] = expected.b;
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
    std::vector<float> out = bhtest::runComputeProgram(
        program, ssbo, static_cast<std::size_t>(4) * K_RAYS, K_RAYS / K_LOCAL);
    glDeleteBuffers(1, &ssbo);
    glDeleteProgram(program);
    return out;
  }

  static std::vector<float> dispatchPole(float physicalSpin, int plane, float escapeR,
                                         float camX, float camY) {
    const GLuint program = bhtest::createComputeProgram(K_POLE_SHADER);
    glUseProgram(program);
    glUniform1f(glGetUniformLocation(program, "physicalSpin"), physicalSpin);
    glUniform1i(glGetUniformLocation(program, "rayCount"), K_POLE_RAYS);
    glUniform1i(glGetUniformLocation(program, "plane"), plane);
    glUniform1f(glGetUniformLocation(program, "escapeR"), escapeR);
    glUniform3f(glGetUniformLocation(program, "camPos"), camX, camY, 30.0F);
    GLuint ssbo = 0;
    glCreateBuffers(1, &ssbo);
    glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * K_POLE_FLOATS), nullptr,
                      GL_DYNAMIC_DRAW);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
    std::vector<float> out = bhtest::runComputeProgram(program, ssbo, K_POLE_FLOATS, 1);
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
    std::vector<float> out = bhtest::runComputeProgram(
        program, ssbo, static_cast<std::size_t>(3) * K_RAYS, K_RAYS / K_LOCAL);
    glDeleteBuffers(1, &ssbo);
    glDeleteProgram(program);
    return out;
  }
};

bhtest::HiddenGlContext *KerrShaderCaptureTest::context = nullptr;

TEST_F(KerrShaderCaptureTest, CaptureEdgesMatchBardeenWithPhysicalHandedness) {
  constexpr double kMargin = 0.005;
  for (const float spin : {0.0F, 0.01F, 0.5F, 0.9F, 0.99F, -0.9F}) {
    const std::vector<float> out = dispatch(K_SHADER, spin);
    const double bPro = equatorialCriticalImpact(static_cast<double>(spin), true);
    const double bRetro = equatorialCriticalImpact(static_cast<double>(spin), false);
    int checked = 0;
    for (int i = 0; i < K_RAYS; ++i) {
      const auto b = static_cast<double>(out[2 * static_cast<std::size_t>(i)]);
      const float fate = out[(2 * static_cast<std::size_t>(i)) + 1];
      const double bc = ((b >= 0.0) == (bPro >= 0.0)) ? bPro : bRetro;
      const double ratio = b / bc;
      if (ratio > 1.0 + kMargin) {
        EXPECT_EQ(fate, 1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
        ++checked;
      } else if (ratio < 1.0 - kMargin) {
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
    const auto k = 4 * static_cast<std::size_t>(i);
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
  constexpr float kSpin = 0.9F;
  constexpr double kEscape = 2000.0;
  const std::vector<float> gpu = dispatchFan(kSpin, 1, static_cast<float>(kEscape));
  const double mass = physics::C2 / physics::G;
  const double aTrace = -static_cast<double>(kSpin);
  const double rPlus = 1.0 + std::sqrt(1.0 - (aTrace * aTrace));
  int compared = 0;
  for (int i = 0; i < K_RAYS; i += 4) {
    const double alpha =
        0.3 * ((2.0 * (static_cast<double>(i) + 0.5) / static_cast<double>(K_RAYS)) - 1.0);
    // Camera on +x at theta = pi/2, phi = 0: e_r = x, e_theta = -z, e_phi = y.
    const physics::KerrNullGeodesic g = physics::kerrNullGeodesicFromBL(
        30.0, 0.5 * std::numbers::pi, 0.0, -std::cos(alpha), -std::sin(alpha) / 30.0, 0.0, mass,
        aTrace);
    physics::KerrGeodesicState s = g.state;
    double fate = 0.0;
    for (int step = 0; step < 20'000'000; ++step) {
      if (s.r <= rPlus * 1.001) {
        fate = -1.0;
        break;
      }
      if (s.r > kEscape && s.vr > 0.0) {
        fate = 1.0;
        break;
      }
      const double sin2 = std::sin(s.theta) * std::sin(s.theta);
      const double base = 2e-4 / (1.0 + (s.r * s.r)) * std::max(1.0, s.r / 5.0);
      const double axis = 0.02 * std::max(sin2, 1e-14) / std::max(std::abs(g.consts.lz), 1e-14);
      s = physics::kerrStepMino(s, mass, aTrace, g.consts, std::min(base, axis));
    }
    const auto k = 4 * static_cast<std::size_t>(i);
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
  constexpr double kMargin = 0.02;
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
    const std::vector<float> out = bhtest::runComputeProgram(
        program, ssbo, static_cast<std::size_t>(3) * K_RAYS, K_RAYS / 256);
    const double bPro = equatorialCriticalImpact(static_cast<double>(spin), true);
    const double bRetro = equatorialCriticalImpact(static_cast<double>(spin), false);
    int maxStepRays = 0;
    for (int i = 0; i < K_RAYS; ++i) {
      const auto b = static_cast<double>(out[3 * static_cast<std::size_t>(i)]);
      const float fate = out[(3 * static_cast<std::size_t>(i)) + 1];
      maxStepRays += out[(3 * static_cast<std::size_t>(i)) + 2] > 0.5F ? 1 : 0;
      const double bc = ((b >= 0.0) == (bPro >= 0.0)) ? bPro : bRetro;
      const double ratio = b / bc;
      if (ratio > 1.0 + kMargin) {
        EXPECT_EQ(fate, 1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
      } else if (ratio < 1.0 - kMargin) {
        EXPECT_EQ(fate, -1.0F) << "spin=" << spin << " b=" << b << " b_c=" << bc;
      }
    }
    EXPECT_LT(maxStepRays, K_RAYS / 20) << "spin=" << spin;
  }
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

TEST_F(KerrShaderCaptureTest, PixelRightOfCenterMapsAlongCameraRight) {
  // bhRayDir maps screen offsets onto the (right, up, forward) columns of the
  // camera basis without mirroring: a pixel right of and above center yields
  // positive right and up components.
  const GLuint program = bhtest::createComputeProgram(R"(
#version 460 core
layout(local_size_x = 1) in;
layout(std430, binding = 0) buffer Output { float result[]; };
#include "include/interop_raygen.glsl"
void main() {
  mat3 basis = mat3(vec3(1.0, 0.0, 0.0), vec3(0.0, 1.0, 0.0), vec3(0.0, 0.0, 1.0));
  vec3 d = bhRayDir(vec2(300.0, 260.0), vec2(400.0, 400.0), 1.0, basis);
  result[0] = d.x;
  result[1] = d.y;
  result[2] = d.z;
}
)");
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 3), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
  const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 3);
  EXPECT_GT(out[0], 0.0F);
  EXPECT_GT(out[1], 0.0F);
  EXPECT_GT(out[2], 0.0F);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

namespace {

struct PoleRay {
  float fate;
  float nx, ny, nz;
  float q, lz, vr;
  float wx, wy, wz;
};

PoleRay poleRay(const std::vector<float> &out, int i) {
  const std::size_t o = static_cast<std::size_t>(K_POLE_STRIDE) * static_cast<std::size_t>(i);
  return {.fate = out.at(o),
          .nx = out.at(o + 1),
          .ny = out.at(o + 2),
          .nz = out.at(o + 3),
          .q = out.at(o + 4),
          .lz = out.at(o + 5),
          .vr = out.at(o + 6),
          .wx = out.at(o + 7),
          .wy = out.at(o + 8),
          .wz = out.at(o + 9)};
}

double poleAlpha(int i) {
  return std::numbers::pi * static_cast<double>(i + 1) / static_cast<double>(K_POLE_RAYS + 1);
}

// Initial state of an xz-fan ray and its yz twin: Lz = 0, equal Carter
// constants, and |w| = p_theta ~ r sin(alpha) for both.
void expectAxialInit(const PoleRay &x, const PoleRay &y, double alpha, const std::string &where) {
  const double transverse = 30.0 * std::sin(alpha);
  EXPECT_EQ(x.lz, 0.0F) << where;
  EXPECT_EQ(y.lz, 0.0F) << where;
  EXPECT_GT(std::hypot(x.wx, x.wy, x.wz), 0.9 * transverse) << where;
  EXPECT_GT(std::hypot(y.wx, y.wy, y.wz), 0.9 * transverse) << where;
  EXPECT_NEAR(y.q, x.q, 1e-5F * std::max(1.0F, std::abs(x.q))) << where;
}

// The yz fan is the xz fan rotated by 90 degrees about z: escaped directions
// are related by (x, y, z) -> (-y, x, z). Returns the escaped count.
int expectAxialRotation(const std::vector<float> &xs, const std::vector<float> &ys,
                        float spin) {
  int escaped = 0;
  for (int i = 0; i < K_POLE_RAYS; ++i) {
    const PoleRay x = poleRay(xs, i);
    const PoleRay y = poleRay(ys, i);
    const std::string where = "spin=" + std::to_string(spin) + " ray " + std::to_string(i);
    expectAxialInit(x, y, poleAlpha(i), where);
    EXPECT_EQ(y.fate, x.fate) << where;
    if (x.fate == 1.0F && y.fate == 1.0F) {
      EXPECT_NEAR(y.nx, -x.ny, 2e-3F) << where;
      EXPECT_NEAR(y.ny, x.nx, 2e-3F) << where;
      EXPECT_NEAR(y.nz, x.nz, 2e-3F) << where;
      ++escaped;
    }
  }
  return escaped;
}

struct ReferenceRay {
  double fate{0.0};
  physics::KerrGeodesicState state{};
};

// Double-precision trace of the time-reversed ray (spin aTrace) from
// (r, theta, phi) = (30, 0, phi0) with k^r = -cos(alpha), k^theta =
// sin(alpha) / r, k^phi = 0, to r = escapeR.
ReferenceRay tracePoleReference(double alpha, double phi0, double aTrace, double escapeR) {
  const double mass = physics::C2 / physics::G;
  const double rPlus = 1.0 + std::sqrt(1.0 - (aTrace * aTrace));
  const physics::KerrNullGeodesic g = physics::kerrNullGeodesicFromBL(
      30.0, 0.0, phi0, -std::cos(alpha), std::sin(alpha) / 30.0, 0.0, mass, aTrace);
  physics::KerrGeodesicState s = g.state;
  for (int step = 0; step < 20'000'000; ++step) {
    if (s.r <= rPlus * 1.001) {
      return {.fate = -1.0, .state = s};
    }
    if (s.r > escapeR && s.vr > 0.0) {
      return {.fate = 1.0, .state = s};
    }
    s = physics::kerrStepMino(s, mass, aTrace, g.consts,
                              2e-4 / (1.0 + (s.r * s.r)) * std::max(1.0, s.r / 5.0));
  }
  return {.fate = 0.0, .state = s};
}

// Compares a GPU pole fan against the reference; returns the escaped count.
int expectPoleFanMatchesReference(const std::vector<float> &gpu, int plane, double aTrace,
                                  double escapeR) {
  const double phi0 = plane == 0 ? 0.0 : 0.5 * std::numbers::pi;
  int compared = 0;
  for (int i = 0; i < K_POLE_RAYS; ++i) {
    const ReferenceRay ref = tracePoleReference(poleAlpha(i), phi0, aTrace, escapeR);
    const PoleRay p = poleRay(gpu, i);
    const std::string where = "plane " + std::to_string(plane) + " ray " + std::to_string(i);
    EXPECT_EQ(static_cast<double>(p.fate), ref.fate) << where;
    if (ref.fate == 1.0 && p.fate == 1.0F) {
      const physics::KerrGeodesicState &s = ref.state;
      EXPECT_NEAR(p.nx, std::sin(s.theta) * std::cos(s.phi), 3e-3) << where;
      EXPECT_NEAR(p.ny, std::sin(s.theta) * std::sin(s.phi), 3e-3) << where;
      EXPECT_NEAR(p.nz, std::cos(s.theta), 3e-3) << where;
      ++compared;
    }
  }
  return compared;
}

// A camera 1e-4 off the axis tilts e_r by 1e-4 / r, which moves vr and Q
// (scale r^2) by about 1e-4 r and w (scale r) by about 1e-4, so the
// tolerances are 1e-4 of each scale at r = 30.
void expectContinuous(const std::vector<float> &axis, const std::vector<float> &off,
                      const std::string &label) {
  constexpr float radius = 30.0F;
  constexpr float tol = 1e-4F;
  for (int i = 0; i < K_POLE_RAYS; ++i) {
    const PoleRay p = poleRay(axis, i);
    const PoleRay o = poleRay(off, i);
    const std::string where = label + " ray " + std::to_string(i);
    EXPECT_NEAR(o.q, p.q, tol * radius * radius) << where;
    EXPECT_NEAR(o.vr, p.vr, tol * radius * radius) << where;
    EXPECT_NEAR(o.lz, 0.0F, tol * radius) << where;
    EXPECT_NEAR(o.wx, p.wx, tol * radius) << where;
    EXPECT_NEAR(o.wy, p.wy, tol * radius) << where;
    EXPECT_NEAR(o.wz, p.wz, tol * radius) << where;
  }
}

} // namespace

TEST_F(KerrShaderCaptureTest, PoleCameraFansAreRelatedByAxialRotation) {
  // A camera exactly on the spin axis: Kerr is axisymmetric, so the yz fan is
  // the xz fan rotated by 90 degrees about z. A pole start that zeroes w
  // traces the yz fan radially instead.
  for (const float spin : {0.0F, 0.9F}) {
    const std::vector<float> xs = dispatchPole(spin, 0, 200.0F, 0.0F, 0.0F);
    const std::vector<float> ys = dispatchPole(spin, 1, 200.0F, 0.0F, 0.0F);
    EXPECT_GT(expectAxialRotation(xs, ys, spin), K_POLE_RAYS / 2) << "spin=" << spin;
  }
}

TEST_F(KerrShaderCaptureTest, PoleCameraMatchesDoublePrecisionReference) {
  // On the axis the Boyer-Lindquist azimuth is free: the reference starts at
  // theta = 0 with phi chosen so e_theta = (cos phi, sin phi, 0) carries the
  // transverse direction, and integrates with physics::kerrStepMino in double
  // to r = 2000, where the Kerr-Schild and Boyer-Lindquist azimuths agree to
  // about a / r.
  constexpr float spin = 0.9F;
  constexpr double escapeR = 2000.0;
  for (const int plane : {0, 1}) {
    const std::vector<float> gpu =
        dispatchPole(spin, plane, static_cast<float>(escapeR), 0.0F, 0.0F);
    EXPECT_GT(expectPoleFanMatchesReference(gpu, plane, -static_cast<double>(spin), escapeR),
              K_POLE_RAYS / 2)
        << "plane " << plane;
  }
}

TEST_F(KerrShaderCaptureTest, PoleStartIsContinuousWithOffAxisStart) {
  // A camera 1e-4 off the axis builds w from p_theta e_theta + (Lz / sin)
  // e_phi through the generic branch; its constants and angular state must
  // match the on-axis start.
  for (const float spin : {0.0F, 0.9F}) {
    for (const int plane : {0, 1}) {
      const std::vector<float> axis = dispatchPole(spin, plane, 60.0F, 0.0F, 0.0F);
      const std::string label = "spin=" + std::to_string(spin) + " plane=" + std::to_string(plane);
      expectContinuous(axis, dispatchPole(spin, plane, 60.0F, 1e-4F, 0.0F), label + " dx");
      expectContinuous(axis, dispatchPole(spin, plane, 60.0F, 0.0F, 1e-4F), label + " dy");
    }
  }
}

TEST_F(KerrShaderCaptureTest, RadiativeTransferIntegratesAffinePathLength) {
  // A uniform shell 300 <= r <= 700 (M = 1) with source function 1 and
  // absorption 1/400 per unit length: a ray crossing it far from the hole
  // along a nearly straight path of geometric length L must reach
  // I = 1 - exp(-L / 400) and T = exp(-L / 400), at two step sizes a factor 4
  // apart. On the spin axis the affine length equals Delta r exactly; the
  // equatorial ray at impact parameter 5 crosses sqrt(700^2 - 25) -
  // sqrt(300^2 - 25). Emission sampled at step end points misplaces at most
  // one step per shell boundary, 0.5 stepSize r ~ 3.5 of L = 400 at the
  // coarser step, so the tolerance is 2%. Passing the Mino increment as the
  // length gives L ~ 1/300 - 1/700 and I ~ 5e-6.
  constexpr float rNear = 300.0F;
  constexpr float rFar = 700.0F;
  constexpr double alpha = 1.0 / 400.0;
  const GLuint program = bhtest::createComputeProgram(rteSlabShader());
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 3), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  struct Ray {
    float x, y, z, dx, dy, dz;
    double length;
  };
  const double equatorialLength =
      std::sqrt((700.0 * 700.0) - 25.0) - std::sqrt((300.0 * 300.0) - 25.0);
  for (const Ray ray : {Ray{.x = 0.0F, .y = 0.0F, .z = 1000.0F, .dx = 0.0F, .dy = 0.0F,
                            .dz = -1.0F, .length = 400.0},
                        Ray{.x = 1000.0F, .y = 0.0F, .z = 0.0F, .dx = -1000.0F, .dy = 5.0F,
                            .dz = 0.0F, .length = equatorialLength}}) {
    const double intensity = 1.0 - std::exp(-alpha * ray.length);
    const double transmit = std::exp(-alpha * ray.length);
    for (const float stepSize : {0.01F, 0.0025F}) {
      glUseProgram(program);
      glUniform1f(glGetUniformLocation(program, "kerrSpin"), 0.9F);
      glUniform1f(glGetUniformLocation(program, "slabStepSize"), stepSize);
      glUniform1f(glGetUniformLocation(program, "slabNear"), rNear);
      glUniform1f(glGetUniformLocation(program, "slabFar"), rFar);
      glUniform1f(glGetUniformLocation(program, "slabAlpha"), static_cast<float>(alpha));
      glUniform3f(glGetUniformLocation(program, "slabCamPos"), ray.x, ray.y, ray.z);
      glUniform3f(glGetUniformLocation(program, "slabCamDir"), ray.dx, ray.dy, ray.dz);
      const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 3);
      const std::string where =
          "camera z=" + std::to_string(ray.z) + " stepSize=" + std::to_string(stepSize);
      EXPECT_NEAR(out.at(0), intensity, 0.02 * intensity) << where;
      EXPECT_NEAR(out.at(1), transmit, 0.02 * transmit) << where;
      EXPECT_GT(out.at(2), 50.0F) << where;
    }
  }
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

namespace {

struct ToggleRay {
  double fate;
  double impact;
  double dx, dy, dz;
};

std::vector<ToggleRay> traceSceneToggles(GLuint program, GLuint ssbo, float lensing,
                                         float holeRendered) {
  glUseProgram(program);
  glUniform1i(glGetUniformLocation(program, "rayCount"), K_RAYS);
  glUniform1f(glGetUniformLocation(program, "kerrSpin"), 0.9F);
  glUniform1f(glGetUniformLocation(program, "adiskEnabled"), 0.0F);
  glUniform1f(glGetUniformLocation(program, "gravitationalLensing"), lensing);
  glUniform1f(glGetUniformLocation(program, "renderBlackHole"), holeRendered);
  const std::vector<float> out =
      bhtest::runComputeProgram(program, ssbo, static_cast<std::size_t>(5) * K_RAYS, K_RAYS / 256);
  std::vector<ToggleRay> rays;
  for (std::size_t k = 0; k + 4 < out.size(); k += 5) {
    rays.push_back({.fate = static_cast<double>(out.at(k)),
                    .impact = static_cast<double>(out.at(k + 1)),
                    .dx = static_cast<double>(out.at(k + 2)),
                    .dy = static_cast<double>(out.at(k + 3)),
                    .dz = static_cast<double>(out.at(k + 4))});
  }
  return rays;
}

double rayAlpha(int i) {
  return 0.3 * ((2.0 * (static_cast<double>(i) + 0.5) / static_cast<double>(K_RAYS)) - 1.0);
}

// Angle between an escape direction and the camera direction of ray i.
double deflection(const ToggleRay &ray, int i) {
  const double alpha = rayAlpha(i);
  const double cosAngle = (-std::cos(alpha) * ray.dx) + (std::sin(alpha) * ray.dy);
  const double norm = std::hypot(ray.dx, ray.dy, ray.dz);
  return std::acos(std::clamp(cosAngle / norm, -1.0, 1.0));
}

// Straight rays: captured below the horizon radius, undeflected above it
// (the flat-space Mino leapfrog at stepSize 0.1 bends them by at most ~6e-3
// rad). Returns the captured count.
int expectStraightCapture(const std::vector<ToggleRay> &rays, double rPlus) {
  int captured = 0;
  for (int i = 0; i < K_RAYS; ++i) {
    const ToggleRay &ray = rays.at(static_cast<std::size_t>(i));
    const std::string where = "lensing off, ray " + std::to_string(i);
    if (ray.impact < 0.98 * rPlus) {
      EXPECT_EQ(ray.fate, -1.0) << where << " b=" << ray.impact;
      ++captured;
    } else if (ray.impact > 1.02 * rPlus) {
      EXPECT_EQ(ray.fate, 1.0) << where << " b=" << ray.impact;
      EXPECT_LT(deflection(ray, i), 1e-2) << where;
    }
  }
  return captured;
}

} // namespace

TEST_F(KerrShaderCaptureTest, SceneTogglesStraightenRaysAndRemoveTheHole) {
  // gravitationalLensing = 0 traces straight rays that the horizon
  // (r+ = 1.436 M at a = 0.9) still captures: capture exactly when the
  // impact parameter is below r+, and escaped rays leave along the camera
  // direction. renderBlackHole = 0 removes the hole: nothing is captured,
  // the b = 0 ray included, and every ray keeps its direction. With both on
  // the same fan is lensed: rays at b ~ 6 M deflect by more than a radian.
  const double rPlus = 1.0 + std::sqrt(1.0 - (0.9 * 0.9));
  const GLuint program = bhtest::createComputeProgram(sceneToggleShader());
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 5 * K_RAYS), nullptr,
                    GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);

  EXPECT_GT(expectStraightCapture(traceSceneToggles(program, ssbo, 0.0F, 1.0F), rPlus), 0);

  const std::vector<ToggleRay> noHole = traceSceneToggles(program, ssbo, 1.0F, 0.0F);
  for (int i = 0; i < K_RAYS; ++i) {
    const ToggleRay &ray = noHole.at(static_cast<std::size_t>(i));
    EXPECT_EQ(ray.fate, 1.0) << "no hole, ray " << i;
    EXPECT_LT(deflection(ray, i), 1e-5) << "no hole, ray " << i;
  }

  const std::vector<ToggleRay> lensed = traceSceneToggles(program, ssbo, 1.0F, 1.0F);
  int strong = 0;
  for (int i = 0; i < K_RAYS; ++i) {
    const ToggleRay &ray = lensed.at(static_cast<std::size_t>(i));
    if (ray.fate == 1.0 && ray.impact < 6.0 && deflection(ray, i) > 1.0) {
      ++strong;
    }
  }
  EXPECT_GT(strong, 0);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

TEST_F(KerrShaderCaptureTest, HawkingGlowShadesCapturedRays) {
  // The physical traces add the Hawking thermal glow to captured rays, as the
  // legacy tracer does at its capture point: with hawkingGlowEnabled the
  // captured color is hawkingThermalGlow at the capture radius (direct
  // Planck evaluation, primordial mass 5e14 g, T_H ~ 2e5 K), and without it
  // the horizon stays black.
  const GLuint program = bhtest::createComputeProgram(hawkingShadeShader());
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 8), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  glUseProgram(program);
  glUniform1f(glGetUniformLocation(program, "adiskEnabled"), 0.0F);
  glUniform1f(glGetUniformLocation(program, "useHawkingLUTs"), 0.0F);
  glUniform1f(glGetUniformLocation(program, "blackHoleMass"), 5.0e14F);
  for (const float enabled : {1.0F, 0.0F}) {
    glUseProgram(program);
    glUniform1f(glGetUniformLocation(program, "hawkingGlowEnabled"), enabled);
    const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 8);
    const std::string where = "hawkingGlowEnabled=" + std::to_string(enabled);
    ASSERT_EQ(out.at(0), 1.0F) << where;
    for (std::size_t k = 0; k < 3; ++k) {
      const float expected = enabled > 0.5F ? out.at(5 + k) : 0.0F;
      EXPECT_TRUE(std::isfinite(out.at(1 + k))) << where;
      EXPECT_NEAR(out.at(1 + k), expected, 1e-5F * std::max(1.0F, std::abs(expected))) << where;
    }
    EXPECT_NEAR(out.at(4), enabled > 0.5F ? out.at(5) : 0.0F,
                1e-5F * std::max(1.0F, std::abs(out.at(5))))
        << where;
    if (enabled > 0.5F) {
      EXPECT_GT(out.at(5) + out.at(6) + out.at(7), 0.0F) << where;
    }
  }
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}
