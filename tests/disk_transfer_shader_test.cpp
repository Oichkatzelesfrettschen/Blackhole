/**
 * @file disk_transfer_shader_test.cpp
 * @brief Shipped disk_transfer.glsl against the double-precision C++.
 *
 * A compute dispatch evaluates dtPageThorneShape, dtDiskTransferG and
 * dtBlackbodyChroma from shader/include/disk_transfer.glsl over a grid of
 * spins (including a retrograde disk), radii from 1.1 to 20 r_isco, photon
 * lambda of 0 and +-0.8 r, and three temperatures. Each result must match
 * physics::pageThorneFluxShape, physics::diskTransferG and
 * physics::blackbodyChromaLinearSrgb evaluated at the shader's own float
 * radius. Falsifiers: a transcription slip in a root coefficient, a wrong
 * sign of a in u^t or Omega, or a swapped sRGB matrix row.
 *
 * The traced-ray cases run the shipped bhTraceGeodesic + bhShadeHit,
 * bhTraceGeodesicRTE and bhTraceGeodesicStokes (interop_trace.glsl, with the
 * declarations of geodesic_trace.comp) for a mirror pair of camera rays that
 * land on the approaching and receding sides of the disk; see
 * support/kerr_disk_reference.h for the geometry and the double-precision
 * reference trace.
 * Skips without a GL 4.6 context.
 */

#include <array>
#include <cmath>
#include <cstddef>
#include <numbers>
#include <string>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <gtest/gtest.h>

#include "physics/disk_transfer.h"
#include "physics/page_thorne.h"
#include "support/gl_compute_harness.h"
#include "support/kerr_disk_reference.h"

using namespace gl;

namespace {

constexpr std::size_t K_CASES = 60; // 5 spins x 4 radii x 3 lambdas
constexpr std::size_t K_STRIDE = 6;
constexpr std::array<float, 5> K_SPINS = {0.0F, 0.5F, 0.9F, 0.998F, -0.5F};
constexpr std::array<float, 3> K_TEMPERATURES = {3000.0F, 6500.0F, 12000.0F};

const char *const K_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
#include "include/disk_transfer.glsl"
const float SPINS[5] = float[5](0.0, 0.5, 0.9, 0.998, -0.5);
const float RATIOS[4] = float[4](1.1, 1.6, 4.0, 20.0);
const float LAMBDAS[3] = float[3](0.0, 0.8, -0.8);
const float TEMPS[3] = float[3](3000.0, 6500.0, 12000.0);
void main() {
  int i = int(gl_GlobalInvocationID.x);
  if (i >= 60) {
    return;
  }
  float a = SPINS[i / 12];
  float r = RATIOS[(i / 3) % 4] * isco_radius(a);
  float lambda = LAMBDAS[i % 3] * r;
  vec3 chroma = dtBlackbodyChroma(TEMPS[i % 3]);
  result[6 * i + 0] = r;
  result[6 * i + 1] = dtPageThorneShape(r, a);
  result[6 * i + 2] = dtDiskTransferG(r, a, lambda);
  result[6 * i + 3] = chroma.r;
  result[6 * i + 4] = chroma.g;
  result[6 * i + 5] = chroma.b;
}
)";

class DiskTransferShaderTest : public ::testing::Test {
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
};

bhtest::HiddenGlContext *DiskTransferShaderTest::context = nullptr;

TEST_F(DiskTransferShaderTest, MatchesDoublePrecisionReference) {
  const GLuint program = bhtest::createComputeProgram(K_SHADER);
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * K_STRIDE * K_CASES), nullptr,
                    GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
  const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, K_STRIDE * K_CASES, 1);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);

  constexpr std::array<double, 3> lambdas = {0.0, 0.8, -0.8};
  for (std::size_t i = 0; i < K_CASES; ++i) {
    const auto at = [&](std::size_t k) { return static_cast<double>(out.at((K_STRIDE * i) + k)); };
    const auto a = static_cast<double>(K_SPINS.at(i / 12));
    const double r = at(0);
    const double lambda = lambdas.at(i % 3) * r;

    // Float cancellation in the logarithmic bracket grows toward the
    // zero-torque edge; 1.1 r_isco is the closest radius sampled.
    const double shape = physics::pageThorneFluxShape(r, a);
    EXPECT_NEAR(at(1) / shape, 1.0, 2e-3) << "a=" << a << " r=" << r;

    const double g = physics::diskTransferG(r, a, lambda);
    EXPECT_NEAR(at(2) / g, 1.0, 1e-5) << "a=" << a << " r=" << r << " lambda=" << lambda;

    const std::array<double, 3> rgb =
        physics::blackbodyChromaLinearSrgb(static_cast<double>(K_TEMPERATURES.at(i % 3)));
    for (std::size_t c = 0; c < 3; ++c) {
      EXPECT_NEAR(at(3 + c), rgb.at(c), 1e-4) << "channel " << c;
    }
  }
}

// Shipped trace path for the two rays of a mirror pair, through the
// declarations of shader/geodesic_trace.comp (its main() is replaced). Per
// ray: disk hit flag, hit radius |xy|, photonLambda, then the rgb of
// bhShadeHit, bhTraceGeodesicRTE and bhTraceGeodesicStokes.
constexpr std::size_t K_TRACE_STRIDE = 12;

std::string traceShader() {
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  return comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
uniform vec3 rayOrigin;
uniform vec3 rayDirs[2];
uniform int traceSteps;
uniform float traceStepSize;
void main() {
  int i = int(gl_LocalInvocationIndex);
  if (i >= 2) {
    return;
  }
  Ray ray;
  ray.position = rayOrigin;
  ray.velocity = rayDirs[i];
  ray.affineParameter = 0.0;
  HitResult hit = bhTraceGeodesic(ray, schwarzschildRadius, depthFar, traceSteps, traceStepSize);
  vec4 shaded = bhShadeHit(hit, rayOrigin, schwarzschildRadius);
  vec3 terminal;
  vec4 rte = bhTraceGeodesicRTE(ray, schwarzschildRadius, depthFar, traceSteps, traceStepSize,
                                rteOpacityScale, terminal);
  vec4 stokes = bhTraceGeodesicStokes(ray, schwarzschildRadius, depthFar, traceSteps,
                                      traceStepSize, rteOpacityScale, stokesBFieldAngle,
                                      stokesNeScale, terminal);
  int o = 12 * i;
  result[o] = hit.hitDisk ? 1.0 : 0.0;
  result[o + 1] = length(hit.hitPoint.xy);
  result[o + 2] = hit.photonLambda;
  result[o + 3] = shaded.r;
  result[o + 4] = shaded.g;
  result[o + 5] = shaded.b;
  result[o + 6] = rte.r;
  result[o + 7] = rte.g;
  result[o + 8] = rte.b;
  result[o + 9] = stokes.r;
  result[o + 10] = stokes.g;
  result[o + 11] = stokes.b;
}
)";
}

struct TraceCase {
  float spin;
  float rs;
};

// Camera at (40, 0, 10) M, rays tilted by atan(0.36) off the hole: both land
// near r = 13 M, where the approaching side's g is about 1.23 and the
// receding side's about 0.68.
constexpr double K_CAMERA_DISTANCE_M = 40.0;
constexpr double K_CAMERA_HEIGHT_M = 10.0;
constexpr double K_FOV_SCALE = 0.36;
constexpr float K_PEAK_TEMPERATURE = 10000.0F;

double luminance(const float *rgb) {
  return (0.2126729 * static_cast<double>(rgb[0])) + (0.7151522 * static_cast<double>(rgb[1])) +
         (0.0721750 * static_cast<double>(rgb[2]));
}

class DiskTransferTraceTest : public DiskTransferShaderTest {
protected:
  static std::vector<float> trace(GLuint program, const bhtest::MirrorPair &pair, TraceCase c,
                                  int transferMode) {
    glUseProgram(program);
    const auto set1f = [&](const char *name, float v) {
      glUniform1f(glGetUniformLocation(program, name), v);
    };
    set1f("kerrSpin", c.spin);
    set1f("schwarzschildRadius", c.rs);
    set1f("depthFar", 100.0F * c.rs);
    set1f("adiskEnabled", 1.0F);
    set1f("diskPeakTemperature", K_PEAK_TEMPERATURE);
    set1f("diskBrightness", 1.0F);
    set1f("diskFluxPeak", static_cast<float>(physics::pageThorneFluxPeak(static_cast<double>(c.spin))));
    set1f("diskTransferMode", static_cast<float>(transferMode));
    set1f("backgroundEnabled", 0.0F);
    set1f("rteOpacityScale", 0.0F);
    set1f("stokesBFieldAngle", 0.0F);
    set1f("stokesNeScale", 0.0F);
    set1f("bhDebugFlags", 0.0F);
    set1f("traceStepSize", 0.02F);
    glUniform1i(glGetUniformLocation(program, "traceSteps"), 20000);
    glUniform3f(glGetUniformLocation(program, "rayOrigin"), static_cast<float>(pair.cam[0]),
                static_cast<float>(pair.cam[1]), static_cast<float>(pair.cam[2]));
    std::array<float, 6> dirs{};
    for (std::size_t k = 0; k < 6; ++k) {
      dirs.at(k) = static_cast<float>(pair.dir.at(k / 3).at(k % 3));
    }
    glUniform3fv(glGetUniformLocation(program, "rayDirs"), 2, dirs.data());

    GLuint ssbo = 0;
    glCreateBuffers(1, &ssbo);
    glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 2 * K_TRACE_STRIDE), nullptr,
                      GL_DYNAMIC_DRAW);
    glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
    std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 2 * K_TRACE_STRIDE, 1);
    glDeleteBuffers(1, &ssbo);
    return out;
  }
};

// For each ray of the pair, the shipped bhShadeHit color must carry
// g = physics::diskTransferG(r_hit / M, a, lambda / M) with lambda from the
// double-precision reference trace of the same camera ray, recovered as
// (Y / F_norm(r_hit / M))^(1/4) since the chroma has unit luminance. The
// approaching ray must have g > 1.05 and the receding one g < 0.95. The
// nonunit r_s cases scale the geometry with M, so the image is unchanged and
// every M = 1 evaluation of the flux shape or g would miss by a factor of M
// in r and lambda. In Interstellar mode the luminance must equal F_norm alone.
// Tolerances, about five times the float32 deviations measured on an
// SM 8.9 GL 4.6 driver: hit radius 1e-4 (chord interpolation of the
// crossing), lambda 1e-5, g 5e-5, Interstellar luminance 2e-4 (float
// Page-Thorne bracket and chroma matrix). A flipped lambda sign moves g from
// about 1.23 to 0.68, and a dropped 1/M moves r and lambda by the factor M.
// Checks one ray of the pair; side 0 is the approaching ray.
void checkTracedSide(const float *px, const float *filmPx, const bhtest::MirrorPair &pair,
                     std::size_t side, TraceCase c) {
  const auto spin = static_cast<double>(c.spin);
  const auto rs = static_cast<double>(c.rs);
  const double m = 0.5 * rs;
  const double peak = physics::pageThorneFluxPeak(spin);
  const double rIn = 0.5 * physics::pageThorneIscoRadius(spin) * rs;
  ASSERT_EQ(px[0], 1.0F) << "a=" << spin << " rs=" << rs << " side " << side;
  ASSERT_EQ(filmPx[0], 1.0F) << "a=" << spin << " rs=" << rs << " side " << side;

  // The shader receives these vectors rounded to float; the 6e-8 relative
  // rounding moves r and lambda far less than the tolerances below.
  const bhtest::DiskHitReference ref =
      bhtest::traceDiskHitReference(pair.cam, pair.dir.at(side), rs, spin, rIn, 100.0 * rs);
  ASSERT_TRUE(ref.hitDisk) << "a=" << spin << " rs=" << rs << " side " << side;

  const auto rHit = static_cast<double>(px[1]);
  const auto lambda = static_cast<double>(px[2]);
  EXPECT_NEAR(rHit / ref.radius, 1.0, 1e-4) << "a=" << spin << " rs=" << rs;
  EXPECT_NEAR(lambda / ref.lambda, 1.0, 1e-5) << "a=" << spin << " rs=" << rs;

  for (std::size_t k = 3; k < 6; ++k) {
    EXPECT_GT(px[k], 0.0F) << "chroma channel clipped, side " << side;
  }
  const double fluxNorm = physics::pageThorneFluxShape(rHit / m, spin) / peak;
  const double gGpu = std::pow(luminance(px + 3) / fluxNorm, 0.25);
  const double gRef = physics::diskTransferG(rHit / m, spin, ref.lambda / m);
  EXPECT_NEAR(gGpu / gRef, 1.0, 5e-5)
      << "a=" << spin << " rs=" << rs << " side " << side << " g=" << gGpu;
  if (side == 0) {
    EXPECT_GT(gGpu, 1.05) << "approaching side, a=" << spin << " rs=" << rs;
  } else {
    EXPECT_LT(gGpu, 0.95) << "receding side, a=" << spin << " rs=" << rs;
  }

  const double filmFluxNorm =
      physics::pageThorneFluxShape(static_cast<double>(filmPx[1]) / m, spin) / peak;
  EXPECT_NEAR(luminance(filmPx + 3) / filmFluxNorm, 1.0, 2e-4)
      << "Interstellar mode, a=" << spin << " rs=" << rs << " side " << side;
}

TEST_F(DiskTransferTraceTest, TracedDiskRaysCarryTheOrbitingEmitterShift) {
  const GLuint program = bhtest::createComputeProgram(traceShader());
  for (const TraceCase c : {TraceCase{0.0F, 2.0F}, TraceCase{0.9F, 2.0F}, TraceCase{0.9F, 6.0F},
                            TraceCase{-0.6F, 1.0F}}) {
    const bhtest::MirrorPair pair = bhtest::makeMirrorPair(
        static_cast<double>(c.rs), K_CAMERA_DISTANCE_M, K_CAMERA_HEIGHT_M, K_FOV_SCALE);
    const std::vector<float> physical = trace(program, pair, c, 0);
    const std::vector<float> film = trace(program, pair, c, 1);
    for (std::size_t side = 0; side < 2; ++side) {
      checkTracedSide(&physical.at(side * K_TRACE_STRIDE), &film.at(side * K_TRACE_STRIDE), pair,
                      side, c);
    }
  }
  glDeleteProgram(program);
}

// The volumetric RTE and Stokes traces shade each disk step with the photon's
// own lambda. At a = 0 the mirror pair is exactly symmetric, so with g = 1
// (Interstellar) both rays accumulate the same color, while the physical
// shift makes the approaching ray brighter by more than 1.5x and bluer
// (larger B/R). Optically thin (rteOpacityScale 0), Faraday rotation off.
TEST_F(DiskTransferTraceTest, VolumetricTracesBrightenTheApproachingSide) {
  const GLuint program = bhtest::createComputeProgram(traceShader());
  const TraceCase c{0.0F, 2.0F};
  const bhtest::MirrorPair pair =
      bhtest::makeMirrorPair(2.0, K_CAMERA_DISTANCE_M, K_CAMERA_HEIGHT_M, K_FOV_SCALE);
  const std::vector<float> physical = trace(program, pair, c, 0);
  const std::vector<float> film = trace(program, pair, c, 1);
  glDeleteProgram(program);

  for (const std::size_t offset : {std::size_t{6}, std::size_t{9}}) {
    const char *const path = offset == 6 ? "RTE" : "Stokes";
    const float *app = &physical.at(offset);
    const float *rec = &physical.at(K_TRACE_STRIDE + offset);
    const float *filmApp = &film.at(offset);
    const float *filmRec = &film.at(K_TRACE_STRIDE + offset);
    ASSERT_GT(luminance(filmApp), 0.0) << path;
    EXPECT_NEAR(luminance(filmApp) / luminance(filmRec), 1.0, 1e-5) << path;
    EXPECT_GT(luminance(app), 1.5 * luminance(rec)) << path;
    EXPECT_GT(static_cast<double>(app[2] / app[0]), static_cast<double>(rec[2] / rec[0])) << path;
  }
}

// A camera in the disk plane (z = 0) inside the annulus sees the disk
// edge-on: a step that starts on the plane is not a crossing. A ray leaving
// the plane away from the hole never crosses it and must report no disk hit;
// a ray leaving it toward the hole may only hit on a genuine crossing on the
// far side, not at the camera's own radius at t = 0.
TEST_F(DiskTransferTraceTest, InPlaneCameraDoesNotHitTheDiskAtItsOwnPosition) {
  const GLuint program = bhtest::createComputeProgram(traceShader());
  constexpr double cameraR = 15.0; // 7.5 r_s, inside the 3-100 r_s disk
  bhtest::MirrorPair pair;
  pair.cam = {cameraR, 0.0, 0.0};
  pair.forward = {-1.0, 0.0, 0.0};
  constexpr double inv = 0.5 * std::numbers::sqrt2;
  pair.dir = {bhtest::Vec3d{inv, 0.0, inv}, bhtest::Vec3d{-0.96, 0.0, 0.28}};
  for (const float spin : {0.0F, 0.9F}) {
    const std::vector<float> out = trace(program, pair, TraceCase{spin, 2.0F}, 0);
    EXPECT_EQ(out.at(0), 0.0F) << "outward ray reported a disk hit, a=" << spin
                               << " r_hit=" << out.at(1);
    if (out.at(K_TRACE_STRIDE) == 1.0F) {
      EXPECT_GT(std::abs(static_cast<double>(out.at(K_TRACE_STRIDE + 1)) - cameraR), 1.0)
          << "inward ray hit the disk at the camera radius, a=" << spin;
    }
  }
  glDeleteProgram(program);
}

} // namespace
