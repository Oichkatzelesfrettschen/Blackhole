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
#include <array>
#include <cmath>
#include <cstddef>
#include <numbers>
#include <ranges>
#include <string>
#include <vector>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <gtest/gtest.h>

#include "physics/constants.h"
#include "physics/kerr.h"
#include "physics/stokes_transport.h"
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

// Starts on and next to the equatorial stationary limit r = 2M (a = 0.6):
// ray i sits at radius index i % 3 (2(1 - 1e-4), 2, 2(1 + 1e-4)) with
// direction (cos beta, sin beta, 0), beta = 2 pi (i / 3 + 0.5) / 342, so
// k^phi = sin(beta) / r. Reports the three on-shell residuals of
// K_ONSHELL_SHADER, or -1 in the first slot for a ray marked captured.
const char *const K_STATIONARY_LIMIT_SHADER = R"(
#version 460 core
layout(local_size_x = 64) in;
layout(std430, binding = 0) buffer Output { float result[]; };
uniform int rayCount;
#include "include/kerr.glsl"
void main() {
  int i = int(gl_GlobalInvocationID.x);
  if (i >= rayCount) {
    return;
  }
  float r_s = 2.0;
  float a = 0.6;
  int rIdx = i % 3;
  float r0 = rIdx == 0 ? 2.0 * (1.0 - 1e-4) : (rIdx == 1 ? 2.0 : 2.0 * (1.0 + 1e-4));
  float beta = 6.28318530718 * (float(i / 3) + 0.5) / 342.0;
  KerrConsts c;
  KerrRay ray;
  kerrInitGeodesic(vec3(r0, 0.0, 0.0), vec3(cos(beta), sin(beta), 0.0), r_s, a, c, ray);
  if (!(ray.r > 0.0)) {
    result[3 * i] = -1.0;
    result[3 * i + 1] = 0.0;
    result[3 * i + 2] = 0.0;
    return;
  }
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

// A straight ray at inclination `incl` from the disk normal crossing the
// midplane at (crossX, 0, 0) (default 30) from z = 3 to z = -3 (15 scale heights of h = 0.2
// each side), cut into chords of length segLength starting at an offset of
// 0.37 segLength, each passed to bhDiskSegment and rteStepVec3 with
// absorption kappa * jEff, as bhTraceGeodesicRTE does per step. Reports the
// emission column sum(jEff * length) and the intensity.
std::string diskSlabShader() {
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  return comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
uniform float segLength;
uniform float incl;
uniform float kappa;
uniform float crossX = 30.0;
void main() {
  float r_s = 2.0;
  float h = 0.1 * r_s;
  vec3 dir = vec3(sin(incl), 0.0, -cos(incl));
  float total = 6.0 / cos(incl);
  vec3 start = vec3(crossX, 0.0, 0.0) - 0.5 * total * dir;
  float column = 0.0;
  float transmit = 1.0;
  vec3 accum = vec3(0.0);
  float s0 = 0.0;
  float s1 = min(0.37 * segLength, total);
  for (int k = 0; k < 100000 && s0 < total; ++k) {
    vec3 emitColor;
    float jEff;
    float rho;
    if (bhDiskSegment(start + s0 * dir, start + s1 * dir, bhDiskInnerRadius(r_s), 100.0 * r_s,
                      h, r_s, emitColor, jEff, rho)) {
      column += jEff * (s1 - s0);
      accum += rteStepVec3(vec3(1.0), jEff, kappa * jEff, s1 - s0, transmit);
    }
    s0 = s1;
    s1 = min(s1 + segLength, total);
  }
  result[0] = column;
  result[1] = accum.x;
}
)";
}

// bhTraceGeodesic at a = 0.998 from the camera (3 sin 60deg, 0, 3 cos 60deg)
// along 16 downward directions (0.8 cos beta, 0.8 sin beta, -1), with a fine
// schedule (stepSize 0.002, 200000 steps). Reports hitDisk, the hit point,
// hit.origin (the camera in the tracer's chart), and the hit point in
// Boyer-Lindquist coordinates (bhChartToBoyerLindquist).
constexpr int K_ORIGIN_RAYS = 16;
constexpr int K_ORIGIN_STRIDE = 10;
std::string chartOriginShader() {
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  return comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
void main() {
  int i = int(gl_GlobalInvocationID.y) * int(gl_NumWorkGroups.x) * 16 +
          int(gl_GlobalInvocationID.x);
  if (i >= 16) {
    return;
  }
  float beta = 6.28318530718 * float(i) / 16.0;
  Ray ray;
  ray.position = 3.0 * vec3(sin(1.04719755), 0.0, cos(1.04719755));
  ray.velocity = normalize(vec3(0.8 * cos(beta), 0.8 * sin(beta), -1.0));
  ray.affineParameter = 0.0;
  HitResult hit = bhTraceGeodesic(ray, 2.0, 100.0, 200000, 0.002);
  vec3 bl = bhChartToBoyerLindquist(hit.hitPoint, 2.0);
  result[10 * i] = hit.hitDisk ? 1.0 : 0.0;
  result[10 * i + 1] = hit.hitPoint.x;
  result[10 * i + 2] = hit.hitPoint.y;
  result[10 * i + 3] = hit.hitPoint.z;
  result[10 * i + 4] = hit.origin.x;
  result[10 * i + 5] = hit.origin.y;
  result[10 * i + 6] = hit.origin.z;
  result[10 * i + 7] = bl.x;
  result[10 * i + 8] = bl.y;
  result[10 * i + 9] = bl.z;
}
)";
}

// bhTraceGeodesic at a = 0.6 from a camera in the disk plane, (15, 0, 0)
// inside the annulus 6 <= rho <= 200 (the default input camera, world
// (0, 0, 15), maps there), along 64 directions tilted +-0.05 to +-0.6 rad
// out of the plane at several azimuths. Reports hitDisk and the hit point's
// distance from the camera.
std::string inPlaneCameraShader() {
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  return comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
void main() {
  int i = int(gl_GlobalInvocationID.y) * int(gl_NumWorkGroups.x) * 16 +
          int(gl_GlobalInvocationID.x);
  if (i >= 64) {
    return;
  }
  float tilt = (i % 2 == 0 ? 1.0 : -1.0) * (0.05 + 0.55 * float((i / 2) % 8) / 7.0);
  float azimuth = 6.28318530718 * float(i / 16) / 4.0 + 0.3;
  Ray ray;
  ray.position = vec3(15.0, 0.0, 0.0);
  ray.velocity = vec3(cos(azimuth) * cos(tilt), sin(azimuth) * cos(tilt), sin(tilt));
  ray.affineParameter = 0.0;
  HitResult hit = bhTraceGeodesic(ray, 2.0, 100.0, 300, 0.1);
  result[2 * i] = hit.hitDisk ? 1.0 : 0.0;
  result[2 * i + 1] = length(hit.hitPoint - hit.origin);
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

TEST_F(KerrShaderCaptureTest, StationaryLimitStartIsOnShell) {
  // On r = 2M (g_tt = 0 in float32 exactly) the null condition is linear in
  // k^t. A direction with g_tphi k^phi < 0 (sin beta > 0 at a > 0) has the
  // finite root -spatial / (2 g_tphi k^phi) and must start on shell; one
  // with g_tphi k^phi > 0 has no finite future root and must be marked
  // captured. 1e-4 outside (g_tt < 0) every direction starts on shell; 1e-4
  // inside, a direction is either on shell or captured.
  const std::vector<float> out = dispatch(K_STATIONARY_LIMIT_SHADER, 0.0F);
  int onLimit = 0;
  for (int i = 0; i < K_RAYS; ++i) {
    const int rIdx = i % 3;
    const int betaIdx = i / 3;
    const double sinBeta =
        std::sin(2.0 * std::numbers::pi * (static_cast<double>(betaIdx) + 0.5) / 342.0);
    const std::size_t k = static_cast<std::size_t>(3) * static_cast<std::size_t>(i);
    const bool captured = out.at(k) < 0.0F;
    const std::string where = "ray " + std::to_string(i) + " r index " + std::to_string(rIdx) +
                              " sin(beta)=" + std::to_string(sinBeta);
    if (rIdx == 1 && std::abs(sinBeta) > 0.05) {
      EXPECT_EQ(captured, sinBeta < 0.0) << where;
      onLimit += captured ? 0 : 1;
    }
    if (rIdx == 2) {
      EXPECT_FALSE(captured) << where;
    }
    if (!captured) {
      for (std::size_t j = 0; j < 3; ++j) {
        EXPECT_LT(out.at(k + j), 1e-4F) << where << " check " << j;
      }
    }
  }
  EXPECT_GT(onLimit, 100);
}

TEST_F(KerrShaderCaptureTest, DiskSegmentIntegratesTheGaussianColumn) {
  // The Gaussian disk layer (h = 0.2) crossed at radius 30 (r_in = 6 at
  // a = 0) has emission column flux g^3 sqrt(2 pi) h / cos(i), flux =
  // x^3 (1 - sqrt x) with x = r_in / r and g = 1 + 0.3 sqrt(r_s / 2r) on the
  // phi = 0 meridian, and intensity (1 - exp(-kappa column)) / kappa. Chords
  // from 0.1 h to 100 h must reproduce both within 0.5%: the chord integral
  // is exact, and the residual is the variation of flux across the +-3 h
  // tan(i) the inclined ray sweeps radially (~1e-3). An end-point sample of
  // the density misses the midplane for chords much longer than h.
  const double h = 0.2;
  const double x = 6.0 / 30.0;
  const double flux = x * x * x * (1.0 - std::sqrt(x));
  const double g = 1.0 + (0.3 * std::sqrt(1.0 / 30.0));
  const double kappa = 400.0;
  const GLuint program = bhtest::createComputeProgram(diskSlabShader());
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 2), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  for (const double incl : {0.0, std::numbers::pi / 3.0}) {
    const double column = flux * g * g * g * std::sqrt(2.0 * std::numbers::pi) * h / std::cos(incl);
    const double intensity = (1.0 - std::exp(-kappa * column)) / kappa;
    for (const float segLength : {0.02F, 0.2F, 2.0F, 20.0F}) {
      glUseProgram(program);
      glUniform1f(glGetUniformLocation(program, "kerrSpin"), 0.0F);
      glUniform1f(glGetUniformLocation(program, "segLength"), segLength);
      glUniform1f(glGetUniformLocation(program, "incl"), static_cast<float>(incl));
      glUniform1f(glGetUniformLocation(program, "kappa"), static_cast<float>(kappa));
      const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 2);
      const std::string where =
          "incl=" + std::to_string(incl) + " segLength=" + std::to_string(segLength);
      EXPECT_NEAR(out.at(0), column, 5e-3 * column) << where;
      EXPECT_NEAR(out.at(1), intensity, 5e-3 * intensity) << where;
    }
  }
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

namespace {

// Emission column flux g^3 exp(-z^2 / 2h^2) over the annulus 6 <= rho <= 200
// (r_s = 2, a = 0) along the diskSlabShader ray, by the midpoint rule with
// 2e6 points.
double referenceDiskColumn(double crossX, double incl) {
  const double h = 0.2;
  const double total = 6.0 / std::cos(incl);
  const int n = 2'000'000;
  const double ds = total / n;
  double column = 0.0;
  for (int k = 0; k < n; ++k) {
    const double s = (k + 0.5) * ds;
    const double x = crossX + ((s - (0.5 * total)) * std::sin(incl));
    const double z = 3.0 - (s * std::cos(incl));
    const double rho = std::abs(x);
    if (rho < 6.0 || rho > 200.0) {
      continue;
    }
    const double u = 6.0 / rho;
    const double flux = u * u * u * (1.0 - std::sqrt(u));
    const double g = 1.0 + (0.3 * std::sqrt(1.0 / rho) * (x >= 0.0 ? 1.0 : -1.0));
    column += flux * g * g * g * std::exp(-0.5 * (z / h) * (z / h)) * ds;
  }
  return column;
}

} // namespace

TEST_F(KerrShaderCaptureTest, DiskSegmentClipsChordsToTheAnnulus) {
  // A ray 10 degrees from grazing crosses the midplane 1 M outside r_in = 6
  // and 1 M inside r_out = 200; its density footprint (+-3 h tan(80 deg) =
  // +-3.4 M) straddles the edge. The emission column must converge to the
  // quadrature reference as chords shrink from 40 h to 0.1 h. Checking one
  // radius per chord keeps or drops a whole chord at an edge instead.
  const double incl = 80.0 * std::numbers::pi / 180.0;
  const GLuint program = bhtest::createComputeProgram(diskSlabShader());
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 2), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  for (const double crossX : {7.0, 199.0}) {
    const double reference = referenceDiskColumn(crossX, incl);
    double previous = 1.0;
    for (const float segLength : {8.0F, 2.0F, 0.5F, 0.1F, 0.02F}) {
      glUseProgram(program);
      glUniform1f(glGetUniformLocation(program, "kerrSpin"), 0.0F);
      glUniform1f(glGetUniformLocation(program, "segLength"), segLength);
      glUniform1f(glGetUniformLocation(program, "incl"), static_cast<float>(incl));
      glUniform1f(glGetUniformLocation(program, "kappa"), 1.0F);
      glUniform1f(glGetUniformLocation(program, "crossX"), static_cast<float>(crossX));
      const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 2);
      const double error = std::abs((static_cast<double>(out.at(0)) - reference) / reference);
      const std::string where = "crossX=" + std::to_string(crossX) +
                                " segLength=" + std::to_string(segLength) +
                                " error=" + std::to_string(error);
      // Second order in the chord: the centroid read of the radial factors is
      // exact for linear variation, and flux curves sharply just outside r_in.
      EXPECT_LE(error, std::max(1.05 * previous, 1e-5)) << where;
      if (segLength <= 0.5F) {
        EXPECT_LT(error, 1e-2) << where;
      }
      if (segLength <= 0.1F) {
        EXPECT_LT(error, 1e-3) << where;
      }
      previous = error;
    }
  }
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

namespace {

// Kerr-Schild azimuth offset F(r) = a / (r+ - r-) ln((r - r+) / (r - r-))
// (M = 1), the rotation kerrKsAzimuthOffset applies.
double ksAzimuthOffset(double r, double a) {
  const double root = std::sqrt(1.0 - (a * a));
  return a / (2.0 * root) * std::log((r - (1.0 + root)) / (r - (1.0 - root)));
}

struct ChartHit {
  bool hitDisk{false};
  double x{0.0};    // Kerr-Schild chart
  double y{0.0};
  double xBl{0.0};  // Boyer-Lindquist
  double yBl{0.0};
};

// Double-precision disk crossing of the time-reversed ray (spin aTrace) from
// the camera, in the Kerr-Schild chart: phi_KS = phi_BL + F(r).
ChartHit referenceDiskHit(double camX, double camZ, double dx, double dy, double dz,
                          double aTrace) {
  const double mass = physics::C2 / physics::G;
  const double r0 = std::hypot(camX, camZ);
  const double theta0 = std::acos(camZ / r0);
  const double norm = std::sqrt((dx * dx) + (dy * dy) + (dz * dz));
  const double ux = dx / norm;
  const double uy = dy / norm;
  const double uz = dz / norm;
  // e_r, e_theta, e_phi at (theta0, phi = 0).
  const double kr = (ux * std::sin(theta0)) + (uz * std::cos(theta0));
  const double kth = ((ux * std::cos(theta0)) - (uz * std::sin(theta0))) / r0;
  const double kph = uy / (r0 * std::sin(theta0));
  const physics::KerrNullGeodesic g =
      physics::kerrNullGeodesicFromBL(r0, theta0, 0.0, kr, kth, kph, mass, aTrace);
  physics::KerrGeodesicState s = g.state;
  const double rPlus = 1.0 + std::sqrt(1.0 - (aTrace * aTrace));
  for (int step = 0; step < 5'000'000 && s.r > rPlus * 1.001; ++step) {
    const physics::KerrGeodesicState next =
        physics::kerrStepMino(s, mass, aTrace, g.consts, 2e-5 / (1.0 + (s.r * s.r)));
    const double c0 = std::cos(s.theta);
    const double c1 = std::cos(next.theta);
    if (c0 * c1 <= 0.0) {
      const double t = c0 / (c0 - c1);
      const double r = s.r + (t * (next.r - s.r));
      const double phiBl = s.phi + (t * (next.phi - s.phi));
      const double phi = phiBl + ksAzimuthOffset(r, aTrace);
      return {.hitDisk = true,
              .x = r * std::cos(phi),
              .y = r * std::sin(phi),
              .xBl = r * std::cos(phiBl),
              .yBl = r * std::sin(phiBl)};
    }
    s = next;
  }
  return {};
}

} // namespace

namespace {

// View vector and depth (hit - origin) of the GPU disk hit at out[k] against
// the reference, and its Boyer-Lindquist position (out[k + 7..8]).
void expectChartHit(const std::vector<float> &out, std::size_t k, const ChartHit &ref,
                    const std::array<double, 3> &origin, const std::string &where) {
  const auto vx = static_cast<double>(out.at(k + 1) - out.at(k + 4));
  const auto vy = static_cast<double>(out.at(k + 2) - out.at(k + 5));
  const auto vz = static_cast<double>(out.at(k + 3) - out.at(k + 6));
  // float32 stepping leaves ~2e-4; the unrotated camera is off by ~1.5.
  EXPECT_NEAR(vx, ref.x - origin[0], 1e-3) << where;
  EXPECT_NEAR(vy, ref.y - origin[1], 1e-3) << where;
  EXPECT_NEAR(vz, -origin[2], 1e-3) << where;
  EXPECT_NEAR(std::sqrt((vx * vx) + (vy * vy) + (vz * vz)),
              std::hypot(ref.x - origin[0], ref.y - origin[1], origin[2]), 1e-3)
      << where;
  // The wiregrid reads Boyer-Lindquist phi: bhChartToBoyerLindquist must
  // undo the offset, which rotates the chart hit by F(r_hit) (0.1 to 0.6
  // rad here) away from it.
  EXPECT_NEAR(out.at(k + 7), ref.xBl, 1e-3) << where;
  EXPECT_NEAR(out.at(k + 8), ref.yBl, 1e-3) << where;
  EXPECT_GT(std::hypot(ref.x - ref.xBl, ref.y - ref.yBl), 0.1) << where;
}

} // namespace

TEST_F(KerrShaderCaptureTest, HitOriginSharesTheTracerChart) {
  // kerrInitGeodesic rotates the ray state by the Kerr-Schild offset
  // F(r_cam), which at a = 0.998 and r = 3 is 0.50 rad, so hit points are in
  // that chart. hit.origin, rotated alike, must give the view vector and
  // depth (hit - origin) of the double-precision reference; the unrotated
  // camera misses them by ~1.5 M. bhChartToBoyerLindquist must return the
  // reference's Boyer-Lindquist hit point for the wiregrid overlay.
  const double aTrace = -0.998;
  const double camX = 3.0 * std::sin(std::numbers::pi / 3.0);
  const double camZ = 3.0 * std::cos(std::numbers::pi / 3.0);
  const double offset = ksAzimuthOffset(3.0, aTrace);
  const double originX = camX * std::cos(offset);
  const double originY = camX * std::sin(offset);
  const GLuint program = bhtest::createComputeProgram(chartOriginShader());
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo,
                    static_cast<GLsizeiptr>(sizeof(float) * K_ORIGIN_STRIDE * K_ORIGIN_RAYS),
                    nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  glUseProgram(program);
  glUniform1f(glGetUniformLocation(program, "kerrSpin"), 0.998F);
  glUniform1f(glGetUniformLocation(program, "adiskEnabled"), 1.0F);
  const std::vector<float> out = bhtest::runComputeProgram(
      program, ssbo, static_cast<std::size_t>(K_ORIGIN_STRIDE) * K_ORIGIN_RAYS, 1);
  int compared = 0;
  for (int i = 0; i < K_ORIGIN_RAYS; ++i) {
    const std::size_t k =
        static_cast<std::size_t>(K_ORIGIN_STRIDE) * static_cast<std::size_t>(i);
    const double beta = 2.0 * std::numbers::pi * static_cast<double>(i) / K_ORIGIN_RAYS;
    const ChartHit ref =
        referenceDiskHit(camX, camZ, 0.8 * std::cos(beta), 0.8 * std::sin(beta), -1.0, aTrace);
    const std::string where = "ray " + std::to_string(i);
    EXPECT_NEAR(out.at(k + 4), originX, 1e-4) << where;
    EXPECT_NEAR(out.at(k + 5), originY, 1e-4) << where;
    EXPECT_NEAR(out.at(k + 6), camZ, 1e-4) << where;
    if (!ref.hitDisk || out.at(k) < 0.5F || std::hypot(ref.x, ref.y) < 1.5) {
      continue;
    }
    expectChartHit(out, k, ref, {originX, originY, camZ}, where);
    ++compared;
  }
  EXPECT_GT(compared, K_ORIGIN_RAYS / 2);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

namespace {

// Two polarized layers, near (index 0) and far (index 1), with different
// EVPAs, absorption, Faraday rates, and path lengths.
struct PolLayer {
  double jI, jQ, jU, jV, alpha, rhoV, ds;
};

PolLayer polLayer(double jI, double chiB, double jV, double alpha, double rhoV, double ds) {
  return {.jI = jI,
          .jQ = -jI * 0.7 * std::cos(2.0 * chiB),
          .jU = -jI * 0.7 * std::sin(2.0 * chiB),
          .jV = jV,
          .alpha = alpha,
          .rhoV = rhoV,
          .ds = ds};
}

physics::StokesVector stepLayer(const physics::StokesVector &state, const PolLayer &l) {
  return physics::stokesStep(state, {.jI = l.jI, .jQ = l.jQ, .jU = l.jU, .jV = l.jV}, l.alpha,
                             l.rhoV, l.ds);
}

} // namespace

TEST_F(KerrShaderCaptureTest, StokesCompositesLayersFrontToBack) {
  // The observed Stokes vector of a near layer in front of a far one is the
  // far layer's output transferred through the near layer (the CPU
  // stokesStep integrated from the far end). stokesCompositeStep, fed in
  // camera order as bhTraceGeodesicStokes marches, must reproduce it; feeding
  // the running state into the farther layer, the reverse order, misses it by
  // more than 0.1 here.
  const PolLayer nearLayer = polLayer(1.0, 0.2, 0.0, 0.8, 1.5, 1.0);
  const PolLayer farLayer = polLayer(2.0, 1.1, 0.3, 0.3, -0.7, 1.5);
  const physics::StokesVector reference = stepLayer(stepLayer({}, farLayer), nearLayer);
  const physics::StokesVector reversed = stepLayer(stepLayer({}, nearLayer), farLayer);
  ASSERT_GT(std::hypot(reference.q - reversed.q, reference.u - reversed.u), 0.1);

  const GLuint program = bhtest::createComputeProgram(R"(
#version 460 core
layout(local_size_x = 1) in;
layout(std430, binding = 0) buffer Output { float result[]; };
uniform vec4 em0;
uniform vec3 k0;
uniform vec4 em1;
uniform vec3 k1;
#include "include/stokes_transport.glsl"
void main() {
  vec4 observed = vec4(0.0);
  float transmit = 1.0;
  float faraday = 0.0;
  stokesCompositeStep(observed, transmit, faraday, em0, k0.x, k0.y, k0.z);
  stokesCompositeStep(observed, transmit, faraday, em1, k1.x, k1.y, k1.z);
  result[0] = observed.x;
  result[1] = observed.y;
  result[2] = observed.z;
  result[3] = observed.w;
  result[4] = transmit;
}
)");
  glUseProgram(program);
  const auto setLayer = [program](const char *em, const char *k, const PolLayer &l) {
    glUniform4f(glGetUniformLocation(program, em), static_cast<float>(l.jI),
                static_cast<float>(l.jQ), static_cast<float>(l.jU), static_cast<float>(l.jV));
    glUniform3f(glGetUniformLocation(program, k), static_cast<float>(l.alpha),
                static_cast<float>(l.rhoV), static_cast<float>(l.ds));
  };
  setLayer("em0", "k0", nearLayer);
  setLayer("em1", "k1", farLayer);
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 5), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 0, ssbo);
  const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 5);
  EXPECT_NEAR(out.at(0), reference.i, 1e-5);
  EXPECT_NEAR(out.at(1), reference.q, 1e-5);
  EXPECT_NEAR(out.at(2), reference.u, 1e-5);
  EXPECT_NEAR(out.at(3), reference.v, 1e-5);
  EXPECT_NEAR(out.at(4), std::exp(-((0.8 * 1.0) + (0.3 * 1.5))), 1e-6);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

TEST_F(KerrShaderCaptureTest, CameraInTheDiskPlaneIsNotADiskHit) {
  // A zero-thickness disk seen from a point in its plane: a ray leaving the
  // plane has not crossed it at its own start, so no ray may report a disk
  // hit at the camera (distance 0). Treating the start point (z = 0) as a
  // crossing shades every tilted pixel as the disk at the observer.
  const GLuint program = bhtest::createComputeProgram(inPlaneCameraShader());
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 128), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  glUseProgram(program);
  glUniform1f(glGetUniformLocation(program, "kerrSpin"), 0.6F);
  glUniform1f(glGetUniformLocation(program, "adiskEnabled"), 1.0F);
  const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 128, 1);
  const auto atCamera = std::ranges::count_if(std::views::iota(0, 64), [&out](int i) {
    const auto k = static_cast<std::size_t>(2) * static_cast<std::size_t>(i);
    return out.at(k) > 0.5F && out.at(k + 1) < 1e-2F;
  });
  EXPECT_EQ(atCamera, 0);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}

TEST_F(KerrShaderCaptureTest, NoHoleTerminalPointsSkipTheChartConversion) {
  // With renderBlackHole = 0 the traces return the straight camera ray's end
  // point, never rotated into the Kerr-Schild chart, so the wiregrid's
  // bhChartToBoyerLindquist must leave it as is; at a = 0.998 and r ~ 100
  // the -F(r) rotation would move it by ~1 M.
  const std::string comp = bhtest::readShaderInclude("geodesic_trace.comp");
  const GLuint program = bhtest::createComputeProgram(comp.substr(0, comp.find("void main()")) + R"(
layout(std430, binding = 1) buffer Output { float result[]; };
void main() {
  Ray ray;
  ray.position = vec3(20.0, 5.0, 3.0);
  ray.velocity = normalize(vec3(0.3, 1.0, 0.2));
  ray.affineParameter = 0.0;
  HitResult hit = bhTraceGeodesic(ray, 2.0, 100.0, 300, 0.1);
  vec3 terminalPos;
  bhTraceGeodesicRTE(ray, 2.0, 100.0, 300, 0.1, 0.5, terminalPos);
  vec3 a = bhChartToBoyerLindquist(hit.hitPoint, 2.0);
  vec3 b = bhChartToBoyerLindquist(terminalPos, 2.0);
  result[0] = length(a - hit.hitPoint);
  result[1] = length(b - terminalPos);
  result[2] = length(hit.hitPoint);
}
)");
  GLuint ssbo = 0;
  glCreateBuffers(1, &ssbo);
  glNamedBufferData(ssbo, static_cast<GLsizeiptr>(sizeof(float) * 3), nullptr, GL_DYNAMIC_DRAW);
  glBindBufferBase(GL_SHADER_STORAGE_BUFFER, 1, ssbo);
  glUseProgram(program);
  glUniform1f(glGetUniformLocation(program, "kerrSpin"), 0.998F);
  glUniform1f(glGetUniformLocation(program, "renderBlackHole"), 0.0F);
  glUniform1f(glGetUniformLocation(program, "adiskEnabled"), 0.0F);
  const std::vector<float> out = bhtest::runComputeProgram(program, ssbo, 3);
  EXPECT_GT(out.at(2), 50.0F);
  EXPECT_LT(out.at(0), 1e-4F);
  EXPECT_LT(out.at(1), 1e-4F);
  glDeleteBuffers(1, &ssbo);
  glDeleteProgram(program);
}
