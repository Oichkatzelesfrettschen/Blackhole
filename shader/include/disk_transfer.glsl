#ifndef DISK_TRANSFER_GLSL
#define DISK_TRANSFER_GLSL

// Page-Thorne disk flux, orbiting-emitter energy shift and blackbody chroma,
// all in M = 1 units with the disk orbiting in +phi (signed spin a). The
// shift g is E_obs / E_emit for an observer at rest at infinity, and the
// renderer draws the disk as bolometric g^4 F / F_peak times the
// unit-luminance chroma at g T_emit rather than the visible-band luminance of
// the shifted blackbody (physics/disk_transfer.h).
// Float twins of src/physics/page_thorne.h and src/physics/disk_transfer.h;
// tests/disk_transfer_shader_test.cpp holds these functions to the C++.

// Use include/ prefix for shader loader compatibility
#include "include/disk_profile.glsl"

// Page-Thorne flux shape S(r) = F(r) 8 pi / (3 Mdot); zero at and inside the
// ISCO. The disk inner edge (bhDiskInnerRadius) and this zero-torque edge
// share isco_radius. x2 comes from Vieta's product x1 x2 x3 = -2a, which
// stays accurate in float as x2 -> 0 at a -> 0, where its term vanishes.
// The spin is clamped to |a| <= 0.9999 like isco_radius; at |a| = 1 the roots
// x1 and x2 coincide and the closed form divides by zero.
float dtPageThorneShape(float r, float aIn) {
  float a = clamp(aIn, -0.9999, 0.9999);
  float rIsco = isco_radius(a);
  if (!(r > rIsco)) {
    return 0.0;
  }
  float x = sqrt(r);
  float x0 = sqrt(rIsco);
  float theta = acos(clamp(a, -1.0, 1.0)) / 3.0;
  float x1 = 2.0 * cos(theta - 1.0471975512);
  float x3 = -2.0 * cos(theta);
  float x2 = -2.0 * a / (x1 * x3);

  float bracket = x - x0 - 1.5 * a * log(x / x0);
  bracket -= 3.0 * (x1 - a) * (x1 - a) / (x1 * (x1 - x2) * (x1 - x3)) *
             log((x - x1) / (x0 - x1));
  if (abs(x2) > 1e-7) {
    bracket -= 3.0 * (x2 - a) * (x2 - a) / (x2 * (x2 - x1) * (x2 - x3)) *
               log((x - x2) / (x0 - x2));
  }
  bracket -= 3.0 * (x3 - a) * (x3 - a) / (x3 * (x3 - x1) * (x3 - x2)) *
             log((x - x3) / (x0 - x3));
  float q = x * x * x - 3.0 * x + 2.0 * a;
  return max(bracket, 0.0) / (x * x * x * x * q);
}

// g = 1 / (u^t (1 - Omega lambda)) for a Keplerian circular emitter at r and
// a photon with lambda = Lz / E; 0 where no circular orbit exists or the
// photon's local energy would be non-positive.
float dtDiskTransferG(float r, float a, float lambda) {
  float invR32 = 1.0 / (r * sqrt(r));
  float q = 1.0 - 3.0 / r + 2.0 * a * invR32;
  if (!(q > 0.0)) {
    return 0.0;
  }
  float ut = (1.0 + a * invR32) / sqrt(q);
  float omega = 1.0 / (r * sqrt(r) + a);
  float denom = 1.0 - omega * lambda;
  if (!(denom > 0.0)) {
    return 0.0;
  }
  return 1.0 / (ut * denom);
}

// Linear-sRGB blackbody chromaticity at luminance Y = 1: the Kim et al.
// (2002) cubic fit to the CIE 1931 Planckian locus over 1667-25000 K,
// clamped to that range, with out-of-gamut components clipped to zero.
vec3 dtBlackbodyChroma(float temperatureK) {
  float t = clamp(temperatureK, 1667.0, 25000.0);
  float inv = 1.0e3 / t;
  float inv2 = inv * inv;
  float inv3 = inv2 * inv;
  float xc = t <= 4000.0
                 ? -0.2661239 * inv3 - 0.2343589 * inv2 + 0.8776956 * inv + 0.179910
                 : -3.0258469 * inv3 + 2.1070379 * inv2 + 0.2226347 * inv + 0.240390;
  float xc2 = xc * xc;
  float xc3 = xc2 * xc;
  float yc;
  if (t <= 2222.0) {
    yc = -1.1063814 * xc3 - 1.34811020 * xc2 + 2.18555832 * xc - 0.20219683;
  } else if (t <= 4000.0) {
    yc = -0.9549476 * xc3 - 1.37418593 * xc2 + 2.09137015 * xc - 0.16748867;
  } else {
    yc = 3.0817580 * xc3 - 5.87338670 * xc2 + 3.75112997 * xc - 0.37001483;
  }
  float bigX = xc / yc;
  float bigZ = (1.0 - xc - yc) / yc;
  vec3 rgb = vec3(3.2404542 * bigX - 1.5371385 - 0.4985314 * bigZ,
                  -0.9692660 * bigX + 1.8760108 + 0.0415560 * bigZ,
                  0.0556434 * bigX - 0.2040259 + 1.0572252 * bigZ);
  return max(rgb, vec3(0.0));
}

#endif // DISK_TRANSFER_GLSL
