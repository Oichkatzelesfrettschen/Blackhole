/**
 * @file disk_transfer.h
 * @brief Energy shift and blackbody color of light from a Keplerian Kerr disk.
 *
 * Geometric units G = c = M = 1; aStar is the signed spin with the disk
 * orbiting in +phi (aStar < 0 is a retrograde disk). A circular equatorial
 * emitter at radius r has (Bardeen, Press & Teukolsky 1972)
 *
 *   Omega = 1 / (r^{3/2} + a),
 *   u^t   = (1 + a r^{-3/2}) / sqrt(1 - 3/r + 2a r^{-3/2}),
 *
 * and a photon with conserved energy E and axial angular momentum Lz reaching
 * a static observer at infinity has
 *
 *   g = E_obs / E_emit = 1 / (u^t (1 - Omega lambda)),   lambda = Lz / E.
 *
 * lambda comes from the traced ray (the physical photon's Lz = -c.Lz of the
 * time-reversed trace in kerr.glsl), so light bending and frame dragging
 * enter g through the photon's constants. Liouville's theorem keeps I_nu/nu^3
 * invariant, so a blackbody of temperature T appears as a blackbody of
 * temperature g T with bolometric intensity scaled by g^4.
 *
 * The renderer's Interstellar disk transfer mode forces g = 1 for both color
 * and intensity and keeps the lensing. James, von Tunzelmann, Franklin &
 * Thorne (2015, arXiv:1502.03808, sec. 4.2) render the disk of their Figures
 * 15a and 16 "without frequency shifts and associated colour and brightness
 * changes" and state: "This, with some embellishments, is the accretion disk
 * seen around the black hole Gargantua in Interstellar."
 *
 * shader/include/disk_transfer.glsl and src/cuda/device_disk_transfer.cuh are
 * the float twins; tests/disk_transfer_test.cpp pins the values and
 * tests/disk_transfer_shader_test.cpp and tests/cuda_disk_transfer_test.cu
 * hold the twins to this header. The header compiles as C++17 for those
 * nvcc-built tests.
 */

#ifndef PHYSICS_DISK_TRANSFER_H
#define PHYSICS_DISK_TRANSFER_H

#include <algorithm>
#include <array>
#include <cmath>

namespace physics {

/** @brief Keplerian angular velocity dphi/dt of a circular orbit (M = 1). */
[[nodiscard]] inline double keplerianOmega(double r, double aStar) noexcept {
  return 1.0 / ((r * std::sqrt(r)) + aStar);
}

/**
 * @brief u^t of the circular equatorial orbit at r (M = 1).
 *
 * 1/u^t at the ISCO is 0.707107 (a = 0), 0.370868 (a = 0.9), 0.092670
 * (a = 0.998). Returns 0 where no timelike circular orbit exists.
 */
[[nodiscard]] inline double circularEmitterUt(double r, double aStar) noexcept {
  if (!(r > 0.0)) {
    return 0.0;
  }
  double const invR32 = 1.0 / (r * std::sqrt(r));
  double const q = 1.0 - (3.0 / r) + (2.0 * aStar * invR32);
  if (!(q > 0.0)) {
    return 0.0;
  }
  return (1.0 + (aStar * invR32)) / std::sqrt(q);
}

/**
 * @brief Energy shift g = E_obs / E_emit for a disk emitter and a photon of
 *        angular momentum per unit energy lambda (M = 1).
 *
 * g > 1 on the approaching side (lambda > 0 for a disk orbiting in +phi).
 * Returns 0 where the emitter has no circular orbit or the photon would need
 * non-positive local energy (1 - Omega lambda <= 0).
 */
[[nodiscard]] inline double diskTransferG(double r, double aStar, double lambda) noexcept {
  double const ut = circularEmitterUt(r, aStar);
  double const denom = 1.0 - (keplerianOmega(r, aStar) * lambda);
  if (!(ut > 0.0) || !(denom > 0.0)) {
    return 0.0;
  }
  return 1.0 / (ut * denom);
}

/**
 * @brief Linear-sRGB chromaticity of a blackbody, normalized to luminance Y = 1.
 *
 * Planckian locus chromaticity (x_c, y_c) from the cubic fit of Kim et al.
 * (2002) to the CIE 1931 2-degree locus over 1667-25000 K, converted to XYZ
 * with Y = 1 and to linear sRGB
 * (D65, IEC 61966-2-1). Temperatures outside the fit range are clamped to it;
 * negative sRGB components (out of gamut below about 1900 K) clip to zero.
 * With Y = 1 the displayed luminance tracks the bolometric intensity the
 * caller multiplies in, and the temperature sets hue only.
 */
[[nodiscard]] inline std::array<double, 3> blackbodyChromaLinearSrgb(double temperatureK) noexcept {
  double const t = std::clamp(temperatureK, 1667.0, 25000.0);
  double const inv = 1.0e3 / t; // 1e3 / T keeps the powers of the fit near unity
  double const inv2 = inv * inv;
  double const inv3 = inv2 * inv;
  double const xc = t <= 4000.0
                        ? (-0.2661239 * inv3) - (0.2343589 * inv2) + (0.8776956 * inv) + 0.179910
                        : (-3.0258469 * inv3) + (2.1070379 * inv2) + (0.2226347 * inv) + 0.240390;
  double const xc2 = xc * xc;
  double const xc3 = xc2 * xc;
  double yc = 0.0;
  if (t <= 2222.0) {
    yc = (-1.1063814 * xc3) - (1.34811020 * xc2) + (2.18555832 * xc) - 0.20219683;
  } else if (t <= 4000.0) {
    yc = (-0.9549476 * xc3) - (1.37418593 * xc2) + (2.09137015 * xc) - 0.16748867;
  } else {
    yc = (3.0817580 * xc3) - (5.87338670 * xc2) + (3.75112997 * xc) - 0.37001483;
  }
  double const bigX = xc / yc;
  double const bigZ = (1.0 - xc - yc) / yc;
  double const red = (3.2404542 * bigX) - 1.5371385 - (0.4985314 * bigZ);
  double const green = (-0.9692660 * bigX) + 1.8760108 + (0.0415560 * bigZ);
  double const blue = (0.0556434 * bigX) - 0.2040259 + (1.0572252 * bigZ);
  return {std::max(red, 0.0), std::max(green, 0.0), std::max(blue, 0.0)};
}

} // namespace physics

#endif // PHYSICS_DISK_TRANSFER_H
