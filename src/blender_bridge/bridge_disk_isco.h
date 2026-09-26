/**
 * @file bridge_disk_isco.h
 * @brief Inner edge of the Blender bridge's accretion disk, in units of M.
 *
 * The disk orbits with angular momentum along +z and the spin a* is signed:
 * a* > 0 co-rotates with the disk and a* < 0 counter-rotates with it. The
 * Bardeen-Press-Teukolsky (1972) radius
 *
 *   r_isco = M (3 + Z2 - sign(a*) sqrt((3 - Z1)(3 + Z1 + 2 Z2)))
 *
 * therefore equals physics::kerrIscoRadius(mass, a, true) and
 * bhbKerrIsco(a*, 1): 2.3209 M at a* = 0.9 and 8.7174 M at a* = -0.9.
 *
 * The function is plain host code in float so that cuda_renderer.cu, compiled
 * by nvcc as C++17, and the host tests share one definition.
 */

#ifndef BLACKHOLE_BLENDER_BRIDGE_DISK_ISCO_H
#define BLACKHOLE_BLENDER_BRIDGE_DISK_ISCO_H

#include <cmath>

namespace bridge {

/**
 * @brief ISCO of the +z disk around a hole of signed spin @p aStar, in units of M.
 *
 * @param aStar Dimensionless signed spin in [-1, 1]
 * @return r_isco / M: 6 at a* = 0, below 6 for a* > 0, above 6 for a* < 0
 */
[[nodiscard]] inline float diskIscoOverM(float aStar) noexcept {
  float const oneMinusA2 = 1.0f - (aStar * aStar);
  float const z1 =
      1.0f + (std::cbrt(oneMinusA2) * (std::cbrt(1.0f + aStar) + std::cbrt(1.0f - aStar)));
  float const z2 = std::sqrt((3.0f * aStar * aStar) + (z1 * z1));
  // 3 - Z1 vanishes at a* = 0; the clamp keeps a rounded-negative product out of sqrt.
  float const root = std::sqrt(std::fmax(0.0f, (3.0f - z1) * (3.0f + z1 + (2.0f * z2))));
  return (aStar >= 0.0f) ? (3.0f + z2 - root) : (3.0f + z2 + root);
}

} // namespace bridge

#endif // BLACKHOLE_BLENDER_BRIDGE_DISK_ISCO_H
