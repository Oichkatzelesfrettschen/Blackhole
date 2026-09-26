/**
 * @file photon_ring.h
 * @brief Kerr photon shell: bound spherical photon orbits and their Lyapunov exponent.
 *
 * Geometric units G = c = M = 1. A bound photon orbit of radius r in the
 * photon shell r_+ <= r <= r_- (prograde and retrograde equatorial orbits at
 * the ends) has the critical conserved quantities (Bardeen 1973)
 *
 *   lambda = a + r (r - 2 Delta / (r - 1)) / a,
 *   eta    = r^3 (4 Delta / (r - 1)^2 - r) / a^2,    Delta = r^2 - 2r + a^2.
 *
 * A neighboring ray departs from the orbit as delta r_n = e^{gamma n} delta r_0
 * per half libration in theta, which makes gamma the demagnification exponent
 * between successive photon subrings. Johnson et al. (2020, Sci. Adv. 6,
 * eaaz1310) and Gralla & Lupsasca (2020, PRD 101, 044031) give
 *
 *   gamma = 4 r sqrt(chi) K(u_+ / u_-) / sqrt(-u_- a^2),
 *   chi   = 1 - Delta / (r (r - 1)^2),
 *   u_+-  = Delta_theta +- sqrt(Delta_theta^2 + eta / a^2),
 *   Delta_theta = (1 - (eta + lambda^2) / a^2) / 2,
 *
 * where 4 r sqrt(chi) = sqrt(2 R''(r)) of the radial potential and
 * 2 K(u_+/u_-) / sqrt(-u_- a^2) is the Mino time of one half libration. The
 * code forms a^2 u_- = h - sqrt(h^2 + a^2 eta) with h = (a^2 - eta - lambda^2)/2
 * and u_+ / u_- = -a^2 eta / (a^2 u_-)^2, so neither root divides by a^2 and
 * gamma -> pi continuously as a -> 0. K(m) for the negative parameter
 * m = u_+/u_- is Carlson's R_F(0, 1 - m, 1).
 */

#ifndef PHYSICS_PHOTON_RING_H
#define PHYSICS_PHOTON_RING_H

#include <algorithm>
#include <cmath>
#include <numbers>

#include "elliptic_integrals.h"
#include "safe_limits.h"

namespace physics {

/// Radii bounding the Kerr photon shell, M = 1.
struct PhotonShell {
  double prograde = 3.0;   ///< r_+, equatorial prograde photon orbit
  double retrograde = 3.0; ///< r_-, equatorial retrograde photon orbit
};

/**
 * @brief Photon shell bounds r_+- = 2 (1 + cos((2/3) acos(-+|a|))), M = 1.
 * @param a Spin, |a| <= 1
 */
[[nodiscard]] inline PhotonShell photonShell(double a) noexcept {
  const double s = std::min(std::abs(a), 1.0);
  return {.prograde = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(-s))),
          .retrograde = 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(s)))};
}

/**
 * @brief Lyapunov exponent gamma of the bound photon orbit at radius r, M = 1.
 *
 * @param a Spin, |a| < 1; gamma depends on a^2 and lambda^2 only
 * @param r Orbit radius inside the photon shell of a (r = 3 at a = 0)
 * @return gamma per half orbit; pi for Schwarzschild; divergentResult<double>(),
 *         a finite sentinel safe under -ffast-math, when r lies outside the
 *         shell (eta < 0)
 */
[[nodiscard]] inline double photonRingLyapunovExponent(double a, double r) noexcept {
  const double a2 = a * a;
  if (a2 == 0.0) {
    return std::numbers::pi;
  }
  const double rm1 = r - 1.0;
  const double rm3 = r - 3.0;
  const double delta = (r * r) - (2.0 * r) + a2;
  // eta and lambda with the O(a^2) cancellations expanded away:
  // 4 Delta - r (r - 1)^2 = 4 a^2 - r (r - 3)^2 and
  // a^2 (r - 1) - r (r (r - 1) - 2 Delta) = -(r^2 (r - 3) + a^2 (r + 1)).
  const double eta = r * r * r * ((4.0 * a2) - (r * rm3 * rm3)) / (a2 * rm1 * rm1);
  if (!(eta >= 0.0)) {
    return divergentResult<double>();
  }
  const double lambda = -((r * r * rm3) + (a2 * (r + 1.0))) / (a * rm1);
  const double chi = 1.0 - (delta / (r * rm1 * rm1));
  const double h = 0.5 * (a2 - eta - (lambda * lambda));
  const double a2uMinus = h - std::sqrt((h * h) + (a2 * eta)); // a^2 u_- < 0
  const double m = -a2 * eta / (a2uMinus * a2uMinus);          // u_+ / u_- <= 0
  const double kComplete = carlsonRf(0.0, 1.0 - m, 1.0);
  return 4.0 * r * std::sqrt(chi) * kComplete / std::sqrt(-a2uMinus);
}

} // namespace physics

#endif // PHYSICS_PHOTON_RING_H
