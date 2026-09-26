/**
 * @file kerr_newman.h
 * @brief Kerr-Newman metric for rotating, electrically charged black holes.
 *
 * WHY: The Kerr-Newman family is the most general stationary, axially
 * symmetric, electrovacuum solution to the Einstein-Maxwell equations
 * (Newman et al. 1965).  It reduces exactly to Kerr when Q = 0 and to
 * Reissner-Nordstrom when a = 0, providing a continuous family that
 * brackets both astrophysically relevant limits.  This header exposes the
 * complete metric in Boyer-Lindquist coordinates for use in geodesic
 * integration, horizon detection, and EHT shadow modelling.
 *
 * WHAT: Line element in geometric units (G = c = 1):
 *
 *   ds^2 = -(Delta - a^2 sin^2 theta)/Sigma dt^2
 *        - 2a sin^2 theta (r^2 + a^2 - Delta)/Sigma dt dphi
 *        + Sigma/Delta dr^2
 *        + Sigma dtheta^2
 *        + ((r^2 + a^2)^2 - Delta a^2 sin^2 theta)/Sigma sin^2 theta dphi^2
 *
 * where:
 *   Sigma  = r^2 + a^2 cos^2(theta)
 *   Delta  = r^2 - 2 M r + a^2 + Q^2          (charge Q modifies horizon)
 *   A      = (r^2 + a^2)^2 - a^2 Delta sin^2(theta)
 *   M      = geometric mass [length]
 *   a      = J/M = spin parameter [length]  (|a| <= M for sub-extremal)
 *   Q      = electric charge [length]       (a^2 + Q^2 <= M^2 required)
 *
 * All coordinates and parameters are in geometric units (G = c = 1) so that
 * M, a, Q, and r share the same dimension [length].
 *
 * HOW: Include this header and call the functions in the physics:: namespace.
 * All functions are [[nodiscard]] inline and carry no state.
 * For CGS unit inputs, convert via M_geom = G*M_cgs/c^2 before calling.
 *
 * References:
 *   - Newman, E. et al. (1965). J. Math. Phys. 6, 918 -- original solution
 *   - Carter, B. (1968). Phys. Rev. 174, 1559 -- separability, Carter constant
 *   - Wald, R. M. (1984). General Relativity, Chap. 12
 *   - Misner, Thorne & Wheeler (1973). Gravitation, sec. 33.2
 */

#ifndef PHYSICS_KERR_NEWMAN_H
#define PHYSICS_KERR_NEWMAN_H

#include <cmath>
#include <limits>

#include "verified/kerr_newman.hpp"

namespace physics {

// ============================================================================
// Curvature scalars
// ============================================================================

/**
 * @brief Kerr-Newman Sigma: r^2 + a^2 cos^2(theta).
 *
 * Sigma is unchanged from pure Kerr -- the electric charge Q does not appear.
 * It vanishes only at the ring singularity (r = 0, theta = pi/2).
 *
 * @param r     Boyer-Lindquist radial coordinate [geometric units].
 * @param a     Spin parameter J/M [geometric units].
 * @param theta Polar angle [rad].
 * @return Sigma [length^2].
 */
[[nodiscard]] inline double knSigma(double r, double a, double theta) noexcept {
    const double c = std::cos(theta);
    return r * r + a * a * c * c;
}

/**
 * @brief Kerr-Newman Delta: r^2 - 2 M r + a^2 + Q^2.
 *
 * Delta is the radial discriminant: its two real roots (when M^2 >= a^2 + Q^2)
 * are the outer (event) and inner (Cauchy) horizon radii.  The Q^2 term raises
 * both horizons inward relative to uncharged Kerr.
 *
 * @param r Boyer-Lindquist r [geometric units].
 * @param mass Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param charge Electric charge [geometric units].
 * @return Delta [length^2].
 */
[[nodiscard]] constexpr double knDelta(double r, double mass, double a, double charge) noexcept {
  return r * r - 2.0 * mass * r + a * a + charge * charge;
}

/**
 * @brief Kerr-Newman A function: (r^2 + a^2)^2 - a^2 Delta sin^2(theta).
 *
 * A enters the g_phph and g_tph metric components.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param mass     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return A [length^4].
 */
[[nodiscard]] inline double knA(double r, double theta, double mass, double a,
                                double charge) noexcept {
  const double r2a2 = r * r + a * a;
  const double s = std::sin(theta);
  const double delta = knDelta(r, mass, a, charge);
  return r2a2 * r2a2 - a * a * delta * s * s;
}

// ============================================================================
// Metric components in Boyer-Lindquist coordinates
// ============================================================================

/**
 * @brief g_tt = -(Delta - a^2 sin^2 theta) / Sigma.
 *
 * Equivalent to -(1 - (2 M r - Q^2)/Sigma).  When Q = 0 this reduces to
 * the Kerr g_tt.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param mass     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return g_tt (dimensionless in geometric units).
 */
[[nodiscard]] inline double knGtt(double r, double theta, double mass, double a,
                                  double charge) noexcept {
  const double sigma = knSigma(r, a, theta);
  const double delta = knDelta(r, mass, a, charge);
  const double s = std::sin(theta);
  return -(delta - a * a * s * s) / sigma;
}

/**
 * @brief g_rr = Sigma / Delta.
 *
 * Diverges at the horizons (Delta = 0) -- a coordinate singularity, not a
 * curvature singularity.  Unchanged in form from Kerr; only Delta is modified.
 *
 * @param r Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param mass Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param charge Electric charge [geometric units].
 * @return g_rr [dimensionless in geometric units].
 */
[[nodiscard]] inline double knGrr(double r, double theta, double mass, double a,
                                  double charge) noexcept {
  const double delta = knDelta(r, mass, a, charge);
  if (std::abs(delta) < 1.0e-30) {
    return std::numeric_limits<double>::infinity();
  }
  return knSigma(r, a, theta) / delta;
}

/**
 * @brief g_theta_theta = Sigma.
 *
 * The polar component is purely Sigma, identical to Kerr.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param theta Polar angle [rad].
 * @return g_thth [length^2 in geometric units].
 */
[[nodiscard]] inline double knGthth(double r, double a, double theta) noexcept {
    return knSigma(r, a, theta);
}

/**
 * @brief g_phi_phi = A sin^2(theta) / Sigma.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param mass     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return g_phph [length^2 in geometric units].
 */
[[nodiscard]] inline double knGphph(double r, double theta, double mass, double a,
                                    double charge) noexcept {
  const double sigma = knSigma(r, a, theta);
  const double metricA = knA(r, theta, mass, a, charge);
  const double s = std::sin(theta);
  return metricA * s * s / sigma;
}

/**
 * @brief g_t_phi = -a (2 M r - Q^2) sin^2(theta) / Sigma  (frame-dragging cross term).
 *
 * The Carter form -(Delta/Sigma)(dt - a sin^2 dphi)^2
 * + (sin^2/Sigma)((r^2 + a^2) dphi - a dt)^2 gives
 * g_tph = a sin^2 (Delta - r^2 - a^2) / Sigma, and Delta carries Q^2, so the
 * cross term is -a (2 M r - Q^2) sin^2 / Sigma. At Q = 0 it is the Kerr term.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param mass     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return g_tph [length in geometric units].
 */
[[nodiscard]] inline double knGtph(double r, double theta, double mass, double a,
                                   double charge) noexcept {
  const double sigma = knSigma(r, a, theta);
  const double s = std::sin(theta);
  return -a * (2.0 * mass * r - charge * charge) * s * s / sigma;
}

// ============================================================================
// Horizon radii
// ============================================================================

/**
 * @brief Outer (event) horizon: r_+ = M + sqrt(M^2 - a^2 - Q^2).
 *
 * Returns NaN when M^2 < a^2 + Q^2 (super-extremal -- naked singularity).
 * At extremality (M^2 = a^2 + Q^2) the two horizons merge at r = M; the
 * discriminant comes from verified::knHorizonDiscriminant, which reads a
 * rounding-level negative value as that extremal zero.
 *
 * @param mass Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param charge Electric charge [geometric units].
 * @return r_+ [geometric units], or NaN for naked singularity.
 */
[[nodiscard]] inline double knOuterHorizon(double mass, double a, double charge) noexcept {
  const double disc = verified::knHorizonDiscriminant(mass, a, charge);
  if (disc < 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return mass + std::sqrt(disc);
}

/**
 * @brief Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2 - Q^2).
 *
 * The Cauchy horizon is the boundary beyond which predictability breaks down
 * (strong cosmic censorship conjecture).  Uncharged Kerr has a Cauchy horizon;
 * Reissner-Nordstrom also has one for Q < M.
 *
 * @param mass Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param charge Electric charge [geometric units].
 * @return r_- [geometric units], or NaN for naked singularity.
 */
[[nodiscard]] inline double knInnerHorizon(double mass, double a, double charge) noexcept {
  const double disc = verified::knHorizonDiscriminant(mass, a, charge);
  if (disc < 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return mass - std::sqrt(disc);
}

// ============================================================================
// Ergosphere
// ============================================================================

/**
 * @brief Ergosphere radius: r_ergo(theta) = M + sqrt(M^2 - a^2 cos^2(theta) - Q^2).
 *
 * The ergosphere is where g_tt = 0, i.e., Delta = a^2 sin^2(theta), which
 * gives the condition Sigma = 2 M r - Q^2, or equivalently the formula above.
 * At the poles (theta = 0, pi) the ergosphere touches the outer horizon.
 *
 * @param theta Polar angle [rad].
 * @param mass     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return Ergosphere boundary radius [geometric units].
 */
[[nodiscard]] inline double knErgosphereRadius(double theta, double mass, double a,
                                               double charge) noexcept {
  const double c = std::cos(theta);
  const double disc = verified::knHorizonDiscriminant(mass, a * c, charge);
  if (disc < 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return mass + std::sqrt(disc);
}

// ============================================================================
// Electromagnetic 4-potential
// ============================================================================

/**
 * @brief Time component of the EM 4-potential: A_t = -Q r / Sigma.
 *
 * In Boyer-Lindquist coordinates, the KN electromagnetic vector potential is
 *   A_mu = Q r / Sigma * (dt - a sin^2(theta) dphi).
 * A_t describes the Coulomb-like radial electric field.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return A_t [geometric units].
 */
[[nodiscard]] inline double knElectricPotentialAt(double r, double theta, double a,
                                                  double charge) noexcept {
  const double sigma = knSigma(r, a, theta);
  return -charge * r / sigma;
}

/**
 * @brief Azimuthal EM 4-potential: A_phi = Q r a sin^2(theta) / Sigma.
 *
 * The phi component arises from the spin of the charge distribution.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return A_phi [geometric units].
 */
[[nodiscard]] inline double knMagneticPotentialPhi(double r, double theta, double a,
                                                   double charge) noexcept {
  const double sigma = knSigma(r, a, theta);
  const double s = std::sin(theta);
  return charge * r * a * s * s / sigma;
}

// ============================================================================
// Physical validity and limit checks
// ============================================================================

/**
 * @brief True when M^2 >= a^2 + Q^2 (sub-extremal or extremal black hole).
 *
 * Violations produce a naked singularity -- unphysical under the Cosmic
 * Censorship Conjecture.
 *
 * @param mass Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param charge Electric charge [geometric units].
 * @return true if a physical black hole exists.
 */
[[nodiscard]] constexpr bool knSubExtremal(double mass, double a, double charge) noexcept {
  return verified::knHorizonDiscriminant(mass, a, charge) >= 0.0;
}

/**
 * @brief Frame-dragging angular velocity: Omega = -g_tph / g_phph = a (2 M r - Q^2) / A.
 *
 * This is the angular velocity of a zero-angular-momentum observer (ZAMO).
 * Charge enters through Delta inside A and through the 2 M r - Q^2 factor of
 * g_tph.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param mass     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param charge     Electric charge [geometric units].
 * @return Omega_ZAMO [1/length in geometric units].
 */
[[nodiscard]] inline double knFrameDragging(double r, double theta, double mass, double a,
                                            double charge) noexcept {
  const double metricA = knA(r, theta, mass, a, charge);
  if (std::abs(metricA) < 1.0e-30) {
    return 0.0;
  }
  return a * (2.0 * mass * r - charge * charge) / metricA;
}

} // namespace physics

#endif // PHYSICS_KERR_NEWMAN_H
