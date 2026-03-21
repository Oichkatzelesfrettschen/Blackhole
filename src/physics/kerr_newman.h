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
 * @param M Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param Q Electric charge [geometric units].
 * @return Delta [length^2].
 */
[[nodiscard]] constexpr double knDelta(double r, double M, double a, double Q) noexcept {
    return r * r - 2.0 * M * r + a * a + Q * Q;
}

/**
 * @brief Kerr-Newman A function: (r^2 + a^2)^2 - a^2 Delta sin^2(theta).
 *
 * A enters the g_phph and g_tph metric components.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param Q     Electric charge [geometric units].
 * @return A [length^4].
 */
[[nodiscard]] inline double knA(double r, double theta,
                                double M, double a, double Q) noexcept {
    const double r2a2  = r * r + a * a;
    const double s     = std::sin(theta);
    const double Delta = knDelta(r, M, a, Q);
    return r2a2 * r2a2 - a * a * Delta * s * s;
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
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param Q     Electric charge [geometric units].
 * @return g_tt (dimensionless in geometric units).
 */
[[nodiscard]] inline double knGtt(double r, double theta,
                                  double M, double a, double Q) noexcept {
    const double Sigma = knSigma(r, a, theta);
    const double Delta = knDelta(r, M, a, Q);
    const double s     = std::sin(theta);
    return -(Delta - a * a * s * s) / Sigma;
}

/**
 * @brief g_rr = Sigma / Delta.
 *
 * Diverges at the horizons (Delta = 0) -- a coordinate singularity, not a
 * curvature singularity.  Unchanged in form from Kerr; only Delta is modified.
 *
 * @param r Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param Q Electric charge [geometric units].
 * @return g_rr [dimensionless in geometric units].
 */
[[nodiscard]] inline double knGrr(double r, double theta,
                                  double M, double a, double Q) noexcept {
    const double Delta = knDelta(r, M, a, Q);
    if (std::abs(Delta) < 1.0e-30) return std::numeric_limits<double>::infinity();
    return knSigma(r, a, theta) / Delta;
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
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param Q     Electric charge [geometric units].
 * @return g_phph [length^2 in geometric units].
 */
[[nodiscard]] inline double knGphph(double r, double theta,
                                    double M, double a, double Q) noexcept {
    const double Sigma = knSigma(r, a, theta);
    const double A     = knA(r, theta, M, a, Q);
    const double s     = std::sin(theta);
    return A * s * s / Sigma;
}

/**
 * @brief g_t_phi = -2 M r a sin^2(theta) / Sigma  (frame-dragging cross term).
 *
 * WHY the charge Q does not appear here: the off-diagonal mixing between t
 * and phi arises from angular momentum, not charge.  The electromagnetic
 * field enters only through Delta (in g_tt and g_rr).  This is exact --
 * not an approximation.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @return g_tph [length^2 in geometric units].
 */
[[nodiscard]] inline double knGtph(double r, double theta,
                                   double M, double a) noexcept {
    const double Sigma = knSigma(r, a, theta);
    const double s     = std::sin(theta);
    return -2.0 * M * r * a * s * s / Sigma;
}

// ============================================================================
// Horizon radii
// ============================================================================

/**
 * @brief Outer (event) horizon: r_+ = M + sqrt(M^2 - a^2 - Q^2).
 *
 * Returns NaN when M^2 < a^2 + Q^2 (super-extremal -- naked singularity).
 * At extremality (M^2 = a^2 + Q^2) the two horizons merge at r = M.
 *
 * @param M Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param Q Electric charge [geometric units].
 * @return r_+ [geometric units], or NaN for naked singularity.
 */
[[nodiscard]] inline double knOuterHorizon(double M, double a, double Q) noexcept {
    const double disc = M * M - a * a - Q * Q;
    if (disc < 0.0) return std::numeric_limits<double>::quiet_NaN();
    return M + std::sqrt(disc);
}

/**
 * @brief Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2 - Q^2).
 *
 * The Cauchy horizon is the boundary beyond which predictability breaks down
 * (strong cosmic censorship conjecture).  Uncharged Kerr has a Cauchy horizon;
 * Reissner-Nordstrom also has one for Q < M.
 *
 * @param M Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param Q Electric charge [geometric units].
 * @return r_- [geometric units], or NaN for naked singularity.
 */
[[nodiscard]] inline double knInnerHorizon(double M, double a, double Q) noexcept {
    const double disc = M * M - a * a - Q * Q;
    if (disc < 0.0) return std::numeric_limits<double>::quiet_NaN();
    return M - std::sqrt(disc);
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
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param Q     Electric charge [geometric units].
 * @return Ergosphere boundary radius [geometric units].
 */
[[nodiscard]] inline double knErgosphereRadius(double theta,
                                               double M, double a, double Q) noexcept {
    const double c    = std::cos(theta);
    const double disc = M * M - a * a * c * c - Q * Q;
    if (disc < 0.0) return std::numeric_limits<double>::quiet_NaN();
    return M + std::sqrt(disc);
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
 * @param Q     Electric charge [geometric units].
 * @return A_t [geometric units].
 */
[[nodiscard]] inline double knElectricPotentialAt(double r, double theta,
                                                  double a, double Q) noexcept {
    const double Sigma = knSigma(r, a, theta);
    return -Q * r / Sigma;
}

/**
 * @brief Azimuthal EM 4-potential: A_phi = Q r a sin^2(theta) / Sigma.
 *
 * The phi component arises from the spin of the charge distribution.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param a     Spin parameter [geometric units].
 * @param Q     Electric charge [geometric units].
 * @return A_phi [geometric units].
 */
[[nodiscard]] inline double knMagneticPotentialPhi(double r, double theta,
                                                   double a, double Q) noexcept {
    const double Sigma = knSigma(r, a, theta);
    const double s     = std::sin(theta);
    return Q * r * a * s * s / Sigma;
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
 * @param M Geometric mass [geometric units].
 * @param a Spin parameter [geometric units].
 * @param Q Electric charge [geometric units].
 * @return true if a physical black hole exists.
 */
[[nodiscard]] constexpr bool knSubExtremal(double M, double a, double Q) noexcept {
    return M * M >= a * a + Q * Q;
}

/**
 * @brief Frame-dragging angular velocity: Omega = -g_tph / g_phph.
 *
 * This is the angular velocity of a zero-angular-momentum observer (ZAMO).
 * Identical in form to Kerr; charge enters implicitly through Delta inside A.
 *
 * @param r     Boyer-Lindquist r [geometric units].
 * @param theta Polar angle [rad].
 * @param M     Geometric mass [geometric units].
 * @param a     Spin parameter [geometric units].
 * @param Q     Electric charge [geometric units].
 * @return Omega_ZAMO [1/length in geometric units].
 */
[[nodiscard]] inline double knFrameDragging(double r, double theta,
                                            double M, double a, double Q) noexcept {
    const double A     = knA(r, theta, M, a, Q);
    if (std::abs(A) < 1.0e-30) return 0.0;
    return 2.0 * M * r * a / A;
}

} // namespace physics

#endif // PHYSICS_KERR_NEWMAN_H
