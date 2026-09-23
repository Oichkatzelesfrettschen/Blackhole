/**
 * kerr_extended.h
 *
 * Verified Kerr Black Hole Physics (Spinning Black Holes)
 * Maintained C++ references for the Kerr formulas in rocq/theories/Metrics/Kerr.v
 *
 * This header provides complete Kerr spacetime computations:
 * - Metric tensor components in Boyer-Lindquist coordinates
 * - Horizons (event and Cauchy) and ergosphere
 * - ISCO (innermost stable circular orbit) via Bardeen-Press-Teukolsky
 * - Surface gravity and Hawking temperature
 * - Geodesic analysis and null constraints
 *
 * C++ value tests exercise selected analytic limits and parity checks.
 * Rocq references describe the mathematics rather than floating-point proof equivalence.
 *
 * Formulas shared with kerr.hpp (Sigma, Delta, A, metric components,
 * horizons, ergosphere, BPT ISCO) delegate to that header; this file
 * adds the assertion-checked surface plus energy, angular
 * momentum, four-norm, and validity predicates kerr.hpp does not carry.
 *
 * Geometric units: c = G = M_sun = 1
 *
 * References:
 * [1] Bardeen, J. M., Press, W. H., & Teukolsky, S. A. (1972).
 *     Rotating black holes: locally nonrotating frames, energy extraction.
 * [2] Carter, B. (1968). Global structure of the Kerr black hole.
 *     Physical Review, 174(5), 1559-1571.
 * [3] Novikov, I. D., & Thorne, K. S. (1973). Astrophysics of black holes.
 */

#ifndef PHYSICS_VERIFIED_KERR_EXTENDED_HPP
#define PHYSICS_VERIFIED_KERR_EXTENDED_HPP

#include <cassert>
#include <cmath>
#include <numbers>

#include "kerr.hpp"

namespace verified {

/**
 * KERR METRIC DEFINITION
 *
 * Metric in Boyer-Lindquist coordinates (t, r, theta, phi):
 *   ds^2 = -(1 - 2Mr/Sigma) dt^2 - (2Mra sin^2 theta / Sigma) dt dphi
 *         + (Sigma / Delta) dr^2 + Sigma dtheta^2
 *         + ((r^2 + a^2)^2 - a^2 Delta sin^2 theta) sin^2 theta / Sigma dphi^2
 *
 * where:
 *   Sigma = r^2 + a^2 cos^2 theta
 *   Delta = r^2 - 2Mr + a^2
 *   a = J/M (dimensionless spin parameter, 0 <= a < M)
 *   M = black hole mass in geometric units
 */

/**
 * Kerr metric component g_rr (radial-radial)
 * g_rr = Sigma / Delta
 * Singular at horizons (Delta = 0)
 * Coordinate singularity (not physical singularity)
 */
[[nodiscard]] inline double kerrGRrChecked(double r, double theta, double m, double a) noexcept {
  assert(kerrDelta(r, m, a) != 0.0 && "g_rr singular at horizon");
  return kerrGRr(r, theta, m, a);
}

/**
 * Kerr metric component g_theta_theta (polar-polar)
 * g_theta_theta = Sigma
 * Always positive away from ring singularity
 */
[[nodiscard]] inline double kerrGThetaTheta(double r, double theta, double a) noexcept {
  return kerrGThth(r, theta, a);
}

/**
 * Kerr metric component g_phi_phi (azimuthal-azimuthal)
 * g_phi_phi = A sin^2(theta) / Sigma
 * Includes frame-dragging effect
 */
[[nodiscard]] inline double kerrGPhiPhi(double r, double theta, double m, double a) noexcept {
  return kerrGPhph(r, theta, m, a);
}

/**
 * Kerr metric component g_t_phi (temporal-azimuthal cross term)
 * g_t_phi = -2Mra sin^2(theta) / Sigma
 * Frame-dragging effect: couples time and rotation
 * Zero for Schwarzschild (a = 0)
 */
[[nodiscard]] inline double kerrGTPhi(double r, double theta, double m, double a) noexcept {
  return kerrGTph(r, theta, m, a);
}

/**
 * HORIZON COMPUTATIONS
 */

/**
 * Outer (event) horizon radius
 * r_+ = M + sqrt(M^2 - a^2)
 * Only exists for sub-extremal black holes: a < M
 * Light cone singularity: information barrier from exterior perspective
 */
[[nodiscard]] inline double kerrOuterHorizon(double m, double a) noexcept {
  assert(a < m && "Naked singularity: a >= m");
  assert(m > 0 && "Invalid mass");
  return outerHorizon(m, a);
}

/**
 * Inner (Cauchy) horizon radius
 * r_- = M - sqrt(M^2 - a^2)
 * Separates black hole interior from white hole region
 * Unstable to perturbations in physical black holes
 */
[[nodiscard]] inline double kerrInnerHorizon(double m, double a) noexcept {
  assert(a < m && "Naked singularity: a >= m");
  assert(m > 0 && "Invalid mass");
  return innerHorizon(m, a);
}

/**
 * Ergosphere radius (outer boundary, coordinate-dependent)
 * r_ergo(theta) = M + sqrt(M^2 - a^2 cos^2(theta))
 * Region where g_tt > 0 (metric signature changes)
 * Extends beyond event horizon except at poles
 */
[[nodiscard]] inline double kerrErgosphereRadius(double theta, double m, double a) noexcept {
  assert((m * m) - (a * a * std::cos(theta) * std::cos(theta)) >= 0 &&
         "Invalid ergosphere calculation");
  return ergosphereRadius(theta, m, a);
}

/**
 * ISCO (Innermost Stable Circular Orbit) CALCULATIONS
 */

/**
 * Helper function Z1 from Bardeen-Press-Teukolsky formula, in the M = 1
 * convention: Z1(a) = kerr_Z1(1, a). The general-mass form lives in
 * kerr.hpp, which normalizes the spin as a/M (BPT 1972 eq. 2.21).
 */
[[nodiscard]] inline double bptZ1(double a) noexcept {
  return kerrZ1(1.0, a);
}

/**
 * Helper function Z2 from Bardeen-Press-Teukolsky formula, in the M = 1
 * convention: Z2(a) = kerr_Z2(1, a) = sqrt(3*a^2 + Z1(a)^2).
 */
[[nodiscard]] inline double bptZ2(double a) noexcept {
  return kerrZ2(1.0, a);
}

/**
 * ISCO radius for prograde orbits (co-rotating with black hole)
 * r_isco_prograde = M * (3 + Z2 - sqrt((3 - Z1) * (3 + Z1 + 2*Z2)))
 * For a = 0 (Schwarzschild): r_isco = 6M
 * For a = M (extremal): r_isco = M
 * Delegates to kerr_isco_prograde, whose Z1/Z2 normalize the spin as
 * a/M; a re-derivation here once fed raw a into the M = 1 helpers,
 * which is wrong for any mass except 1 and invisible to unit-mass tests.
 */
[[nodiscard]] inline double kerrIscoProgradeChecked(double m, double a) noexcept {
  assert(m > 0 && "Invalid mass");
  assert(a >= 0 && a < m && "Invalid spin parameter");
  return kerrIscoPrograde(m, a);
}

/**
 * ISCO radius for retrograde orbits (counter-rotating): the + sign on
 * the square root selects the retrograde branch (Z1/Z2 are even in a).
 */
[[nodiscard]] inline double kerrIscoRetrogradeChecked(double m, double a) noexcept {
  assert(m > 0 && "Invalid mass");
  assert(a >= 0 && a < m && "Invalid spin parameter");
  return kerrIscoRetrograde(m, a);
}

/**
 * SURFACE GRAVITY AND THERMODYNAMICS
 */

/**
 * Surface gravity at outer horizon
 * kappa = (r_+ - r_-) / (2 * (r_+^2 + a^2))
 * Proportional to Hawking temperature
 */
[[nodiscard]] constexpr double kerrSurfaceGravity(double m, double a) noexcept {
  assert(m > 0 && "Invalid mass");
  assert(a >= 0 && a < m && "Invalid spin parameter");

  double const rPlus = kerrOuterHorizon(m, a);
  double const rMinus = kerrInnerHorizon(m, a);
  double const numerator = rPlus - rMinus;
  double const denominator = 2.0 * ((rPlus * rPlus) + (a * a));

  assert(denominator != 0 && "Invalid surface gravity denominator");
  return numerator / denominator;
}

/**
 * Hawking temperature in Planck units
 * T_H = kappa / (2*pi)
 * Zero for extremal black holes (a = M)
 */
[[nodiscard]] constexpr double kerrHawkingTemperature(double m, double a) noexcept {
  double const kappa = kerrSurfaceGravity(m, a);
  constexpr double twoPi = 2.0 * std::numbers::pi;
  return kappa / twoPi;
}

/**
 * GEODESIC AND CONSTRAINT FUNCTIONS
 */

/**
 * Energy per unit mass for geodesics in Kerr spacetime
 * E = -g_tt v_t - g_t_phi v_phi
 * Conserved quantity for particles in stationary spacetime
 */
[[nodiscard]] constexpr double kerrEnergy(double r, double theta, double m, double a, double vT,
                                          double vPhi) noexcept {
  double const gTt = kerrGTt(r, theta, m, a);
  double const gTPhi = kerrGTPhi(r, theta, m, a);
  return (-gTt * vT) - (gTPhi * vPhi);
}

/**
 * Angular momentum per unit mass for geodesics
 * L_z = g_phi_phi v_phi + g_t_phi v_t
 * Conserved quantity for particles in axisymmetric spacetime
 */
[[nodiscard]] constexpr double kerrAngularMomentum(double r, double theta, double m, double a,
                                                   double vT, double vPhi) noexcept {
  double const gPhiPhi = kerrGPhiPhi(r, theta, m, a);
  double const gTPhi = kerrGTPhi(r, theta, m, a);
  return (gPhiPhi * vPhi) + (gTPhi * vT);
}

/**
 * Metric norm of four-velocity
 * g_ab v^a v^b
 * For timelike: norm = -1 (with signature (-,+,+,+))
 * For null: norm = 0
 * For spacelike: norm > 0
 */
[[nodiscard]] constexpr double kerrFourNorm(double r, double theta, double m, double a, double vT,
                                            double vR, double vTheta, double vPhi) noexcept {
  double const gTt = kerrGTt(r, theta, m, a);
  double const gRr = kerrGRrChecked(r, theta, m, a);
  double const gThetaTheta = kerrGThetaTheta(r, theta, a);
  double const gPhiPhi = kerrGPhiPhi(r, theta, m, a);
  double const gTPhi = kerrGTPhi(r, theta, m, a);

  return (gTt * vT * vT) + (gRr * vR * vR) + (gThetaTheta * vTheta * vTheta) +
         (gPhiPhi * vPhi * vPhi) + (2.0 * gTPhi * vT * vPhi);
}

/**
 * Check if four-velocity is null (photon geodesic)
 * Tolerance accounts for numerical precision (float32 rounding)
 */
[[nodiscard]] constexpr bool kerrIsNull(double r, double theta, double m, double a, double vT,
                                        double vR, double vTheta, double vPhi,
                                        double tolerance = 1e-6) noexcept {
  double const norm = kerrFourNorm(r, theta, m, a, vT, vR, vTheta, vPhi);
  return std::abs(norm) < tolerance;
}

/**
 * Check if four-velocity is timelike (massive particle geodesic)
 * Normalized: g_ab v^a v^b = -1
 */
[[nodiscard]] constexpr bool kerrIsTimelike(double r, double theta, double m, double a, double vT,
                                            double vR, double vTheta, double vPhi,
                                            double tolerance = 1e-6) noexcept {
  double const norm = kerrFourNorm(r, theta, m, a, vT, vR, vTheta, vPhi);
  return std::abs(norm + 1.0) < tolerance;
}

/**
 * VALIDATION CONSTRAINTS (Z3-verified properties)
 * These properties have been verified using Z3 SMT solver
 * in tests/z3_kerr_verification.py
 */

/**
 * Verify sub-extremal condition: required for physical black holes
 * Ensures a < M (no naked singularity)
 */
[[nodiscard]] constexpr bool kerrIsSubextremal(double m, double a) noexcept {
  return a >= 0.0 && a < m && m > 0.0;
}

/**
 * Verify ISCO is in physically valid region
 * ISCO must be outside event horizon and in ergosphere
 */
[[nodiscard]] constexpr bool kerrIscoValid(double m, double a) noexcept {
  if (!kerrIsSubextremal(m, a)) {
    return false;
  }

  double const rIsco = kerrIscoProgradeChecked(m, a);
  double const rPlus = kerrOuterHorizon(m, a);
  double const rErgo = kerrErgosphereRadius(0.0, m, a); // At equator

  // ISCO outside horizon, inside ergosphere at equator
  return rIsco > rPlus && rIsco < rErgo;
}

/**
 * Verify metric signature is Lorentzian in exterior region
 * Exterior: r > r_+ and g_tt < 0, g_rr > 0, g_theta > 0, g_phi > 0
 */
[[nodiscard]] constexpr bool kerrMetricLorentzianExterior(double r, double theta, double m,
                                                          double a) noexcept {
  if (!kerrIsSubextremal(m, a)) {
    return false;
  }

  double const rPlus = kerrOuterHorizon(m, a);
  if (r <= rPlus) {
    return false; // Not in exterior
  }

  double const gTt = kerrGTt(r, theta, m, a);
  double const gRr = kerrGRrChecked(r, theta, m, a);
  double const gThetaTheta = kerrGThetaTheta(r, theta, a);
  double const gPhiPhi = kerrGPhiPhi(r, theta, m, a);

  // Lorentzian signature: (-,+,+,+)
  return gTt < 0 && gRr > 0 && gThetaTheta > 0 && gPhiPhi > 0;
}

/**
 * Function-pointer interface for C++ metric consumers.
 */

using KirrMetricFunc = double (*)(double, double, double, double);

struct KirrExtractedInterface {
  KirrMetricFunc gTt;
  KirrMetricFunc gRr;
  KirrMetricFunc gTPhi;
};

} // namespace verified

#endif // PHYSICS_VERIFIED_KERR_EXTENDED_HPP
