/**
 * @file coordinates.h
 * @brief Coordinate transformations for black hole spacetimes.
 *
 * Provides conversions between different coordinate systems:
 * - Boyer-Lindquist (BL): Standard spherical-like coordinates
 * - Modified Kerr-Schild (MKS): Horizon-penetrating with logarithmic radial
 * - Cartesian: Observer coordinates
 *
 * Modified Kerr-Schild coordinates use:
 *   X^0 = t
 *   X^1 = log(r/R0)  (logarithmic radial)
 *   X^2 = theta/pi   (normalized polar)
 *   X^3 = phi/(2*pi) (normalized azimuthal)
 *
 * References:
 *   - McKinney & Gammie (2004) for MKS coordinate systems
 *   - Gammie, McKinney, Toth (2003) HARM formalism
 *
 * Cleanroom implementation based on standard GR coordinate theory.
 */

#ifndef PHYSICS_COORDINATES_H
#define PHYSICS_COORDINATES_H

#include "constants.h"
#include <algorithm>
#include <array>
#include <cmath>

namespace physics {

// ============================================================================
// Coordinate Parameters
// ============================================================================

/**
 * @brief Parameters for Modified Kerr-Schild (MKS) coordinate system.
 *
 * The MKS system uses:
 *   r = R0 * exp(X1)           -- logarithmic radial coordinate
 *   theta = pi * X2 + ...      -- modified polar with optional derefining
 *
 * Derefining (hslope != 0) concentrates resolution near the equator.
 */
struct MKSParams {
  double R0 = 1.0;      // Radial scale factor
  double hslope = 0.0;  // Theta derefining parameter (0 = uniform)
  double poly_xt = 0.0; // Polynomial derefine exponent
  double mks_smooth = 0.0; // Smoothing parameter for inner boundary
};

// ============================================================================
// Boyer-Lindquist Coordinates
// ============================================================================

/**
 * @brief Boyer-Lindquist coordinates (r, theta, phi).
 */
struct BLCoord {
  double r;      // Radial coordinate
  double theta;  // Polar angle [0, pi]
  double phi;    // Azimuthal angle [0, 2*pi]
};

/**
 * @brief Convert MKS code coordinates to Boyer-Lindquist.
 *
 * Standard MKS mapping:
 *   r = R0 * exp(X1)
 *   theta = pi * X2 (no derefining)
 *   phi = X3
 *
 * @param X1 Code radial coordinate
 * @param X2 Code polar coordinate [0, 1]
 * @param X3 Code azimuthal coordinate
 * @param params MKS coordinate parameters
 * @return Boyer-Lindquist coordinates
 */
inline BLCoord bl_coord(double X1, double X2, double X3,
                        const MKSParams &params = MKSParams{}) {
  BLCoord bl;

  // Radial: logarithmic mapping
  bl.r = params.R0 * std::exp(X1);

  // Polar: with optional derefining
  // theta = pi * X2 + (1 - hslope) * sin(2*pi*X2) / 2
  // hslope=0: Maximum derefining (concentrate at equator)
  // hslope=1: No derefining (uniform/linear mapping)
  if (std::abs(params.hslope - 1.0) < 1e-10) {
    // No derefining: simple linear mapping (hslope=1)
    bl.theta = PI * X2;
  } else {
    // Derefining: concentrate resolution near equator
    // This stretches the grid near the poles
    bl.theta = PI * X2 + (1.0 - params.hslope) * std::sin(2.0 * PI * X2) / 2.0;
  }

  // Clamp theta to valid range
  bl.theta = std::clamp(bl.theta, 1e-10, PI - 1e-10);

  // Azimuthal: direct mapping
  bl.phi = X3;

  return bl;
}

/**
 * @brief Compute r from MKS X1 coordinate.
 *
 * r = R0 * exp(X1)
 *
 * @param X1 Code radial coordinate
 * @param R0 Radial scale factor (default 1.0)
 * @return Boyer-Lindquist radial coordinate
 */
inline double r_of_X(double X1, double R0 = 1.0) {
  return R0 * std::exp(X1);
}

/**
 * @brief Compute theta from MKS X2 coordinate.
 *
 * With derefining parameter hslope:
 *   theta = pi * X2 + (1 - hslope) * sin(2*pi*X2) / 2
 *
 * When hslope = 0, maximum derefining (concentrate resolution at equator).
 * When hslope = 1, no derefining (uniform/linear spacing).
 *
 * @param X2 Code polar coordinate [0, 1]
 * @param hslope Derefining parameter (0 = max derefining, 1 = uniform)
 * @return Boyer-Lindquist polar angle
 */
inline double th_of_X(double X2, double hslope = 0.0) {
  double theta;

  if (std::abs(hslope - 1.0) < 1e-10) {
    // No derefining: simple linear mapping (hslope=1)
    theta = PI * X2;
  } else {
    // Derefining active
    theta = PI * X2 + (1.0 - hslope) * std::sin(2.0 * PI * X2) / 2.0;
  }

  // Clamp to avoid coordinate singularities at poles
  return std::clamp(theta, 1e-10, PI - 1e-10);
}

/**
 * @brief Compute X1 from Boyer-Lindquist r coordinate.
 *
 * Inverse of r_of_X: X1 = log(r / R0)
 *
 * @param r Boyer-Lindquist radial coordinate
 * @param R0 Radial scale factor (default 1.0)
 * @return MKS radial coordinate X1
 */
inline double X_of_r(double r, double R0 = 1.0) {
  return std::log(r / R0);
}

/**
 * @brief Compute derivative dr/dX1.
 *
 * For r = R0 * exp(X1):  dr/dX1 = R0 * exp(X1) = r
 *
 * @param X1 Code radial coordinate
 * @param R0 Radial scale factor
 * @return dr/dX1
 */
inline double dr_dX1(double X1, double R0 = 1.0) {
  return R0 * std::exp(X1);
}

/**
 * @brief Compute derivative dtheta/dX2.
 *
 * For theta = pi * X2 + (1 - hslope) * sin(2*pi*X2) / 2:
 *   dtheta/dX2 = pi + (1 - hslope) * pi * cos(2*pi*X2)
 *              = pi * (1 + (1 - hslope) * cos(2*pi*X2))
 *
 * When hslope=1, dtheta/dX2 = pi (constant, no derefining).
 * When hslope=0, dtheta/dX2 varies with X2 (maximum derefining).
 *
 * @param X2 Code polar coordinate
 * @param hslope Derefining parameter (0 = max derefining, 1 = uniform)
 * @return dtheta/dX2
 */
inline double dth_dX2(double X2, double hslope = 0.0) {
  if (std::abs(hslope - 1.0) < 1e-10) {
    // No derefining: constant derivative
    return PI;
  }
  return PI * (1.0 + (1.0 - hslope) * std::cos(2.0 * PI * X2));
}

// ============================================================================
// Cartesian <-> Spherical Conversions
// ============================================================================

/**
 * @brief Convert spherical (r, theta, phi) to Cartesian (x, y, z).
 *
 * Standard transformation:
 *   x = r * sin(theta) * cos(phi)
 *   y = r * sin(theta) * sin(phi)
 *   z = r * cos(theta)
 *
 * @param r Radial coordinate
 * @param theta Polar angle [0, pi]
 * @param phi Azimuthal angle [0, 2*pi]
 * @return Cartesian coordinates {x, y, z}
 */
inline std::array<double, 3> spherical_to_cartesian(double r, double theta, double phi) {
  double sin_theta = std::sin(theta);
  double cos_theta = std::cos(theta);
  double sin_phi = std::sin(phi);
  double cos_phi = std::cos(phi);

  return {
    r * sin_theta * cos_phi,  // x
    r * sin_theta * sin_phi,  // y
    r * cos_theta             // z
  };
}

/**
 * @brief Convert Cartesian (x, y, z) to spherical (r, theta, phi).
 *
 * Inverse transformation:
 *   r = sqrt(x² + y² + z²)
 *   theta = acos(z / r)
 *   phi = atan2(y, x)
 *
 * @param x X coordinate
 * @param y Y coordinate
 * @param z Z coordinate
 * @return BLCoord with spherical coordinates
 */
inline BLCoord cartesian_to_spherical(double x, double y, double z) {
  BLCoord bl;

  bl.r = std::sqrt(x * x + y * y + z * z);

  if (bl.r < 1e-30) {
    bl.theta = 0.0;
    bl.phi = 0.0;
    return bl;
  }

  bl.theta = std::acos(std::clamp(z / bl.r, -1.0, 1.0));
  bl.phi = std::atan2(y, x);

  // Normalize phi to [0, 2*pi]
  if (bl.phi < 0) {
    bl.phi += 2.0 * PI;
  }

  return bl;
}

// ============================================================================
// Kerr-Schild Coordinates
// ============================================================================
//
// Kerr-Schild (KS) coordinates are horizon-penetrating: the metric is
// regular at both horizons, unlike Boyer-Lindquist which has coordinate
// singularities at r = r_+/-.
//
// The KS metric is:
//   g_mu_nu = eta_mu_nu + f * l_mu * l_nu
//
// where f = 2Mr / Sigma, and l^mu is a null vector.
//
// CRITICAL: For backward ray tracing (rays from camera into the scene),
// the OUTGOING null vector must be used (arXiv:2310.02321):
//   l^mu_out = (1, +sqrt(Delta/Sigma), 0, a/Sigma)
//
// Using the ingoing null vector gives wrong caustic structure for
// observer-to-source ray tracing.
//
// References:
//   - arXiv:2310.02321 (Coordinate choice for backward ray tracing)
//   - Kerr (1963), Visser (2007) "The Kerr spacetime" Ch. 1
//   - MTW Ch. 33
// ============================================================================

/**
 * @brief Kerr-Schild coordinate state.
 *
 * KS coordinates share (r, theta) with BL but differ in (t, phi).
 * The radial coordinate r is defined implicitly via:
 *   x^2 + y^2 = (r^2 + a^2) sin^2(theta)
 *   z = r cos(theta)
 */
struct KSCoord {
  double t;      // KS time
  double r;      // Radial (same as BL r)
  double theta;  // Polar (same as BL theta)
  double phi;    // KS azimuthal (differs from BL phi)
};

/**
 * @brief Outgoing principal null vector l^mu in outgoing KS coordinates.
 *
 * In outgoing Kerr-Schild coordinates, the outgoing principal null
 * vector of the Kerr spacetime takes the simple form:
 *   l^mu = (1, 1, 0, 0)
 *
 * This is a geodesic, shear-free, null vector that generates the
 * KS foliation. It is null with respect to both the flat background
 * eta_mu_nu (in Cartesian form) and the full metric g_mu_nu.
 *
 * Proof: g_tt + 2*g_tr + g_rr = 0 (verified algebraically using
 * the BL transformation; the numerator reduces to -Delta*Sigma^2
 * which cancels exactly with Sigma/Delta from g_rr^BL).
 */
inline std::array<double, 4> ks_outgoing_null_vector(
    [[maybe_unused]] double r, [[maybe_unused]] double theta,
    [[maybe_unused]] double a, [[maybe_unused]] double r_s) {
  return {1.0, 1.0, 0.0, 0.0};
}

/**
 * @brief Kerr-Schild scalar function f = 2Mr/Sigma.
 *
 * The KS metric is g = eta + f * l (x) l.
 *
 * @param r Radial coordinate [geometric units]
 * @param theta Polar angle [rad]
 * @param M Geometric mass = GM_phys/c^2 [geometric units]
 * @param a Spin parameter [geometric units]
 * @return f (dimensionless)
 */
inline double ks_f(double r, double theta, double M, double a) {
  double sigma = r * r + a * a * std::cos(theta) * std::cos(theta);
  if (sigma < 1e-30) return 0.0;
  return 2.0 * M * r / sigma;
}

/**
 * @brief Outgoing KS metric tensor components g_mu_nu.
 *
 * Derived from the BL metric via the outgoing coordinate transformation:
 *   dt_BL = dt_KS + (2Mr/Delta) dr
 *   dphi_BL = dphi_KS + (a/Delta) dr
 *   r, theta unchanged
 *
 * This yields a metric regular at the outer horizon (Delta=0).
 *
 * Returns the 10 independent components as a flat array:
 * [g_tt, g_tr, g_t_theta, g_t_phi, g_rr, g_r_theta, g_r_phi,
 *  g_theta_theta, g_theta_phi, g_phi_phi]
 *
 * @param r Radial coordinate [geometric units]
 * @param theta Polar angle [rad]
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return 10 independent metric components (lower indices)
 */
inline std::array<double, 10> ks_outgoing_metric(
    double r, double theta, double M, double a) {
  double cos_th = std::cos(theta);
  double sin_th = std::sin(theta);
  double sin2 = sin_th * sin_th;
  double sigma = r * r + a * a * cos_th * cos_th;
  double delta = r * r - 2.0 * M * r + a * a;
  double r_s = 2.0 * M;

  // BL metric components
  double bl_tt = -(1.0 - r_s * r / sigma);
  double bl_tph = -r_s * r * a * sin2 / sigma;
  double bl_rr = sigma / delta;
  double bl_thth = sigma;
  double bl_phph = (r * r + a * a + r_s * r * a * a * sin2 / sigma) * sin2;

  // Transformation: alpha = 2Mr/Delta, beta = a/Delta
  double alpha = r_s * r / delta;
  double beta = a / delta;

  // KS metric via substitution dt_BL = dt + alpha*dr, dphi_BL = dphi + beta*dr
  double g_tt = bl_tt;
  double g_tr = bl_tt * alpha + bl_tph * beta;
  double g_tth = 0.0;
  double g_tph = bl_tph;
  double g_rr = bl_tt * alpha * alpha + 2.0 * bl_tph * alpha * beta
              + bl_rr + bl_phph * beta * beta;
  double g_rth = 0.0;
  double g_rph = bl_tph * alpha + bl_phph * beta;
  double g_thth = bl_thth;
  double g_thph = 0.0;
  double g_phph = bl_phph;

  return {g_tt, g_tr, g_tth, g_tph, g_rr, g_rth, g_rph,
          g_thth, g_thph, g_phph};
}

/**
 * @brief Ingoing principal null vector n^mu in outgoing KS coordinates.
 *
 * Solves g_mu_nu n^mu n^nu = 0 for radial ingoing rays (n^theta=0, n^phi=0)
 * with n^r = -1. The quadratic g_tt (n^t)^2 - 2 g_tr n^t + g_rr = 0
 * gives n^t = (g_tr +/- sqrt(g_tr^2 - g_tt*g_rr)) / g_tt.
 * We choose the branch with larger |n^t| (the one representing ingoing rays).
 */
inline std::array<double, 4> ks_ingoing_null_vector(
    double r, double theta, double a, double r_s) {
  auto g = ks_outgoing_metric(r, theta, r_s / 2.0, a);
  double gtt = g[0], gtr = g[1], grr = g[4];

  if (std::abs(gtt) < 1e-30) {
    return {1.0, -1.0, 0.0, 0.0};
  }

  double disc = gtr * gtr - gtt * grr;
  double sqrt_disc = (disc > 0.0) ? std::sqrt(disc) : 0.0;

  // Choose the ingoing branch
  double nt = (gtr + sqrt_disc) / gtt;

  return {nt, -1.0, 0.0, 0.0};
}

/**
 * @brief BL to outgoing KS time transformation (differential).
 *
 * dt_KS = dt_BL + (2Mr / Delta) dr
 *
 * For outgoing KS, the sign in front of dr is positive.
 *
 * @param r Current radial position [geometric units]
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return dt_KS/dr correction factor
 */
inline double bl_to_ks_dt_dr(double r, double M, double a) {
  double delta = r * r - 2.0 * M * r + a * a;
  if (std::abs(delta) < 1e-30) return 0.0; // At horizon
  return 2.0 * M * r / delta;
}

/**
 * @brief BL to outgoing KS azimuthal transformation (differential).
 *
 * dphi_KS = dphi_BL + (a / Delta) dr
 *
 * @param r Current radial position [geometric units]
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return dphi_KS/dr correction factor
 */
inline double bl_to_ks_dphi_dr(double r, double M, double a) {
  double delta = r * r - 2.0 * M * r + a * a;
  if (std::abs(delta) < 1e-30) return 0.0;
  return a / delta;
}

/**
 * @brief Convert BL 4-velocity to outgoing KS 4-velocity.
 *
 * Transforms u^mu from Boyer-Lindquist to outgoing Kerr-Schild:
 *   u^t_KS = u^t_BL + (2Mr/Delta) u^r_BL
 *   u^r_KS = u^r_BL
 *   u^theta_KS = u^theta_BL
 *   u^phi_KS = u^phi_BL + (a/Delta) u^r_BL
 *
 * @param u_bl BL 4-velocity {u^t, u^r, u^theta, u^phi}
 * @param r Radial coordinate [geometric units]
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return KS 4-velocity {u^t, u^r, u^theta, u^phi}
 */
inline std::array<double, 4> bl_to_ks_velocity(
    const std::array<double, 4>& u_bl,
    double r, double M, double a) {
  double delta = r * r - 2.0 * M * r + a * a;
  double correction = (std::abs(delta) > 1e-30) ? 1.0 / delta : 0.0;

  return {
    u_bl[0] + 2.0 * M * r * correction * u_bl[1],  // u^t_KS
    u_bl[1],                                          // u^r_KS (unchanged)
    u_bl[2],                                          // u^theta_KS (unchanged)
    u_bl[3] + a * correction * u_bl[1]               // u^phi_KS
  };
}

/**
 * @brief Convert outgoing KS 4-velocity to BL 4-velocity.
 *
 * Inverse of bl_to_ks_velocity:
 *   u^t_BL = u^t_KS - (2Mr/Delta) u^r_KS
 *   u^r_BL = u^r_KS
 *   u^theta_BL = u^theta_KS
 *   u^phi_BL = u^phi_KS - (a/Delta) u^r_KS
 */
inline std::array<double, 4> ks_to_bl_velocity(
    const std::array<double, 4>& u_ks,
    double r, double M, double a) {
  double delta = r * r - 2.0 * M * r + a * a;
  double correction = (std::abs(delta) > 1e-30) ? 1.0 / delta : 0.0;

  return {
    u_ks[0] - 2.0 * M * r * correction * u_ks[1],
    u_ks[1],
    u_ks[2],
    u_ks[3] - a * correction * u_ks[1]
  };
}

/**
 * @brief Check if outgoing KS metric is regular at given radius.
 *
 * Unlike BL coordinates, KS should be regular everywhere outside the
 * ring singularity (r=0, theta=pi/2). Returns true if all metric
 * components are finite.
 */
inline bool ks_metric_is_regular(double r, double theta, double M, double a) {
  auto g = ks_outgoing_metric(r, theta, M, a);
  for (double val : g) {
    // Use builtin to work with -ffast-math (which assumes no inf/nan)
    if (val != val || val > 1e30 || val < -1e30) return false;
  }
  return true;
}

/**
 * @brief Convert Kerr-Schild (KS) phi to Boyer-Lindquist phi.
 *
 * The exact transformation requires integrating a/Delta along the geodesic.
 * For a single snapshot at radius r:
 *   phi_BL = phi_KS - a * ln|r - r_+| / (r_+ - r_-) + a * ln|r - r_-| / (r_+ - r_-)
 *
 * This function computes the instantaneous (non-integrated) correction.
 *
 * @param r Radial coordinate [geometric units]
 * @param phi_ks KS azimuthal angle
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return BL phi coordinate (approximate for finite-r observers)
 */
inline double ks_to_bl_phi(double r, double phi_ks, double M, double a) {
  if (std::abs(a) < 1e-15) return phi_ks; // Schwarzschild: no correction

  double disc = M * M - a * a;
  if (disc <= 0.0) return phi_ks; // Extremal or super-extremal

  double sqrt_disc = std::sqrt(disc);
  double r_plus = M + sqrt_disc;
  double r_minus = M - sqrt_disc;
  double dr = r_plus - r_minus;

  if (std::abs(dr) < 1e-15) return phi_ks;

  // Integrated correction from infinity to r
  // phi_BL = phi_KS - (a / (r_+ - r_-)) * ln|(r - r_+) / (r - r_-)|
  double arg_plus = std::abs(r - r_plus);
  double arg_minus = std::abs(r - r_minus);

  if (arg_plus < 1e-15 || arg_minus < 1e-15) return phi_ks;

  return phi_ks - (a / dr) * std::log(arg_plus / arg_minus);
}

} // namespace physics

#endif // PHYSICS_COORDINATES_H
