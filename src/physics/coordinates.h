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
 *   r = r0 * exp(X1)           -- logarithmic radial coordinate
 *   theta = pi * X2 + ...      -- modified polar with optional derefining
 *
 * Derefining (hslope != 0) concentrates resolution near the equator.
 */
struct MKSParams {
  double r0 = 1.0;         // Radial scale factor
  double hslope = 0.0;     // Theta derefining parameter (0 = uniform)
  double polyXt = 0.0;     // Polynomial derefine exponent
  double mksSmooth = 0.0;  // Smoothing parameter for inner boundary
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
 *   r = r0 * exp(x1)
 *   theta = pi * x2 (no derefining)
 *   phi = x3
 *
 * @param x1 Code radial coordinate
 * @param x2 Code polar coordinate [0, 1]
 * @param x3 Code azimuthal coordinate
 * @param params MKS coordinate parameters
 * @return Boyer-Lindquist coordinates
 */
[[nodiscard]] inline BLCoord blCoord(double x1, double x2, double x3,
                                     const MKSParams& params = MKSParams{}) {
  BLCoord bl{};

  // Radial: logarithmic mapping
  bl.r = params.r0 * std::exp(x1);

  // Polar: with optional derefining
  // theta = pi * x2 + (1 - hslope) * sin(2*pi*x2) / 2
  // hslope=0: Maximum derefining (concentrate at equator)
  // hslope=1: No derefining (uniform/linear mapping)
  if (std::abs(params.hslope - 1.0) < 1e-10) {
    // No derefining: simple linear mapping (hslope=1)
    bl.theta = PI * x2;
  } else {
    // Derefining: concentrate resolution near equator
    // This stretches the grid near the poles
    bl.theta = (PI * x2) + ((1.0 - params.hslope) * std::sin(2.0 * PI * x2) / 2.0);
  }

  // Clamp theta to valid range
  bl.theta = std::clamp(bl.theta, 1e-10, PI - 1e-10);

  // Azimuthal: direct mapping
  bl.phi = x3;

  return bl;
}

/**
 * @brief Compute r from MKS x1 coordinate.
 *
 * r = r0 * exp(x1)
 *
 * @param x1 Code radial coordinate
 * @param r0 Radial scale factor (default 1.0)
 * @return Boyer-Lindquist radial coordinate
 */
[[nodiscard]] inline double rOfX(double x1, double r0 = 1.0) {
  return r0 * std::exp(x1);
}

/**
 * @brief Compute theta from MKS x2 coordinate.
 *
 * With derefining parameter hslope:
 *   theta = pi * x2 + (1 - hslope) * sin(2*pi*x2) / 2
 *
 * When hslope = 0, maximum derefining (concentrate resolution at equator).
 * When hslope = 1, no derefining (uniform/linear spacing).
 *
 * @param x2 Code polar coordinate [0, 1]
 * @param hslope Derefining parameter (0 = max derefining, 1 = uniform)
 * @return Boyer-Lindquist polar angle
 */
[[nodiscard]] inline double thOfX(double x2, double hslope = 0.0) {
  double theta{};

  if (std::abs(hslope - 1.0) < 1e-10) {
    // No derefining: simple linear mapping (hslope=1)
    theta = PI * x2;
  } else {
    // Derefining active
    theta = (PI * x2) + ((1.0 - hslope) * std::sin(2.0 * PI * x2) / 2.0);
  }

  // Clamp to avoid coordinate singularities at poles
  return std::clamp(theta, 1e-10, PI - 1e-10);
}

/**
 * @brief Compute x1 from Boyer-Lindquist r coordinate.
 *
 * Inverse of rOfX: x1 = log(r / r0)
 *
 * @param r Boyer-Lindquist radial coordinate
 * @param r0 Radial scale factor (default 1.0)
 * @return MKS radial coordinate x1
 */
[[nodiscard]] inline double xOfR(double r, double r0 = 1.0) {
  return std::log(r / r0);
}

/**
 * @brief Compute derivative dr/dx1.
 *
 * For r = r0 * exp(x1):  dr/dx1 = r0 * exp(x1) = r
 *
 * @param x1 Code radial coordinate
 * @param r0 Radial scale factor
 * @return dr/dx1
 */
[[nodiscard]] inline double drDX1(double x1, double r0 = 1.0) {
  return r0 * std::exp(x1);
}

/**
 * @brief Compute derivative dtheta/dx2.
 *
 * For theta = pi * x2 + (1 - hslope) * sin(2*pi*x2) / 2:
 *   dtheta/dx2 = pi + (1 - hslope) * pi * cos(2*pi*x2)
 *              = pi * (1 + (1 - hslope) * cos(2*pi*x2))
 *
 * When hslope=1, dtheta/dx2 = pi (constant, no derefining).
 * When hslope=0, dtheta/dx2 varies with x2 (maximum derefining).
 *
 * @param x2 Code polar coordinate
 * @param hslope Derefining parameter (0 = max derefining, 1 = uniform)
 * @return dtheta/dx2
 */
[[nodiscard]] inline double dthDX2(double x2, double hslope = 0.0) {
  if (std::abs(hslope - 1.0) < 1e-10) {
    // No derefining: constant derivative
    return PI;
  }
  return PI * (1.0 + ((1.0 - hslope) * std::cos(2.0 * PI * x2)));
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
[[nodiscard]] inline std::array<double, 3> sphericalToCartesian(
    double r, double theta, double phi) {
  const double sinTheta = std::sin(theta);
  const double cosTheta = std::cos(theta);
  const double sinPhi = std::sin(phi);
  const double cosPhi = std::cos(phi);

  return {
    r * sinTheta * cosPhi,  // x
    r * sinTheta * sinPhi,  // y
    r * cosTheta            // z
  };
}

/**
 * @brief Convert Cartesian (x, y, z) to spherical (r, theta, phi).
 *
 * Inverse transformation:
 *   r = sqrt(x^2 + y^2 + z^2)
 *   theta = acos(z / r)
 *   phi = atan2(y, x)
 *
 * @param x X coordinate
 * @param y Y coordinate
 * @param z Z coordinate
 * @return BLCoord with spherical coordinates
 */
[[nodiscard]] inline BLCoord cartesianToSpherical(double x, double y, double z) {
  BLCoord bl{};

  bl.r = std::sqrt((x * x) + (y * y) + (z * z));

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
[[nodiscard]] inline std::array<double, 4> ksOutgoingNullVector(
    [[maybe_unused]] double r, [[maybe_unused]] double theta,
    [[maybe_unused]] double a, [[maybe_unused]] double rS) {
  return {1.0, 1.0, 0.0, 0.0};
}

/**
 * @brief Kerr-Schild scalar function f = 2Mr/Sigma.
 *
 * The KS metric is g = eta + f * l (x) l.
 *
 * @param r Radial coordinate [geometric units]
 * @param theta Polar angle [rad]
 * @param mGeom Geometric mass = GM_phys/c^2 [geometric units]
 * @param a Spin parameter [geometric units]
 * @return f (dimensionless)
 */
[[nodiscard]] inline double ksF(double r, double theta, double mGeom, double a) {
  const double sigma = (r * r) + (a * a * std::cos(theta) * std::cos(theta));
  if (sigma < 1e-30) { return 0.0; }
  return (2.0 * mGeom * r) / sigma;
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
 * @param mGeom Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return 10 independent metric components (lower indices)
 */
[[nodiscard]] inline std::array<double, 10> ksOutgoingMetric(
    double r, double theta, double mGeom, double a) {
  const double cosTh = std::cos(theta);
  const double sinTh = std::sin(theta);
  const double sin2 = sinTh * sinTh;
  const double sigma = (r * r) + (a * a * cosTh * cosTh);
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  const double rS = 2.0 * mGeom;

  // BL metric components
  const double blTt = -(1.0 - ((rS * r) / sigma));
  const double blTph = -(rS * r * a * sin2) / sigma;
  const double blRr = sigma / delta;
  const double blThth = sigma;
  const double blPhph = ((r * r) + (a * a) + (rS * r * a * a * sin2 / sigma)) * sin2;

  // Transformation: alpha = 2Mr/Delta, beta = a/Delta
  const double alpha = (rS * r) / delta;
  const double beta = a / delta;

  // KS metric via substitution dt_BL = dt + alpha*dr, dphi_BL = dphi + beta*dr
  const double gTt = blTt;
  const double gTr = (blTt * alpha) + (blTph * beta);
  const double gTth = 0.0;
  const double gTph = blTph;
  const double gRr = (blTt * alpha * alpha) + (2.0 * blTph * alpha * beta)
                   + blRr + (blPhph * beta * beta);
  const double gRth = 0.0;
  const double gRph = (blTph * alpha) + (blPhph * beta);
  const double gThth = blThth;
  const double gThph = 0.0;
  const double gPhph = blPhph;

  return {gTt, gTr, gTth, gTph, gRr, gRth, gRph, gThth, gThph, gPhph};
}

/**
 * @brief Ingoing principal null vector n^mu in outgoing KS coordinates.
 *
 * Solves g_mu_nu n^mu n^nu = 0 for radial ingoing rays (n^theta=0, n^phi=0)
 * with n^r = -1. The quadratic g_tt (n^t)^2 - 2 g_tr n^t + g_rr = 0
 * gives n^t = (g_tr +/- sqrt(g_tr^2 - g_tt*g_rr)) / g_tt.
 * We choose the branch with larger |n^t| (the one representing ingoing rays).
 */
[[nodiscard]] inline std::array<double, 4> ksIngoingNullVector(
    double r, double theta, double a, double rS) {
  const auto g = ksOutgoingMetric(r, theta, rS / 2.0, a);
  const double gtt = std::get<0>(g);
  const double gtr = std::get<1>(g);
  const double grr = std::get<4>(g);

  if (std::abs(gtt) < 1e-30) {
    return {1.0, -1.0, 0.0, 0.0};
  }

  const double disc = (gtr * gtr) - (gtt * grr);
  const double sqrtDisc = (disc > 0.0) ? std::sqrt(disc) : 0.0;

  // Choose the ingoing branch
  const double nt = (gtr + sqrtDisc) / gtt;

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
 * @param mGeom Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return dt_KS/dr correction factor
 */
[[nodiscard]] inline double blToKsDtDr(double r, double mGeom, double a) {
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  if (std::abs(delta) < 1e-30) { return 0.0; }  // At horizon
  return (2.0 * mGeom * r) / delta;
}

/**
 * @brief BL to outgoing KS azimuthal transformation (differential).
 *
 * dphi_KS = dphi_BL + (a / Delta) dr
 *
 * @param r Current radial position [geometric units]
 * @param mGeom Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return dphi_KS/dr correction factor
 */
[[nodiscard]] inline double blToKsDphiDr(double r, double mGeom, double a) {
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  if (std::abs(delta) < 1e-30) { return 0.0; }
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
 * @param uBl BL 4-velocity {u^t, u^r, u^theta, u^phi}
 * @param r Radial coordinate [geometric units]
 * @param mGeom Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return KS 4-velocity {u^t, u^r, u^theta, u^phi}
 */
[[nodiscard]] inline std::array<double, 4> blToKsVelocity(
    const std::array<double, 4>& uBl,
    double r, double mGeom, double a) {
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  const double correction = (std::abs(delta) > 1e-30) ? 1.0 / delta : 0.0;

  return {
    std::get<0>(uBl) + (2.0 * mGeom * r * correction * std::get<1>(uBl)),
    std::get<1>(uBl),
    std::get<2>(uBl),
    std::get<3>(uBl) + (a * correction * std::get<1>(uBl))
  };
}

/**
 * @brief Convert outgoing KS 4-velocity to BL 4-velocity.
 *
 * Inverse of blToKsVelocity:
 *   u^t_BL = u^t_KS - (2Mr/Delta) u^r_KS
 *   u^r_BL = u^r_KS
 *   u^theta_BL = u^theta_KS
 *   u^phi_BL = u^phi_KS - (a/Delta) u^r_KS
 */
[[nodiscard]] inline std::array<double, 4> ksToBlVelocity(
    const std::array<double, 4>& uKs,
    double r, double mGeom, double a) {
  const double delta = (r * r) - (2.0 * mGeom * r) + (a * a);
  const double correction = (std::abs(delta) > 1e-30) ? 1.0 / delta : 0.0;

  return {
    std::get<0>(uKs) - (2.0 * mGeom * r * correction * std::get<1>(uKs)),
    std::get<1>(uKs),
    std::get<2>(uKs),
    std::get<3>(uKs) - (a * correction * std::get<1>(uKs))
  };
}

/**
 * @brief Check if outgoing KS metric is regular at given radius.
 *
 * Unlike BL coordinates, KS should be regular everywhere outside the
 * ring singularity (r=0, theta=pi/2). Returns true if all metric
 * components are finite.
 */
[[nodiscard]] inline bool ksMetricIsRegular(double r, double theta,
                                            double mGeom, double a) {
  const auto g = ksOutgoingMetric(r, theta, mGeom, a);
  // Use builtin comparisons to work with -ffast-math (which assumes no inf/nan)
  return std::ranges::all_of(g, [](const double val) {
    return (val == val) && (val <= 1e30) && (val >= -1e30);
  });
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
 * @param phiKs KS azimuthal angle
 * @param mGeom Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @return BL phi coordinate (approximate for finite-r observers)
 */
[[nodiscard]] inline double ksToBlPhi(double r, double phiKs,
                                      double mGeom, double a) {
  if (std::abs(a) < 1e-15) { return phiKs; }  // Schwarzschild: no correction

  const double disc = (mGeom * mGeom) - (a * a);
  if (disc <= 0.0) { return phiKs; }  // Extremal or super-extremal

  const double sqrtDisc = std::sqrt(disc);
  const double rPlus = mGeom + sqrtDisc;
  const double rMinus = mGeom - sqrtDisc;
  const double dr = rPlus - rMinus;

  if (std::abs(dr) < 1e-15) { return phiKs; }

  // Integrated correction from infinity to r
  // phi_BL = phi_KS - (a / (r_+ - r_-)) * ln|(r - r_+) / (r - r_-)|
  const double argPlus = std::abs(r - rPlus);
  const double argMinus = std::abs(r - rMinus);

  if ((argPlus < 1e-15) || (argMinus < 1e-15)) { return phiKs; }

  return phiKs - ((a / dr) * std::log(argPlus / argMinus));
}

} // namespace physics

#endif // PHYSICS_COORDINATES_H
