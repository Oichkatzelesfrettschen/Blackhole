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
// Kerr-Schild to Boyer-Lindquist
// ============================================================================

/**
 * @brief Convert Kerr-Schild (KS) coordinates to Boyer-Lindquist.
 *
 * The transformation involves:
 *   t_BL = t_KS - integral term
 *   r_BL = r_KS (same)
 *   theta_BL = theta_KS (same)
 *   phi_BL = phi_KS - integral term
 *
 * For ray tracing, we often only need (r, theta, phi) which are unchanged.
 *
 * @param r Radial coordinate (same in both systems)
 * @param theta Polar angle (same in both systems)
 * @param phi_ks Kerr-Schild azimuthal angle
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Boyer-Lindquist phi coordinate
 */
inline double ks_to_bl_phi(double r, double phi_ks, double mass, double a) {
  // For null geodesics at infinity, phi_BL ≈ phi_KS
  // The full transformation requires the geodesic history
  // This is a simplified version for distant observers
  (void)r;
  (void)mass;
  (void)a;
  return phi_ks;
}

} // namespace physics

#endif // PHYSICS_COORDINATES_H
