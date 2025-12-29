/**
 * @file geodesics.h
 * @brief Geodesic calculations for light and particle trajectories.
 *
 * Provides functions for computing light bending, time delays, and
 * trajectory integration in Schwarzschild spacetime.
 *
 * Cleanroom implementation based on standard GR textbook formulas.
 */

#ifndef PHYSICS_GEODESICS_H
#define PHYSICS_GEODESICS_H

#include <cmath>

namespace physics {

// ============================================================================
// Light Deflection
// ============================================================================

/**
 * @brief Compute gravitational light deflection angle (weak field).
 *
 * δφ = 4GM/(bc²)
 *
 * This is the first-order approximation valid for b >> r_s.
 *
 * @param impact_param Impact parameter b [cm]
 * @param mass Central mass [g]
 * @return Deflection angle [radians]
 */
double gravitational_deflection(double impact_param, double mass);

/**
 * @brief Compute critical impact parameter for photon capture.
 *
 * b_crit = (3√3/2) r_s ≈ 2.598 r_s
 *
 * Photons with b < b_crit are captured by the black hole.
 *
 * @param mass Black hole mass [g]
 * @return Critical impact parameter [cm]
 */
double critical_impact_parameter(double mass);

/**
 * @brief Check if a photon with given impact parameter will be captured.
 *
 * @param impact_param Impact parameter b [cm]
 * @param mass Black hole mass [g]
 * @return true if photon will be captured (b < b_crit)
 */
bool is_photon_captured(double impact_param, double mass);

// ============================================================================
// Time Effects
// ============================================================================

/**
 * @brief Compute Shapiro time delay for light passing near mass.
 *
 * Δt = (2GM/c³) ln((r₁ + r₂ + d)/(r₁ + r₂ - d))
 *
 * where d = √((r₁ + r₂)² - b²)
 *
 * @param r1 Distance from mass to source [cm]
 * @param r2 Distance from mass to observer [cm]
 * @param impact_param Impact parameter [cm]
 * @param mass Central mass [g]
 * @return Time delay [s]
 */
double shapiro_delay(double r1, double r2, double impact_param, double mass);

/**
 * @brief Compute gravitational time dilation factor.
 *
 * dτ/dt = √(1 - r_s/r)
 *
 * This is the ratio of proper time to coordinate time.
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Time dilation factor (0 at horizon, 1 at infinity)
 */
double time_dilation_factor(double r, double mass);

// ============================================================================
// Ray Tracing Helpers (for GPU integration)
// ============================================================================

/**
 * @brief Compute effective potential for null geodesics.
 *
 * V_eff(r) = (1 - r_s/r) / r²
 *
 * @param r Radial coordinate [cm]
 * @param r_s Schwarzschild radius [cm]
 * @return Effective potential
 */
double null_effective_potential(double r, double r_s);

/**
 * @brief Compute dr/dφ for null geodesics.
 *
 * (dr/dφ)² = r⁴/b² - r²(1 - r_s/r)
 *
 * @param r Current radius [cm]
 * @param r_s Schwarzschild radius [cm]
 * @param b Impact parameter [cm]
 * @return (dr/dφ)² value
 */
double null_radial_derivative_squared(double r, double r_s, double b);

/**
 * @brief Compute turning point radius for photon trajectory.
 *
 * At the turning point, dr/dφ = 0.
 *
 * @param impact_param Impact parameter [cm]
 * @param mass Black hole mass [g]
 * @return Turning point radius [cm], or NaN if captured
 */
double photon_turning_point(double impact_param, double mass);

// ============================================================================
// Coordinate Transformations
// ============================================================================

/**
 * @brief Convert Schwarzschild to Cartesian coordinates.
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param phi Azimuthal angle [rad]
 * @param[out] x X coordinate [cm]
 * @param[out] y Y coordinate [cm]
 * @param[out] z Z coordinate [cm]
 */
void schwarzschild_to_cartesian(double r, double theta, double phi, double &x,
                                double &y, double &z);

/**
 * @brief Convert Cartesian to Schwarzschild coordinates.
 *
 * @param x X coordinate [cm]
 * @param y Y coordinate [cm]
 * @param z Z coordinate [cm]
 * @param[out] r Radial coordinate [cm]
 * @param[out] theta Polar angle [rad]
 * @param[out] phi Azimuthal angle [rad]
 */
void cartesian_to_schwarzschild(double x, double y, double z, double &r,
                                double &theta, double &phi);

} // namespace physics

#endif // PHYSICS_GEODESICS_H
