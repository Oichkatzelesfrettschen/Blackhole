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

namespace physics {

// ============================================================================
// Light Deflection
// ============================================================================

/**
 * @brief Compute gravitational light deflection angle (weak field).
 *
 * delta_phi = 4GM/(bc^2)
 *
 * This is the first-order approximation valid for b >> r_s.
 *
 * @param impactParam Impact parameter b [cm]
 * @param mass Central mass [g]
 * @return Deflection angle [radians]
 */
[[nodiscard]] double gravitationalDeflection(double impactParam, double mass);

/**
 * @brief Compute critical impact parameter for photon capture.
 *
 * b_crit = (3*sqrt(3)/2) r_s ~ 2.598 r_s
 *
 * Photons with b < b_crit are captured by the black hole.
 *
 * @param mass Black hole mass [g]
 * @return Critical impact parameter [cm]
 */
[[nodiscard]] double criticalImpactParameter(double mass);

/**
 * @brief Check if a photon with given impact parameter will be captured.
 *
 * @param impactParam Impact parameter b [cm]
 * @param mass Black hole mass [g]
 * @return true if photon will be captured (b < b_crit)
 */
[[nodiscard]] bool isPhotonCaptured(double impactParam, double mass);

// ============================================================================
// Time Effects
// ============================================================================

/**
 * @brief Compute Shapiro time delay for light passing near mass.
 *
 * delta_t = (2GM/c^3) * ln((r1 + r2 + d)/(r1 + r2 - d))
 *
 * where d = sqrt((r1 + r2)^2 - b^2)
 *
 * @param r1 Distance from mass to source [cm]
 * @param r2 Distance from mass to observer [cm]
 * @param impactParam Impact parameter [cm]
 * @param mass Central mass [g]
 * @return Time delay [s]
 */
[[nodiscard]] double shapiroDelay(double r1, double r2, double impactParam, double mass);

/**
 * @brief Compute gravitational time dilation factor.
 *
 * dtau/dt = sqrt(1 - r_s/r)
 *
 * This is the ratio of proper time to coordinate time.
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Time dilation factor (0 at horizon, 1 at infinity)
 */
[[nodiscard]] double timeDilationFactor(double r, double mass);

// ============================================================================
// Ray Tracing Helpers (for GPU integration)
// ============================================================================

/**
 * @brief Compute effective potential for null geodesics.
 *
 * V_eff(r) = (1 - rS/r) / r^2
 *
 * @param r Radial coordinate [cm]
 * @param rS Schwarzschild radius [cm]
 * @return Effective potential
 */
[[nodiscard]] double nullEffectivePotential(double r, double rS);

/**
 * @brief Compute (dr/dphi)^2 for null geodesics.
 *
 * (dr/dphi)^2 = r^4/b^2 - r^2*(1 - rS/r)
 *
 * @param r Current radius [cm]
 * @param rS Schwarzschild radius [cm]
 * @param b Impact parameter [cm]
 * @return (dr/dphi)^2 value
 */
[[nodiscard]] double nullRadialDerivativeSquared(double r, double rS, double b);

/**
 * @brief Compute turning point radius for photon trajectory.
 *
 * At the turning point, dr/dphi = 0.
 *
 * @param impactParam Impact parameter [cm]
 * @param mass Black hole mass [g]
 * @return Turning point radius [cm], or NaN if captured
 */
[[nodiscard]] double photonTurningPoint(double impactParam, double mass);

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
void schwarzschildToCartesian(double r, double theta, double phi, double &x,
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
void cartesianToSchwarzschild(double x, double y, double z, double &r,
                              double &theta, double &phi);

} // namespace physics

#endif // PHYSICS_GEODESICS_H
