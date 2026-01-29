/**
 * @file doppler.h
 * @brief Relativistic Doppler effect and beaming calculations.
 *
 * Implements special and general relativistic Doppler effects for:
 * - Moving sources (jets, orbiting matter)
 * - Cosmological redshift
 * - Relativistic beaming/boosting
 * - Aberration
 *
 * Key formulas:
 *   Lorentz factor: γ = 1/√(1 - β²)
 *   Doppler factor: δ = 1/(γ(1 - β cos θ))
 *   Observed flux: F_obs = δ^(3+α) F_emit for power-law spectrum F ∝ ν^α
 *
 * References:
 *   - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics"
 *   - Begelman, Blandford, Rees (1984) Rev. Mod. Phys. 56, 255
 *
 * Cleanroom implementation based on standard SR/GR formulas.
 */

#ifndef PHYSICS_DOPPLER_H
#define PHYSICS_DOPPLER_H

#include "constants.h"
#include "safe_limits.h"
#include <algorithm>
#include <cmath>

namespace physics {

// ============================================================================
// Lorentz Factor
// ============================================================================

/**
 * @brief Compute Lorentz factor γ from velocity.
 *
 * γ = 1/√(1 - v²/c²) = 1/√(1 - β²)
 *
 * @param beta Velocity as fraction of c (v/c), must be in [0, 1)
 * @return Lorentz factor γ ≥ 1
 */
inline double lorentz_factor(double beta) {
  if (beta < 0) beta = -beta;
  if (beta >= 1.0) {
    return safe_infinity<double>();
  }
  return 1.0 / std::sqrt(1.0 - beta * beta);
}

/**
 * @brief Compute velocity β from Lorentz factor.
 *
 * β = √(1 - 1/γ²)
 *
 * @param gamma Lorentz factor γ ≥ 1
 * @return Velocity as fraction of c
 */
inline double beta_from_gamma(double gamma) {
  if (gamma < 1.0) gamma = 1.0;
  return std::sqrt(1.0 - 1.0 / (gamma * gamma));
}

// ============================================================================
// Doppler Factor
// ============================================================================

/**
 * @brief Compute relativistic Doppler factor.
 *
 * δ = 1/(γ(1 - β cos θ))
 *
 * where θ is the angle between velocity and line of sight.
 * θ = 0 means approaching (blueshift), θ = π means receding (redshift).
 *
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @return Doppler factor δ
 */
inline double doppler_factor(double beta, double theta) {
  double gamma = lorentz_factor(beta);
  double cos_theta = std::cos(theta);
  double denominator = gamma * (1.0 - beta * cos_theta);

  if (std::abs(denominator) < 1e-30) {
    return safe_infinity<double>();
  }

  return 1.0 / denominator;
}

/**
 * @brief Compute Doppler factor for head-on approach (θ = 0).
 *
 * δ_max = √((1 + β)/(1 - β)) = γ(1 + β)
 *
 * @param beta Velocity as fraction of c
 * @return Maximum Doppler factor (approaching)
 */
inline double doppler_factor_approaching(double beta) {
  if (beta >= 1.0) {
    return safe_infinity<double>();
  }
  return std::sqrt((1.0 + beta) / (1.0 - beta));
}

/**
 * @brief Compute Doppler factor for direct recession (θ = π).
 *
 * δ_min = √((1 - β)/(1 + β)) = 1/(γ(1 + β))
 *
 * @param beta Velocity as fraction of c
 * @return Minimum Doppler factor (receding)
 */
inline double doppler_factor_receding(double beta) {
  if (beta >= 1.0) {
    return 0.0;
  }
  return std::sqrt((1.0 - beta) / (1.0 + beta));
}

// ============================================================================
// Frequency Shifts
// ============================================================================

/**
 * @brief Compute observed frequency with relativistic Doppler shift.
 *
 * ν_obs = δ × ν_emit
 *
 * @param nu_emit Emitted frequency [Hz]
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @return Observed frequency [Hz]
 */
inline double doppler_shift_relativistic(double nu_emit, double beta, double theta) {
  return doppler_factor(beta, theta) * nu_emit;
}

/**
 * @brief Compute transverse Doppler shift (θ = π/2).
 *
 * ν_obs = ν_emit / γ (always redshift due to time dilation)
 *
 * @param nu_emit Emitted frequency [Hz]
 * @param beta Velocity as fraction of c
 * @return Observed frequency [Hz]
 */
inline double doppler_shift_transverse(double nu_emit, double beta) {
  return nu_emit / lorentz_factor(beta);
}

/**
 * @brief Compute observed frequency from cosmological redshift.
 *
 * ν_obs = ν_emit / (1 + z)
 *
 * @param nu_emit Rest-frame frequency [Hz]
 * @param z Cosmological redshift
 * @return Observed frequency [Hz]
 */
inline double observed_frequency(double nu_emit, double z) {
  return nu_emit / (1.0 + z);
}

/**
 * @brief Compute rest-frame frequency from observed frequency.
 *
 * ν_emit = ν_obs × (1 + z)
 *
 * @param nu_obs Observed frequency [Hz]
 * @param z Cosmological redshift
 * @return Rest-frame frequency [Hz]
 */
inline double rest_frame_frequency(double nu_obs, double z) {
  return nu_obs * (1.0 + z);
}

// ============================================================================
// Relativistic Beaming
// ============================================================================

/**
 * @brief Compute intensity boost from relativistic beaming.
 *
 * For a power-law spectrum F_ν ∝ ν^α:
 *   I_obs = δ^(3+α) × I_emit (optically thin)
 *   I_obs = δ^3 × I_emit (optically thick/blackbody)
 *
 * The δ³ factor comes from:
 *   - δ² from solid angle transformation (aberration)
 *   - δ from time dilation (photon arrival rate)
 *
 * @param I_emit Emitted intensity
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @param alpha Spectral index (F_ν ∝ ν^α), use 0 for blackbody
 * @return Observed intensity
 */
inline double relativistic_beaming_intensity(double I_emit, double beta,
                                              double theta, double alpha) {
  double delta = doppler_factor(beta, theta);
  return I_emit * std::pow(delta, 3.0 + alpha);
}

/**
 * @brief Compute flux density boost from relativistic beaming.
 *
 * F_obs = δ^(3+α) × F_emit for isotropic emitter
 *
 * @param F_emit Emitted flux density
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @param alpha Spectral index
 * @return Observed flux density
 */
inline double relativistic_beaming_flux(double F_emit, double beta,
                                         double theta, double alpha) {
  double delta = doppler_factor(beta, theta);
  return F_emit * std::pow(delta, 3.0 + alpha);
}

/**
 * @brief Compute apparent superluminal velocity.
 *
 * For an object moving at angle θ to line of sight:
 *   β_app = (β sin θ) / (1 - β cos θ)
 *
 * Maximum apparent velocity β_app,max = γβ at θ = arccos(β).
 *
 * @param beta True velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @return Apparent transverse velocity as fraction of c
 */
inline double apparent_superluminal_velocity(double beta, double theta) {
  double sin_theta = std::sin(theta);
  double cos_theta = std::cos(theta);
  double denominator = 1.0 - beta * cos_theta;

  if (std::abs(denominator) < 1e-30) {
    return safe_infinity<double>();
  }

  return (beta * sin_theta) / denominator;
}

/**
 * @brief Compute angle for maximum superluminal velocity.
 *
 * θ_max = arccos(β)
 *
 * At this angle, β_app = γβ.
 *
 * @param beta True velocity as fraction of c
 * @return Optimal viewing angle [rad]
 */
inline double superluminal_optimal_angle(double beta) {
  return std::acos(beta);
}

/**
 * @brief Compute maximum apparent superluminal velocity.
 *
 * β_app,max = γβ = β/√(1 - β²)
 *
 * @param beta True velocity as fraction of c
 * @return Maximum apparent velocity as fraction of c
 */
inline double superluminal_velocity_max(double beta) {
  return lorentz_factor(beta) * beta;
}

// ============================================================================
// Aberration
// ============================================================================

/**
 * @brief Compute relativistic aberration of angle.
 *
 * cos θ' = (cos θ - β) / (1 - β cos θ)
 *
 * Light emitted at angle θ in rest frame appears at θ' in moving frame.
 *
 * @param theta Angle in source rest frame [rad]
 * @param beta Observer velocity as fraction of c
 * @return Angle in observer frame [rad]
 */
inline double relativistic_aberration(double theta, double beta) {
  double cos_theta = std::cos(theta);
  double cos_theta_prime = (cos_theta - beta) / (1.0 - beta * cos_theta);

  // Clamp to valid range for acos
  cos_theta_prime = std::clamp(cos_theta_prime, -1.0, 1.0);

  return std::acos(cos_theta_prime);
}

/**
 * @brief Compute beaming half-angle (headlight effect).
 *
 * θ_beam ≈ 1/γ
 *
 * For highly relativistic motion, most radiation is concentrated
 * within a cone of half-angle ~1/γ.
 *
 * @param gamma Lorentz factor
 * @return Beaming half-angle [rad]
 */
inline double beaming_half_angle(double gamma) {
  if (gamma < 1.0) gamma = 1.0;
  return 1.0 / gamma;
}

// ============================================================================
// K-Corrections
// ============================================================================

/**
 * @brief Compute K-correction for power-law spectrum.
 *
 * For F_ν ∝ ν^α, the K-correction converts observed flux to
 * rest-frame flux at a different frequency:
 *
 *   F_rest = F_obs × (1 + z)^(1 + α)
 *
 * @param F_obs Observed flux density
 * @param z Redshift
 * @param alpha Spectral index
 * @return Rest-frame flux density at corresponding rest frequency
 */
inline double k_correction_power_law(double F_obs, double z, double alpha) {
  return F_obs * std::pow(1.0 + z, 1.0 + alpha);
}

/**
 * @brief Compute K-correction factor.
 *
 * K(z, α) = (1 + z)^(1 + α)
 *
 * @param z Redshift
 * @param alpha Spectral index
 * @return K-correction factor
 */
inline double k_correction_factor(double z, double alpha) {
  return std::pow(1.0 + z, 1.0 + alpha);
}

// ============================================================================
// Accretion Disk Doppler Beaming
// ============================================================================

/**
 * @brief Compute Doppler boost for orbiting disk material
 *
 * WHY: Rotating accretion disks show 10-1000x flux asymmetry due to beaming
 * WHAT: Relativistic Doppler factor for disk material in circular orbit
 * HOW: Keplerian velocity + viewing angle geometry
 *
 * For a circular orbit at radius r around a Kerr black hole:
 *   v_φ/c = √(M/(r - 2M ± a√M/r))
 *
 * Where ± is prograde (+) or retrograde (-).
 *
 * The Doppler boost factor for flux is:
 *   F_obs = δ^(3+α) F_emit
 *
 * where δ = 1/(γ(1 - β cos θ)) and α is the spectral index.
 *
 * References:
 *   - Begelman, Blandford, Rees (1984) Rev. Mod. Phys. 56, 255
 *   - Cunningham (1975) ApJ 202, 788 (Kerr disk imaging)
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter (-1 < a* < 1)
 * @param phi Azimuthal angle [rad] (0 = approaching, π = receding)
 * @param inclination Disk inclination [rad] (0 = face-on, π/2 = edge-on)
 * @param alpha Spectral index (F_ν ∝ ν^α), use 0 for blackbody
 * @return Doppler boost factor (1 = no boost)
 */
inline double disk_doppler_boost(double r, double a_star, double phi,
                                  double inclination, double alpha = 0.0) {
    // Clamp inputs
    a_star = std::clamp(a_star, -0.9999, 0.9999);
    r = std::max(r, 1.1);  // Minimum radius to avoid singularities

    // Keplerian velocity for circular orbit (Schwarzschild approximation)
    // v_φ/c ≈ √(M/r) for r >> M
    // Exact: v_φ/c = √(M/(r - 2M ± a√M/r))
    double discriminant = r - 2.0 + a_star * std::sqrt(1.0 / r);
    if (discriminant <= 0.0) {
        // Inside ISCO or unphysical orbit
        return 1.0;
    }

    double v_orbital = std::sqrt(1.0 / discriminant);
    double beta = std::min(v_orbital, 0.99);  // Cap at 0.99c

    // Velocity components in observer frame
    // v_x = v sin(φ) (perpendicular to line of sight if inclination = 0)
    // v_y = v cos(φ) (along line of sight projection)
    // v_z = 0 (disk is in equatorial plane)

    // Line-of-sight velocity component
    // θ is angle between velocity and line of sight
    // cos θ = (v · n) / |v|
    // where n is unit vector toward observer

    // For disk in x-y plane, observer at inclination i:
    // n = (0, sin i, cos i)
    // v = v_φ (-sin φ, cos φ, 0)
    // v · n = v_φ * sin(i) * cos(φ)

    double cos_theta = std::sin(inclination) * std::cos(phi);

    // Doppler factor
    double delta = doppler_factor(beta, std::acos(std::clamp(cos_theta, -1.0, 1.0)));

    // Beaming boost for flux
    double boost_exponent = 3.0 + alpha;  // δ^(3+α) for optically thin
    double boost = std::pow(delta, boost_exponent);

    // Clamp to reasonable range (avoid numerical instability)
    return std::clamp(boost, 0.01, 1000.0);
}

/**
 * @brief Compute maximum Doppler boost for disk (edge-on, approaching side)
 *
 * Convenience function for maximum boost calculation.
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @param alpha Spectral index
 * @return Maximum Doppler boost factor
 */
inline double disk_doppler_boost_max(double r, double a_star, double alpha = 0.0) {
    return disk_doppler_boost(r, a_star, 0.0, M_PI / 2.0, alpha);
}

/**
 * @brief Compute minimum Doppler boost for disk (edge-on, receding side)
 *
 * Convenience function for minimum boost calculation.
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @param alpha Spectral index
 * @return Minimum Doppler boost factor
 */
inline double disk_doppler_boost_min(double r, double a_star, double alpha = 0.0) {
    return disk_doppler_boost(r, a_star, M_PI, M_PI / 2.0, alpha);
}

} // namespace physics

#endif // PHYSICS_DOPPLER_H
