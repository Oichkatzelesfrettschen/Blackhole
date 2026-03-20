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
 *   Lorentz factor: gamma = 1/sqrt(1 - beta^2)
 *   Doppler factor: delta = 1/(gamma*(1 - beta*cos(theta)))
 *   Observed flux: F_obs = delta^(3+alpha) * F_emit for power-law spectrum
 *
 * References:
 *   - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics"
 *   - Begelman, Blandford, Rees (1984) Rev. Mod. Phys. 56, 255
 *
 * Cleanroom implementation based on standard SR/GR formulas.
 */

#ifndef PHYSICS_DOPPLER_H
#define PHYSICS_DOPPLER_H

#include "safe_limits.h"
#include <algorithm>
#include <cmath>
// NOLINTBEGIN(misc-include-cleaner)
// WHY: M_PI is provided by <cmath> on most platforms but is technically
// a POSIX extension; some toolchains require the include to be visible.
#include <numbers>
// NOLINTEND(misc-include-cleaner)

namespace physics {

// ============================================================================
// Lorentz Factor
// ============================================================================

/**
 * @brief Compute Lorentz factor from velocity.
 *
 * gamma = 1/sqrt(1 - beta^2)
 *
 * @param beta Velocity as fraction of c (v/c), must be in [0, 1)
 * @return Lorentz factor >= 1
 */
[[nodiscard]] inline double lorentzFactor(double beta) {
  if (beta < 0.0) { beta = -beta; }
  if (beta >= 1.0) {
    return safeInfinity<double>();
  }
  return 1.0 / std::sqrt(1.0 - (beta * beta));
}

/**
 * @brief Compute velocity beta from Lorentz factor.
 *
 * beta = sqrt(1 - 1/gamma^2)
 *
 * @param gamma Lorentz factor >= 1
 * @return Velocity as fraction of c
 */
[[nodiscard]] inline double betaFromGamma(double gamma) {
  gamma = std::max(gamma, 1.0);
  return std::sqrt(1.0 - (1.0 / (gamma * gamma)));
}

// ============================================================================
// Doppler Factor
// ============================================================================

/**
 * @brief Compute relativistic Doppler factor.
 *
 * delta = 1/(gamma*(1 - beta*cos(theta)))
 *
 * where theta is the angle between velocity and line of sight.
 * theta = 0 means approaching (blueshift), theta = pi means receding (redshift).
 *
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @return Doppler factor delta
 */
[[nodiscard]] inline double dopplerFactor(double beta, double theta) {
  const double gamma = lorentzFactor(beta);
  const double cosTheta = std::cos(theta);
  const double denominator = gamma * (1.0 - (beta * cosTheta));

  if (std::abs(denominator) < 1e-30) {
    return safeInfinity<double>();
  }

  return 1.0 / denominator;
}

/**
 * @brief Compute Doppler factor for head-on approach (theta = 0).
 *
 * delta_max = sqrt((1 + beta)/(1 - beta)) = gamma*(1 + beta)
 *
 * @param beta Velocity as fraction of c
 * @return Maximum Doppler factor (approaching)
 */
[[nodiscard]] inline double dopplerFactorApproaching(double beta) {
  if (beta >= 1.0) {
    return safeInfinity<double>();
  }
  return std::sqrt((1.0 + beta) / (1.0 - beta));
}

/**
 * @brief Compute Doppler factor for direct recession (theta = pi).
 *
 * delta_min = sqrt((1 - beta)/(1 + beta)) = 1/(gamma*(1 + beta))
 *
 * @param beta Velocity as fraction of c
 * @return Minimum Doppler factor (receding)
 */
[[nodiscard]] inline double dopplerFactorReceding(double beta) {
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
 * nu_obs = delta * nu_emit
 *
 * @param nuEmit Emitted frequency [Hz]
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @return Observed frequency [Hz]
 */
[[nodiscard]] inline double dopplerShiftRelativistic(double nuEmit, double beta, double theta) {
  return dopplerFactor(beta, theta) * nuEmit;
}

/**
 * @brief Compute transverse Doppler shift (theta = pi/2).
 *
 * nu_obs = nu_emit / gamma (always redshift due to time dilation)
 *
 * @param nuEmit Emitted frequency [Hz]
 * @param beta Velocity as fraction of c
 * @return Observed frequency [Hz]
 */
[[nodiscard]] inline double dopplerShiftTransverse(double nuEmit, double beta) {
  return nuEmit / lorentzFactor(beta);
}

/**
 * @brief Compute observed frequency from cosmological redshift.
 *
 * nu_obs = nu_emit / (1 + z)
 *
 * @param nuEmit Rest-frame frequency [Hz]
 * @param z Cosmological redshift
 * @return Observed frequency [Hz]
 */
[[nodiscard]] inline double observedFrequency(double nuEmit, double z) {
  return nuEmit / (1.0 + z);
}

/**
 * @brief Compute rest-frame frequency from observed frequency.
 *
 * nu_emit = nu_obs * (1 + z)
 *
 * @param nuObs Observed frequency [Hz]
 * @param z Cosmological redshift
 * @return Rest-frame frequency [Hz]
 */
[[nodiscard]] inline double restFrameFrequency(double nuObs, double z) {
  return nuObs * (1.0 + z);
}

// ============================================================================
// Relativistic Beaming
// ============================================================================

/**
 * @brief Compute intensity boost from relativistic beaming.
 *
 * For a power-law spectrum F_nu ~ nu^alpha:
 *   I_obs = delta^(3+alpha) * I_emit (optically thin)
 *
 * @param iEmit Emitted intensity
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @param alpha Spectral index, use 0 for blackbody
 * @return Observed intensity
 */
[[nodiscard]] inline double relativisticBeamingIntensity(double iEmit, double beta,
                                                          double theta, double alpha) {
  const double delta = dopplerFactor(beta, theta);
  return iEmit * std::pow(delta, 3.0 + alpha);
}

/**
 * @brief Compute flux density boost from relativistic beaming.
 *
 * F_obs = delta^(3+alpha) * F_emit for isotropic emitter
 *
 * @param fEmit Emitted flux density
 * @param beta Velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @param alpha Spectral index
 * @return Observed flux density
 */
[[nodiscard]] inline double relativisticBeamingFlux(double fEmit, double beta,
                                                     double theta, double alpha) {
  const double delta = dopplerFactor(beta, theta);
  return fEmit * std::pow(delta, 3.0 + alpha);
}

/**
 * @brief Compute apparent superluminal velocity.
 *
 * For an object moving at angle theta to line of sight:
 *   beta_app = (beta * sin(theta)) / (1 - beta * cos(theta))
 *
 * @param beta True velocity as fraction of c
 * @param theta Angle between velocity and line of sight [rad]
 * @return Apparent transverse velocity as fraction of c
 */
[[nodiscard]] inline double apparentSuperluminalVelocity(double beta, double theta) {
  const double sinTheta = std::sin(theta);
  const double cosTheta = std::cos(theta);
  const double denominator = 1.0 - (beta * cosTheta);

  if (std::abs(denominator) < 1e-30) {
    return safeInfinity<double>();
  }

  return (beta * sinTheta) / denominator;
}

/**
 * @brief Compute angle for maximum superluminal velocity.
 *
 * theta_max = arccos(beta)
 *
 * At this angle, beta_app = gamma*beta.
 *
 * @param beta True velocity as fraction of c
 * @return Optimal viewing angle [rad]
 */
[[nodiscard]] inline double superluminalOptimalAngle(double beta) {
  return std::acos(beta);
}

/**
 * @brief Compute maximum apparent superluminal velocity.
 *
 * beta_app_max = gamma*beta = beta/sqrt(1 - beta^2)
 *
 * @param beta True velocity as fraction of c
 * @return Maximum apparent velocity as fraction of c
 */
[[nodiscard]] inline double superluminalVelocityMax(double beta) {
  return lorentzFactor(beta) * beta;
}

// ============================================================================
// Aberration
// ============================================================================

/**
 * @brief Compute relativistic aberration of angle.
 *
 * cos(theta') = (cos(theta) - beta) / (1 - beta*cos(theta))
 *
 * Light emitted at angle theta in rest frame appears at theta' in moving frame.
 *
 * @param theta Angle in source rest frame [rad]
 * @param beta Observer velocity as fraction of c
 * @return Angle in observer frame [rad]
 */
[[nodiscard]] inline double relativisticAberration(double theta, double beta) {
  const double cosTheta = std::cos(theta);
  double cosThetaPrime = (cosTheta - beta) / (1.0 - (beta * cosTheta));

  // Clamp to valid range for acos
  cosThetaPrime = std::clamp(cosThetaPrime, -1.0, 1.0);

  return std::acos(cosThetaPrime);
}

/**
 * @brief Compute beaming half-angle (headlight effect).
 *
 * theta_beam ~ 1/gamma
 *
 * For highly relativistic motion, most radiation is concentrated
 * within a cone of half-angle ~1/gamma.
 *
 * @param gamma Lorentz factor
 * @return Beaming half-angle [rad]
 */
[[nodiscard]] inline double beamingHalfAngle(double gamma) {
  gamma = std::max(gamma, 1.0);
  return 1.0 / gamma;
}

// ============================================================================
// K-Corrections
// ============================================================================

/**
 * @brief Compute K-correction for power-law spectrum.
 *
 * For F_nu ~ nu^alpha, the K-correction converts observed flux to
 * rest-frame flux at a different frequency:
 *
 *   F_rest = F_obs * (1 + z)^(1 + alpha)
 *
 * @param fObs Observed flux density
 * @param z Redshift
 * @param alpha Spectral index
 * @return Rest-frame flux density at corresponding rest frequency
 */
[[nodiscard]] inline double kCorrectionPowerLaw(double fObs, double z, double alpha) {
  return fObs * std::pow(1.0 + z, 1.0 + alpha);
}

/**
 * @brief Compute K-correction factor.
 *
 * K(z, alpha) = (1 + z)^(1 + alpha)
 *
 * @param z Redshift
 * @param alpha Spectral index
 * @return K-correction factor
 */
[[nodiscard]] inline double kCorrectionFactor(double z, double alpha) {
  return std::pow(1.0 + z, 1.0 + alpha);
}

// ============================================================================
// Accretion Disk Doppler Beaming
// ============================================================================

/**
 * @brief Compute Doppler boost for orbiting disk material.
 *
 * WHY: Rotating accretion disks show 10-1000x flux asymmetry due to beaming.
 * WHAT: Relativistic Doppler factor for disk material in circular orbit.
 * HOW: Keplerian velocity + viewing angle geometry.
 *
 * For a circular orbit at radius r around a Kerr black hole:
 *   v_phi/c = sqrt(M/(r - 2M +/- a*sqrt(M/r)))
 *
 * The Doppler boost factor for flux is:
 *   F_obs = delta^(3+alpha) * F_emit
 *
 * where delta = 1/(gamma*(1 - beta*cos(theta))) and alpha is the spectral index.
 *
 * References:
 *   - Begelman, Blandford, Rees (1984) Rev. Mod. Phys. 56, 255
 *   - Cunningham (1975) ApJ 202, 788 (Kerr disk imaging)
 *
 * @param r Radius in units of M
 * @param aStar Dimensionless spin parameter (-1 < a* < 1)
 * @param phi Azimuthal angle [rad] (0 = approaching, pi = receding)
 * @param inclination Disk inclination [rad] (0 = face-on, pi/2 = edge-on)
 * @param alpha Spectral index, use 0 for blackbody
 * @return Doppler boost factor (1 = no boost)
 */
[[nodiscard]] inline double diskDopplerBoost(double r, double aStar, double phi,
                                              double inclination, double alpha = 0.0) {
  // Clamp inputs
  aStar = std::clamp(aStar, -0.9999, 0.9999);
  r = std::max(r, 1.1);  // Minimum radius to avoid singularities

  // Keplerian velocity for circular orbit
  // v_phi/c = sqrt(1/(r - 2 + aStar*sqrt(1/r)))
  const double discriminant = (r - 2.0) + (aStar * std::sqrt(1.0 / r));
  if (discriminant <= 0.0) {
    return 1.0; // Inside ISCO or unphysical orbit
  }

  const double vOrbital = std::sqrt(1.0 / discriminant);
  const double beta = std::min(vOrbital, 0.99);  // Cap at 0.99c

  // Line-of-sight velocity component:
  // For disk in x-y plane, observer at inclination i:
  //   n = (0, sin(i), cos(i));  v = v_phi*(-sin(phi), cos(phi), 0)
  //   v.n = v_phi * sin(i) * cos(phi)
  const double cosTheta = std::sin(inclination) * std::cos(phi);

  // Doppler factor
  const double delta = dopplerFactor(beta, std::acos(std::clamp(cosTheta, -1.0, 1.0)));

  // Beaming boost: delta^(3+alpha) for optically thin
  const double boost = std::pow(delta, 3.0 + alpha);

  // Clamp to reasonable range (avoid numerical instability)
  return std::clamp(boost, 0.01, 1000.0);
}

/**
 * @brief Compute maximum Doppler boost for disk (edge-on, approaching side).
 *
 * @param r Radius in units of M
 * @param aStar Dimensionless spin parameter
 * @param alpha Spectral index
 * @return Maximum Doppler boost factor
 */
[[nodiscard]] inline double diskDopplerBoostMax(double r, double aStar, double alpha = 0.0) {
  return diskDopplerBoost(r, aStar, 0.0, std::numbers::pi / 2.0, alpha);
}

/**
 * @brief Compute minimum Doppler boost for disk (edge-on, receding side).
 *
 * @param r Radius in units of M
 * @param aStar Dimensionless spin parameter
 * @param alpha Spectral index
 * @return Minimum Doppler boost factor
 */
[[nodiscard]] inline double diskDopplerBoostMin(double r, double aStar, double alpha = 0.0) {
  return diskDopplerBoost(r, aStar, std::numbers::pi, std::numbers::pi / 2.0, alpha);
}

} // namespace physics

#endif // PHYSICS_DOPPLER_H
