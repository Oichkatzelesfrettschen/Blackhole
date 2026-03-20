/**
 * @file scattering_models.h
 * @brief Phase 7.1b: Scattering Physics for Radiative Transfer
 *
 * Implements three scattering mechanisms:
 * 1. Thomson scattering: sigma_T ~ 6.65e-25 cm^2 (electron scattering, energy-independent)
 * 2. Rayleigh scattering: sigma_R ~ 1/nu^4 (small particles, dust grains)
 * 3. Mie scattering: sigma_Mie (particles with size ~ wavelength)
 *
 * WHY: Scattering affects photon transport, depolarization, and angular redistribution
 * WHAT: Scattering cross-sections and albedo factors across frequency range
 * HOW: Physics-based formulas with corrections for relativistic plasma
 */

#ifndef SCATTERING_MODELS_H
#define SCATTERING_MODELS_H

#include <algorithm>
#include <cmath>

#include "absorption_models.h"
#include "constants.h"

namespace physics {

// ============================================================================
// Thomson Scattering
// ============================================================================

/**
 * @brief Thomson scattering cross-section
 *
 * sigma_T = (8*pi/3) * (r_e)^2
 * where r_e = e^2 / (m_e * c^2) is the classical electron radius
 *
 * Constant with frequency for non-relativistic electrons.
 * At high energies (E >> m_e*c^2), transitions to Klein-Nishina regime.
 *
 * @return Thomson cross-section [cm^2]
 */
inline double thomsonCrossSection() {
  return SIGMA_THOMSON;
}

/**
 * @brief Klein-Nishina corrected Thomson scattering
 *
 * Accounting for recoil at high photon energies
 *
 * @param nu Photon frequency [Hz]
 * @param theta Dimensionless electron temperature (k*T / (m_e*c^2))
 * @return Effective Thomson cross-section [cm^2]
 */
inline double thomsonCrossSectionCorrected(double nu, double theta) {
  // Photon energy dimensionless
  double const x = (PLANCK * nu) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);

  // Klein-Nishina factor
  // sigma_KN / sigma_T = (1 + x) / ((1 + 2*x)^2) * [2*x*(1 + x)/(1 + 2*x) - ln(1 + 2*x)] + ln(1 +
  // 2*x)/(2*x) - (1 + 3*x)/((1 + 2*x)^3) Approximation for intermediate energies:
  double const sigma = SIGMA_THOMSON / (1.0 + (2.7 * x));

  // Temperature correction (increases effective cross-section for hot plasma)
  double const tempFactor = 1.0 + theta;

  return sigma * tempFactor;
}

/**
 * @brief Thomson scattering opacity (electron number density weighted)
 *
 * kappa_T = n_e * sigma_T
 *
 * @param n_e Electron number density [cm^-3]
 * @return Thomson opacity [cm^-1]
 */
inline double thomsonOpacity(double nE) {
  return nE * SIGMA_THOMSON;
}

// ============================================================================
// Rayleigh Scattering
// ============================================================================

/**
 * @brief Rayleigh scattering cross-section
 *
 * Applies to particles much smaller than wavelength (a << lambda)
 *
 * sigma_R = (128*pi^5 / 3) * (a^6 / lambda^4) * [(n^2 - 1) / (n^2 + 2)]^2
 *
 * Simplified for dust grains in plasma:
 * sigma_R ~ (pi * a^2) * (n_d / lambda)^4
 *
 * where a = grain radius ~ 0.1 to 1 micron, n_d = refractive index
 *
 * @param nu Observing frequency [Hz]
 * @param grain_radius Dust grain radius [cm]
 * @param refractive_index Complex refractive index (magnitude)
 * @return Rayleigh scattering cross-section [cm^2]
 */
inline double rayleighScattering(double nu, double grainRadius, double refractiveIndex) {
  // Wavelength [cm]
  double const lambda = SPEED_OF_LIGHT / nu;

  // Rayleigh formula approximation
  // sigma_R = (8*pi^5 / 3) * (a / lambda)^4 * (area) * polarizability factor
  double const x = (2.0 * physics::PI * grainRadius) / lambda; // Size parameter
  double const area = physics::PI * grainRadius * grainRadius;

  // Polarizability factor: (n^2 - 1)^2 / (n^2 + 2)^2
  double const nSq = refractiveIndex * refractiveIndex;
  double const polarizability = ((nSq - 1.0) * (nSq - 1.0)) / ((nSq + 2.0) * (nSq + 2.0));

  // Rayleigh scattering (4th power of size parameter)
  double const sigmaR =
      (128.0 * std::pow(physics::PI, 5.0) / 3.0) * std::pow(x, 4.0) * area * polarizability;

  return std::max(0.0, sigmaR);
}

/**
 * @brief Rayleigh scattering opacity
 *
 * @param nu Observing frequency [Hz]
 * @param grain_radius Dust grain radius [cm]
 * @param grain_density Dust grain number density [cm^-3]
 * @param refractive_index Refractive index of grain material
 * @return Rayleigh opacity [cm^-1]
 */
inline double rayleighOpacity(double nu, double grainRadius, double grainDensity,
                              double refractiveIndex) {
  double const sigma = rayleighScattering(nu, grainRadius, refractiveIndex);
  return grainDensity * sigma;
}

// ============================================================================
// Mie Scattering
// ============================================================================

/**
 * @brief Mie scattering efficiency
 *
 * Applies when particle size ~ wavelength
 *
 * Q_sca = 4*x*(1 - g) for moderately large particles
 * where x = pi*d/lambda (size parameter), g = asymmetry parameter
 *
 * @param nu Observing frequency [Hz]
 * @param grain_radius Grain radius [cm]
 * @return Mie scattering efficiency [dimensionless, typically 0-4]
 */
inline double mieScatteringEfficiency(double nu, double grainRadius) {
  // Wavelength [cm]
  double const lambda = SPEED_OF_LIGHT / nu;

  // Size parameter
  double const x = (physics::PI * 2.0 * grainRadius) / lambda;

  // Mie efficiency approximation (valid for x ~ 0.1 to 10)
  // Q_sca ~ x (small), transitions to Q_sca ~ 4 (geometric limit)

  double qSca;
  if (x < 0.05) {
    // Rayleigh limit: Q ~ x^4
    qSca = std::pow(x, 4.0);
  } else if (x < 1.0) {
    // Transition: Q ~ x
    qSca = x;
  } else {
    // Large particles: Q -> 4 (geometric limit)
    qSca = 2.0 + (4.0 / x * std::sin(x)) - ((8.0 / (x * x)) * (1.0 - std::cos(x)));
    qSca = std::clamp(qSca, 0.0, 4.0);
  }

  return qSca;
}

/**
 * @brief Mie scattering cross-section
 *
 * sigma_Mie = Q_sca * pi * a^2
 *
 * @param nu Observing frequency [Hz]
 * @param grain_radius Grain radius [cm]
 * @return Mie scattering cross-section [cm^2]
 */
inline double mieScatteringCrossSection(double nu, double grainRadius) {
  double const q = mieScatteringEfficiency(nu, grainRadius);
  double const area = physics::PI * grainRadius * grainRadius;
  return q * area;
}

/**
 * @brief Mie scattering opacity
 *
 * @param nu Observing frequency [Hz]
 * @param grain_radius Grain radius [cm]
 * @param grain_density Grain number density [cm^-3]
 * @return Mie opacity [cm^-1]
 */
inline double mieOpacity(double nu, double grainRadius, double grainDensity) {
  double const sigma = mieScatteringCrossSection(nu, grainRadius);
  return grainDensity * sigma;
}

// ============================================================================
// Scattering Albedo and Asymmetry
// ============================================================================

/**
 * @brief Single-scattering albedo
 *
 * Probability that a photon is scattered vs absorbed
 * omega = sigma_sca / (sigma_sca + sigma_abs)
 *
 * @param sigma_sca Scattering cross-section [cm^-1]
 * @param sigma_abs Absorption cross-section [cm^-1]
 * @return Single-scattering albedo [0, 1]
 */
inline double singleScatteringAlbedo(double sigmaSca, double sigmaAbs) {
  if (sigmaSca + sigmaAbs < 1e-30) {
    return 0.5;
  }
  return sigmaSca / (sigmaSca + sigmaAbs);
}

/**
 * @brief Asymmetry parameter (g)
 *
 * Average cosine of scattering angle: <cos(theta)> = g
 * g = 0: isotropic scattering
 * g > 0: forward scattering (typical for large particles)
 * g < 0: backward scattering
 *
 * For Rayleigh scattering: g ~ 0
 * For Thomson scattering: g ~ 0.2-0.3 (slightly forward peaked)
 * For Mie scattering: g ranges from 0 to ~0.9 depending on size
 *
 * @param scattering_type 0=Thomson, 1=Rayleigh, 2=Mie
 * @param nu Observing frequency [Hz]
 * @param grain_radius Grain radius (for Mie) [cm]
 * @return Asymmetry parameter g [−1, 1]
 */
inline double asymmetryParameter(int scatteringType, double nu, double grainRadius = 0.0) {
  double g = 0.0;

  if (scatteringType == 0) {
    // Thomson: slightly forward peaked
    g = 0.2;
  } else if (scatteringType == 1) {
    // Rayleigh: nearly isotropic
    g = 0.0;
  } else if (scatteringType == 2) {
    // Mie: depends on size parameter
    double const lambda = SPEED_OF_LIGHT / nu;
    double const x = (physics::PI * 2.0 * grainRadius) / lambda;

    if (x < 0.1) {
      g = 0.0; // Rayleigh-like
    } else if (x < 1.0) {
      g = 0.3 * x; // Transition
    } else {
      // Large particles: forward scattering
      g = std::clamp(0.5 + (0.3 * std::log10(x + 1.0)), 0.0, 0.95);
    }
  }

  return g;
}

// ============================================================================
// Total Scattering Opacity
// ============================================================================

/**
 * @brief Combined scattering opacity
 *
 * kappa_sca = kappa_T + kappa_R + kappa_Mie
 *
 * @param nu Observing frequency [Hz]
 * @param n_e Electron number density [cm^-3]
 * @param grain_radius Dust grain radius [cm]
 * @param grain_density Dust grain number density [cm^-3]
 * @return Total scattering opacity [cm^-1]
 */
inline double totalScatteringOpacity(double nu, double nE, double grainRadius,
                                     double grainDensity) {
  // Thomson from electrons
  double const kappaT = thomsonOpacity(nE);

  // Rayleigh from small grains
  double const kappaR =
      rayleighOpacity(nu, grainRadius, grainDensity, 1.5); // Refractive index ~ 1.5

  // Mie from larger grains
  double const kappaMie = mieOpacity(nu, grainRadius, grainDensity);

  return kappaT + kappaR + kappaMie;
}

}  // namespace physics

#endif  // SCATTERING_MODELS_H
