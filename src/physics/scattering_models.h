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

#include "constants.h"
#include "absorption_models.h"
#include <cmath>
#include <algorithm>

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
inline double thomson_cross_section() {
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
inline double thomson_cross_section_corrected(double nu, double theta) {
    // Photon energy dimensionless
    double x = (PLANCK * nu) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);

    // Klein-Nishina factor
    // sigma_KN / sigma_T = (1 + x) / ((1 + 2*x)^2) * [2*x*(1 + x)/(1 + 2*x) - ln(1 + 2*x)] + ln(1 + 2*x)/(2*x) - (1 + 3*x)/((1 + 2*x)^3)
    // Approximation for intermediate energies:
    double sigma = SIGMA_THOMSON / (1.0 + 2.7 * x);

    // Temperature correction (increases effective cross-section for hot plasma)
    double temp_factor = 1.0 + theta;

    return sigma * temp_factor;
}

/**
 * @brief Thomson scattering opacity (electron number density weighted)
 *
 * kappa_T = n_e * sigma_T
 *
 * @param n_e Electron number density [cm^-3]
 * @return Thomson opacity [cm^-1]
 */
inline double thomson_opacity(double n_e) {
    return n_e * SIGMA_THOMSON;
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
inline double rayleigh_scattering(double nu, double grain_radius, double refractive_index) {
    // Wavelength [cm]
    double lambda = SPEED_OF_LIGHT / nu;

    // Rayleigh formula approximation
    // sigma_R = (8*pi^5 / 3) * (a / lambda)^4 * (area) * polarizability factor
    double x = (2.0 * M_PI * grain_radius) / lambda;  // Size parameter
    double area = M_PI * grain_radius * grain_radius;

    // Polarizability factor: (n^2 - 1)^2 / (n^2 + 2)^2
    double n_sq = refractive_index * refractive_index;
    double polarizability = ((n_sq - 1.0) * (n_sq - 1.0)) / ((n_sq + 2.0) * (n_sq + 2.0));

    // Rayleigh scattering (4th power of size parameter)
    double sigma_R = (128.0 * std::pow(M_PI, 5.0) / 3.0) * std::pow(x, 4.0) * area * polarizability;

    return std::max(0.0, sigma_R);
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
inline double rayleigh_opacity(double nu, double grain_radius, double grain_density,
                               double refractive_index) {
    double sigma = rayleigh_scattering(nu, grain_radius, refractive_index);
    return grain_density * sigma;
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
inline double mie_scattering_efficiency(double nu, double grain_radius) {
    // Wavelength [cm]
    double lambda = SPEED_OF_LIGHT / nu;

    // Size parameter
    double x = (M_PI * 2.0 * grain_radius) / lambda;

    // Mie efficiency approximation (valid for x ~ 0.1 to 10)
    // Q_sca ~ x (small), transitions to Q_sca ~ 4 (geometric limit)

    double Q_sca;
    if (x < 0.05) {
        // Rayleigh limit: Q ~ x^4
        Q_sca = std::pow(x, 4.0);
    } else if (x < 1.0) {
        // Transition: Q ~ x
        Q_sca = x;
    } else {
        // Large particles: Q -> 4 (geometric limit)
        Q_sca = 2.0 + 4.0 / x * std::sin(x) - (8.0 / (x * x)) * (1.0 - std::cos(x));
        Q_sca = std::clamp(Q_sca, 0.0, 4.0);
    }

    return Q_sca;
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
inline double mie_scattering_cross_section(double nu, double grain_radius) {
    double Q = mie_scattering_efficiency(nu, grain_radius);
    double area = M_PI * grain_radius * grain_radius;
    return Q * area;
}

/**
 * @brief Mie scattering opacity
 *
 * @param nu Observing frequency [Hz]
 * @param grain_radius Grain radius [cm]
 * @param grain_density Grain number density [cm^-3]
 * @return Mie opacity [cm^-1]
 */
inline double mie_opacity(double nu, double grain_radius, double grain_density) {
    double sigma = mie_scattering_cross_section(nu, grain_radius);
    return grain_density * sigma;
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
inline double single_scattering_albedo(double sigma_sca, double sigma_abs) {
    if (sigma_sca + sigma_abs < 1e-30) return 0.5;
    return sigma_sca / (sigma_sca + sigma_abs);
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
inline double asymmetry_parameter(int scattering_type, double nu, double grain_radius = 0.0) {
    double g = 0.0;

    if (scattering_type == 0) {
        // Thomson: slightly forward peaked
        g = 0.2;
    } else if (scattering_type == 1) {
        // Rayleigh: nearly isotropic
        g = 0.0;
    } else if (scattering_type == 2) {
        // Mie: depends on size parameter
        double lambda = SPEED_OF_LIGHT / nu;
        double x = (M_PI * 2.0 * grain_radius) / lambda;

        if (x < 0.1) {
            g = 0.0;  // Rayleigh-like
        } else if (x < 1.0) {
            g = 0.3 * x;  // Transition
        } else {
            // Large particles: forward scattering
            g = std::clamp(0.5 + 0.3 * std::log10(x + 1.0), 0.0, 0.95);
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
inline double total_scattering_opacity(double nu, double n_e, double grain_radius,
                                       double grain_density) {
    // Thomson from electrons
    double kappa_T = thomson_opacity(n_e);

    // Rayleigh from small grains
    double kappa_R = rayleigh_opacity(nu, grain_radius, grain_density, 1.5);  // Refractive index ~ 1.5

    // Mie from larger grains
    double kappa_Mie = mie_opacity(nu, grain_radius, grain_density);

    return kappa_T + kappa_R + kappa_Mie;
}

}  // namespace physics

#endif  // SCATTERING_MODELS_H
