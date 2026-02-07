/**
 * @file absorption_models.h
 * @brief Phase 7.1a: Absorption Models for Radiative Transfer
 *
 * Implements three absorption mechanisms:
 * 1. Synchrotron self-absorption (SSA): alpha_ssa ~ B^2 / nu^2
 * 2. Free-free absorption: alpha_ff ~ n_e * T^(-3/2) / nu^2
 * 3. Compton absorption: alpha_comp ~ sigma_T * n_e (Thomson cross-section)
 *
 * WHY: Absorption determines how radiation propagates through magnetized plasma
 * WHAT: Absorption coefficients for SSA, free-free, Compton across frequency range
 * HOW: Physics-based formulas from Rybicki-Lightman + EOS corrections for hot plasma
 */

#ifndef ABSORPTION_MODELS_H
#define ABSORPTION_MODELS_H

#include "constants.h"
#include <cmath>

namespace physics {

// ============================================================================
// Physical Constants (CGS units)
// ============================================================================

/// Speed of light [cm/s]
constexpr double SPEED_OF_LIGHT = 2.99792458e10;

/// Planck constant [erg*s]
constexpr double PLANCK = 6.62607015e-27;

/// Electron mass [g]
constexpr double ELECTRON_MASS = 9.1093837015e-28;

/// Electron charge [esu]
constexpr double ELECTRON_CHARGE = 4.80320425e-10;

/// Thomson cross-section [cm^2]
constexpr double SIGMA_THOMSON = 6.6524587321e-25;

/// Boltzmann constant [erg/K]
constexpr double BOLTZMANN = 1.380649e-16;

// ============================================================================
// Synchrotron Self-Absorption (SSA)
// ============================================================================

/**
 * @brief Synchrotron self-absorption coefficient
 *
 * alpha_ssa = (nu_0^2 / (8 * nu^2)) * (n_e * sigma_T * B / (rho * c))
 * where nu_0 = e*B / (2*pi*m_e*c) is the cyclotron frequency
 *
 * Simplified form (Rybicki-Lightman):
 * alpha_ssa ~ B^2 / (nu^2 * n_e) at low frequencies
 *
 * @param nu Observing frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param n_e Electron number density [cm^-3]
 * @param T Electron temperature [K] (for relativistic correction)
 * @return Absorption coefficient [cm^-1]
 */
inline double synchrotron_self_absorption(double nu, double B, double n_e, double T) {
    // Cyclotron frequency
    double nu_c = (ELECTRON_CHARGE * B) / (2.0 * M_PI * ELECTRON_MASS * SPEED_OF_LIGHT);

    // Synchrotron self-absorption (non-relativistic formula)
    // alpha_ssa = (n_e * sigma_T / 2) * (nu_c / nu)^2
    double alpha_ssa = (n_e * SIGMA_THOMSON / 2.0) * (nu_c * nu_c) / (nu * nu);

    // Relativistic correction factor: increases absorption for high-energy electrons
    // theta = k*T / (m_e * c^2)
    double theta = (BOLTZMANN * T) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);
    double relativistic_factor = (1.0 + 2.4 * theta);  // Approximation for mildly relativistic

    return alpha_ssa * relativistic_factor;
}

// ============================================================================
// Free-Free Absorption
// ============================================================================

/**
 * @brief Free-free (bremsstrahlung) absorption coefficient
 *
 * alpha_ff ~ (n_e * n_i / T^(3/2)) * (1 / nu^2)
 *
 * For hydrogen plasma, n_i ~ n_e (quasi-neutrality)
 *
 * Gaunt factor approximation: g_ff ~ ln(sqrt(3) * lambda_D / lambda_c)
 * where lambda_D = Debye length, lambda_c = Compton wavelength
 *
 * @param nu Observing frequency [Hz]
 * @param n_e Electron number density [cm^-3]
 * @param T Electron temperature [K]
 * @return Absorption coefficient [cm^-1]
 */
inline double free_free_absorption(double nu, double n_e, double T) {
    // Free-free absorption: Gaunt factor included
    // alpha_ff = (8 * sqrt(3) / 3) * (e^6 / (m_e * c^3 * h)) * n_e^2 * Z^2 / (T^(3/2) * nu^2)
    // Simplifies to: alpha_ff = K_ff * n_e^2 * g_ff / (T^(3/2) * nu^2)

    // Prefactor in CGS (includes Gaunt factor ~1 for radio to X-ray)
    double K_ff = 3.68e8;  // [cm^5 / K^(3/2) / s^2]

    // Debye length [cm]
    double lambda_D = std::sqrt((BOLTZMANN * T) / (4.0 * M_PI * n_e * ELECTRON_CHARGE * ELECTRON_CHARGE));

    // Approximate Gaunt factor: g_ff ~ ln(lambda_D * 2 * pi / lambda_c)
    // where lambda_c ~ h / (m_e * c) = Compton wavelength ~ 2.4e-10 cm
    double lambda_c = 2.426e-10;
    double gaunt_factor = std::log(lambda_D / lambda_c + 1.0);

    // Free-free absorption coefficient
    double T_32 = std::pow(T, 1.5);
    double alpha_ff = K_ff * n_e * n_e * gaunt_factor / (T_32 * nu * nu);

    return std::max(0.0, alpha_ff);
}

// ============================================================================
// Compton Scattering Absorption
// ============================================================================

/**
 * @brief Compton absorption coefficient (electron scattering)
 *
 * Compton absorption is dominated by Thomson scattering for low-energy photons.
 * For high-energy photons (E > m_e*c^2), Klein-Nishina cross-section applies.
 *
 * alpha_comp = n_e * sigma(E)
 * where sigma(E) = sigma_Thomson * (Klein-Nishina correction)
 *
 * @param nu Observing frequency [Hz]
 * @param n_e Electron number density [cm^-3]
 * @param theta Dimensionless temperature (k*T / (m_e*c^2)) [dimensionless]
 * @return Absorption coefficient [cm^-1]
 */
inline double compton_absorption(double nu, double n_e, double /* theta */) {
    // Photon energy [erg]
    double h_nu = PLANCK * nu;

    // Electron rest mass energy [erg]
    double m_e_c2 = ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT;

    // Dimensionless photon energy
    double x = h_nu / m_e_c2;

    // Thomson scattering cross-section for low-energy photons
    double sigma = SIGMA_THOMSON;

    // Klein-Nishina correction factor
    // sigma_KN = sigma_T * (1 + x) / ((1 + 2*x)^2) * [(1 + 2*x)/(1 + 2*x) - ln(1 + 2*x)/x] + ...
    // Approximation: sigma_KN ~ sigma_T / (1 + 2.7*x) for x << 1
    //                sigma_KN ~ sigma_T * 0.2 / x for x >> 1

    if (x < 0.1) {
        // Thomson limit (low-energy photons)
        sigma = SIGMA_THOMSON;
    } else if (x < 10.0) {
        // Intermediate regime
        sigma = SIGMA_THOMSON / (1.0 + 2.7 * x);
    } else {
        // Klein-Nishina limit (high-energy photons)
        sigma = SIGMA_THOMSON * (0.2 / x) * (1.0 + x / 2.0);
    }

    // Compton absorption coefficient
    double alpha_comp = n_e * sigma;

    return alpha_comp;
}

// ============================================================================
// Total Absorption Coefficient
// ============================================================================

/**
 * @brief Combined absorption coefficient: SSA + free-free + Compton
 *
 * @param nu Observing frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param n_e Electron number density [cm^-3]
 * @param T Electron temperature [K]
 * @return Total absorption coefficient [cm^-1]
 */
inline double total_absorption_coefficient(double nu, double B, double n_e, double T) {
    // Dimensionless temperature
    double theta = (BOLTZMANN * T) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);

    // Individual components
    double alpha_ssa = synchrotron_self_absorption(nu, B, n_e, T);
    double alpha_ff = free_free_absorption(nu, n_e, T);
    double alpha_comp = compton_absorption(nu, n_e, theta);

    // Total is sum of all contributions
    return alpha_ssa + alpha_ff + alpha_comp;
}

// ============================================================================
// Absorption Diagnostics
// ============================================================================

/**
 * @brief Dominant absorption mechanism at given frequency
 *
 * Returns which process dominates: 0=SSA, 1=free-free, 2=Compton
 *
 * @param nu Observing frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param n_e Electron number density [cm^-3]
 * @param T Electron temperature [K]
 * @return Dominant absorption mode (0=SSA, 1=free-free, 2=Compton)
 */
inline int dominant_absorption_mode(double nu, double B, double n_e, double T) {
    double theta = (BOLTZMANN * T) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);

    double alpha_ssa = synchrotron_self_absorption(nu, B, n_e, T);
    double alpha_ff = free_free_absorption(nu, n_e, T);
    double alpha_comp = compton_absorption(nu, n_e, theta);

    if (alpha_ssa >= alpha_ff && alpha_ssa >= alpha_comp) return 0;
    if (alpha_ff >= alpha_ssa && alpha_ff >= alpha_comp) return 1;
    return 2;
}

/**
 * @brief Optical depth threshold frequency
 *
 * Frequency at which optical depth becomes unity over path length
 *
 * @param B Magnetic field [Gauss]
 * @param n_e Electron number density [cm^-3]
 * @param T Electron temperature [K]
 * @param path_length Path length [cm]
 * @param mode Absorption mode to use (0=SSA, 1=free-free, 2=Compton)
 * @return Threshold frequency [Hz]
 */
inline double optical_depth_threshold_frequency(double B, double n_e, double T,
                                                  double path_length, int mode) {
    // Binary search for frequency where tau = 1
    double nu_low = 1e8;   // 100 MHz
    double nu_high = 1e20; // 100 EeV

    for (int i = 0; i < 50; i++) {
        double nu_mid = std::sqrt(nu_low * nu_high);

        double alpha;
        if (mode == 0) {
            alpha = synchrotron_self_absorption(nu_mid, B, n_e, T);
        } else if (mode == 1) {
            alpha = free_free_absorption(nu_mid, n_e, T);
        } else {
            double theta = (BOLTZMANN * T) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);
            alpha = compton_absorption(nu_mid, n_e, theta);
        }

        double tau = alpha * path_length;

        if (tau > 1.0) {
            nu_high = nu_mid;  // Decrease frequency
        } else {
            nu_low = nu_mid;   // Increase frequency
        }
    }

    return std::sqrt(nu_low * nu_high);
}

}  // namespace physics

#endif  // ABSORPTION_MODELS_H
