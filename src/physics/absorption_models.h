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
#include <algorithm>
#include <cmath>
#include <numbers>

namespace physics {

// ============================================================================
// Physical Constants (CGS units) -- aliases for self-contained readability
// ============================================================================

/// Speed of light [cm/s]
inline constexpr double SPEED_OF_LIGHT = C;

/// Planck constant [erg*s]
inline constexpr double PLANCK = 6.62607015e-27;

/// Electron mass [g]
inline constexpr double ELECTRON_MASS = 9.1093837015e-28;

/// Electron charge [esu]
inline constexpr double ELECTRON_CHARGE = 4.80320425e-10;

// SIGMA_THOMSON from constants.h (inline constexpr double SIGMA_THOMSON)

/// Boltzmann constant [erg/K]
inline constexpr double BOLTZMANN = K_B;

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
 * @param bField Magnetic field [Gauss]
 * @param nE Electron number density [cm^-3]
 * @param tempK Electron temperature [K] (for relativistic correction)
 * @return Absorption coefficient [cm^-1]
 */
[[nodiscard]] inline double synchrotronSelfAbsorption(double nu, double bField,
                                                       double nE, double tempK) {
  // Cyclotron frequency
  const double nuC = (ELECTRON_CHARGE * bField) /
                     (2.0 * std::numbers::pi * ELECTRON_MASS * SPEED_OF_LIGHT);

  // Synchrotron self-absorption (non-relativistic formula)
  // alpha_ssa = (n_e * sigma_T / 2) * (nu_c / nu)^2
  const double alphaSsa = (nE * SIGMA_THOMSON / 2.0) * (nuC * nuC) / (nu * nu);

  // Relativistic correction factor: increases absorption for high-energy electrons
  // theta = k*T / (m_e * c^2)
  const double theta =
      (BOLTZMANN * tempK) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);
  const double relativisticFactor = 1.0 + (2.4 * theta);

  return alphaSsa * relativisticFactor;
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
 * @param nE Electron number density [cm^-3]
 * @param tempK Electron temperature [K]
 * @return Absorption coefficient [cm^-1]
 */
[[nodiscard]] inline double freeFreeAbsorption(double nu, double nE, double tempK) {
  // Free-free absorption: Gaunt factor included
  // alpha_ff = (8 * sqrt(3) / 3) * (e^6 / (m_e * c^3 * h)) * n_e^2 * Z^2 / (T^(3/2) * nu^2)
  // Simplifies to: alpha_ff = K_ff * n_e^2 * g_ff / (T^(3/2) * nu^2)

  // Prefactor in CGS (includes Gaunt factor ~1 for radio to X-ray)
  const double kFf = 3.68e8;  // [cm^5 / K^(3/2) / s^2]

  // Debye length [cm]
  const double lambdaD = std::sqrt((BOLTZMANN * tempK) /
      (4.0 * std::numbers::pi * nE * ELECTRON_CHARGE * ELECTRON_CHARGE));

  // Approximate Gaunt factor: g_ff ~ ln(lambda_D * 2 * pi / lambda_c)
  // where lambda_c ~ h / (m_e * c) = Compton wavelength ~ 2.4e-10 cm
  const double lambdaC = 2.426e-10;
  const double gauntFactor = std::log((lambdaD / lambdaC) + 1.0);

  // Free-free absorption coefficient
  const double t32 = std::pow(tempK, 1.5);
  const double alphaFf = kFf * nE * nE * gauntFactor / (t32 * nu * nu);

  return std::max(0.0, alphaFf);
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
 * @param nE Electron number density [cm^-3]
 * @param theta Dimensionless temperature (k*T / (m_e*c^2)) [dimensionless]
 * @return Absorption coefficient [cm^-1]
 */
[[nodiscard]] inline double comptonAbsorption(double nu, double nE, double theta) {
  static_cast<void>(theta);
  // Photon energy [erg]
  const double hNu = PLANCK * nu;

  // Electron rest mass energy [erg]
  const double mEc2 = ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT;

  // Dimensionless photon energy
  const double x = hNu / mEc2;

  // Thomson scattering cross-section for low-energy photons
  double sigma = SIGMA_THOMSON;

  // Klein-Nishina correction factor
  // sigma_KN = sigma_T * (1 + x) / ((1 + 2*x)^2) * [...] (approx)
  // Approximation: sigma_KN ~ sigma_T / (1 + 2.7*x) for x << 1
  //                sigma_KN ~ sigma_T * 0.2 / x for x >> 1

  if (x < 0.1) {
    // Thomson limit (low-energy photons)
    sigma = SIGMA_THOMSON;
  } else if (x < 10.0) {
    // Intermediate regime
    sigma = SIGMA_THOMSON / (1.0 + (2.7 * x));
  } else {
    // Klein-Nishina limit (high-energy photons)
    sigma = SIGMA_THOMSON * (0.2 / x) * (1.0 + (x / 2.0));
  }

  // Compton absorption coefficient
  const double alphaComp = nE * sigma;

  return alphaComp;
}

// ============================================================================
// Total Absorption Coefficient
// ============================================================================

/**
 * @brief Combined absorption coefficient: SSA + free-free + Compton
 *
 * @param nu Observing frequency [Hz]
 * @param bField Magnetic field [Gauss]
 * @param nE Electron number density [cm^-3]
 * @param tempK Electron temperature [K]
 * @return Total absorption coefficient [cm^-1]
 */
[[nodiscard]] inline double totalAbsorptionCoefficient(double nu, double bField,
                                                        double nE, double tempK) {
  // Dimensionless temperature
  const double theta =
      (BOLTZMANN * tempK) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);

  // Individual components
  const double alphaSsa = synchrotronSelfAbsorption(nu, bField, nE, tempK);
  const double alphaFf = freeFreeAbsorption(nu, nE, tempK);
  const double alphaComp = comptonAbsorption(nu, nE, theta);

  // Total is sum of all contributions
  return alphaSsa + alphaFf + alphaComp;
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
 * @param bField Magnetic field [Gauss]
 * @param nE Electron number density [cm^-3]
 * @param tempK Electron temperature [K]
 * @return Dominant absorption mode (0=SSA, 1=free-free, 2=Compton)
 */
[[nodiscard]] inline int dominantAbsorptionMode(double nu, double bField,
                                                 double nE, double tempK) {
  const double theta =
      (BOLTZMANN * tempK) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);

  const double alphaSsa = synchrotronSelfAbsorption(nu, bField, nE, tempK);
  const double alphaFf = freeFreeAbsorption(nu, nE, tempK);
  const double alphaComp = comptonAbsorption(nu, nE, theta);

  if (alphaSsa >= alphaFf && alphaSsa >= alphaComp) { return 0; }
  if (alphaFf >= alphaSsa && alphaFf >= alphaComp) { return 1; }
  return 2;
}

/**
 * @brief Optical depth threshold frequency
 *
 * Frequency at which optical depth becomes unity over path length
 *
 * @param bField Magnetic field [Gauss]
 * @param nE Electron number density [cm^-3]
 * @param tempK Electron temperature [K]
 * @param pathLength Path length [cm]
 * @param mode Absorption mode to use (0=SSA, 1=free-free, 2=Compton)
 * @return Threshold frequency [Hz]
 */
[[nodiscard]] inline double opticalDepthThresholdFrequency(double bField, double nE,
                                                            double tempK,
                                                            double pathLength, int mode) {
  // Binary search for frequency where tau = 1
  double nuLow = 1e8;   // 100 MHz
  double nuHigh = 1e20; // 100 EeV

  for (int i = 0; i < 50; i++) {
    const double nuMid = std::sqrt(nuLow * nuHigh);

    double alpha;
    if (mode == 0) {
      alpha = synchrotronSelfAbsorption(nuMid, bField, nE, tempK);
    } else if (mode == 1) {
      alpha = freeFreeAbsorption(nuMid, nE, tempK);
    } else {
      const double theta =
          (BOLTZMANN * tempK) / (ELECTRON_MASS * SPEED_OF_LIGHT * SPEED_OF_LIGHT);
      alpha = comptonAbsorption(nuMid, nE, theta);
    }

    const double tau = alpha * pathLength;

    if (tau > 1.0) {
      nuHigh = nuMid;  // Decrease frequency
    } else {
      nuLow = nuMid;   // Increase frequency
    }
  }

  return std::sqrt(nuLow * nuHigh);
}

}  // namespace physics

#endif  // ABSORPTION_MODELS_H
