/**
 * @file synchrotron.h
 * @brief Synchrotron radiation from relativistic electrons.
 *
 * Synchrotron emission occurs when relativistic electrons spiral
 * in magnetic fields. Key for:
 * - Accretion disk coronae
 * - Relativistic jets
 * - Radio lobes
 *
 * Key formulas:
 *   Critical frequency: nu_c = (3/2) * (eB)/(2*pi*m_e*c) * gamma^2
 *   Power per electron: P = (4/3) * sigma_T * c * gamma^2 * U_B
 *   Cooling time: t_cool = gamma*m_e*c^2 / P
 *
 * References:
 *   - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 6
 *   - Longair (2011) "High Energy Astrophysics" Ch. 8
 *
 * Cleanroom implementation based on standard formulas.
 */

#ifndef PHYSICS_SYNCHROTRON_H
#define PHYSICS_SYNCHROTRON_H

#include <algorithm>
#include <cmath>

#include "constants.h"
#include "bessel_k.h"
#include "safe_limits.h"
#include "../../shader/include/synchrotron_lut_domain.h"

namespace physics {

// ============================================================================
// Synchrotron Constants (CGS)
// ============================================================================

/// Electron mass [g]
inline constexpr double M_ELECTRON = 9.1093837015e-28;

/// Electron charge [esu = g^1/2 cm^3/2 / s]
inline constexpr double E_CHARGE = 4.80320425e-10;

/// Classical electron radius r_e = e^2/(m_e c^2) [cm]
inline constexpr double R_ELECTRON = 2.8179403262e-13;

// SIGMA_THOMSON is defined in constants.h (included above)

/// Fine structure constant alpha ~ 1/137
inline constexpr double ALPHA_FINE = 7.2973525693e-3;

/// Synchrotron constant: 3e/(4*pi * m_e^3 * c^5) for critical frequency
inline constexpr double SYNCHROTRON_CONST =
    3.0 * E_CHARGE / (4.0 * PI * M_ELECTRON * M_ELECTRON * M_ELECTRON * C * C * C * C * C);

// ============================================================================
// Electron Gyration
// ============================================================================

/**
 * @brief Compute electron gyrofrequency (cyclotron frequency).
 *
 * omega_B = eB/(m_e c)
 * nu_B = omega_B/(2*pi) = eB/(2*pi*m_e*c)
 *
 * @param bField Magnetic field strength [Gauss]
 * @return Gyrofrequency [Hz]
 */
[[nodiscard]] inline double gyrofrequency(double bField) {
  return E_CHARGE * std::abs(bField) / (TWO_PI * M_ELECTRON * C);
}

/**
 * @brief Compute electron gyroradius (Larmor radius).
 *
 * r_L = gamma * m_e * c^2 / (eB) = gamma * v_perp / omega_B
 *
 * For relativistic electrons with v ~ c:
 * r_L ~ gamma * m_e * c / (eB)
 *
 * @param gamma Electron Lorentz factor
 * @param bField Magnetic field strength [Gauss]
 * @return Gyroradius [cm]
 */
[[nodiscard]] inline double gyroradius(double gamma, double bField) {
  if (std::abs(bField) < 1e-30) {
    return safeInfinity<double>();
  }
  return gamma * M_ELECTRON * C / (E_CHARGE * std::abs(bField));
}

// ============================================================================
// Synchrotron Emission
// ============================================================================

/**
 * @brief Compute synchrotron critical frequency.
 *
 * nu_c = (3/2) * (eB)/(2*pi*m_e*c) * gamma^2 * sin(alpha)
 *
 * For pitch angle alpha = pi/2 (perpendicular to field):
 * nu_c = (3/(4*pi)) * (eB)/(m_e*c) * gamma^2
 *
 * @param gamma Electron Lorentz factor
 * @param bField Magnetic field strength [Gauss]
 * @param pitchAngle Pitch angle [rad], default pi/2
 * @return Critical frequency [Hz]
 */
[[nodiscard]] inline double synchrotronFrequencyCritical(double gamma, double bField,
                                                         double pitchAngle = PI / 2.0) {
  const double sinAlpha = std::sin(pitchAngle);
  return (3.0 / (4.0 * PI)) * (E_CHARGE * std::abs(bField)) / (M_ELECTRON * C) * gamma * gamma *
         sinAlpha;
}

/**
 * @brief Compute peak synchrotron frequency.
 *
 * The spectrum peaks at nu_peak ~= 0.29 * nu_c
 *
 * @param gamma Electron Lorentz factor
 * @param bField Magnetic field strength [Gauss]
 * @return Peak frequency [Hz]
 */
[[nodiscard]] inline double synchrotronFrequencyPeak(double gamma, double bField) {
  return 0.29 * synchrotronFrequencyCritical(gamma, bField);
}

/**
 * @brief Compute synchrotron power radiated by single electron.
 *
 * P = (4/3) * sigma_T * c * gamma^2 * beta^2 * U_B
 *
 * where U_B = B^2/(8*pi) is magnetic energy density.
 * For ultrarelativistic electrons (beta ~ 1):
 * P = (4/3) * sigma_T * c * gamma^2 * (B^2 / (8*pi))
 *
 * @param gamma Electron Lorentz factor
 * @param bField Magnetic field strength [Gauss]
 * @return Power radiated [erg/s]
 */
[[nodiscard]] inline double synchrotronPowerSingleElectron(double gamma, double bField) {
  const double uB = bField * bField / (8.0 * PI);
  const double betaSq = 1.0 - (1.0 / (gamma * gamma));
  return (4.0 / 3.0) * SIGMA_THOMSON * C * gamma * gamma * betaSq * uB;
}

/**
 * @brief Compute synchrotron cooling time.
 *
 * t_cool = E / P = gamma * m_e * c^2 / P
 *
 * @param gamma Electron Lorentz factor
 * @param bField Magnetic field strength [Gauss]
 * @return Cooling time [s]
 */
[[nodiscard]] inline double synchrotronCoolingTime(double gamma, double bField) {
  const double pPow = synchrotronPowerSingleElectron(gamma, bField);
  if (pPow < 1e-50) {
    return safeInfinity<double>();
  }
  return gamma * M_ELECTRON * C * C / pPow;
}

/**
 * @brief Compute cooling Lorentz factor at given time.
 *
 * Electrons above gamma_cool have cooled significantly.
 * gamma_cool = 6*pi * m_e * c / (sigma_T * B^2 * t)
 *
 * @param bField Magnetic field strength [Gauss]
 * @param t Time since injection [s]
 * @return Cooling Lorentz factor
 */
[[nodiscard]] inline double synchrotronCoolingLorentzFactor(double bField, double t) {
  if (t < 1e-50 || std::abs(bField) < 1e-30) {
    return safeInfinity<double>();
  }
  return 6.0 * PI * M_ELECTRON * C / (SIGMA_THOMSON * bField * bField * t);
}

// ============================================================================
// Synchrotron Spectrum Functions
// ============================================================================

/**
 * @brief Synchrotron function F(x) for single electron.
 *
 * F(x) = x * integral_x^inf K_{5/3}(xi) dxi
 *
 * where x = nu/nu_c and K_{5/3} is the modified Bessel function of order 5/3.
 *
 * WHY: A fixed trapezoid kernel evaluates the scaled tail integral without
 * regime switches or an external special-function dependency.
 *
 * References:
 *   - Rybicki & Lightman (1979) Ch. 6, Eq. 6.31
 *   - DLMF 10.32.9, modified Bessel K integral representation
 *
 * @param x Dimensionless frequency nu/nu_c
 * @return F(x) synchrotron function value
 */
[[nodiscard]] inline double synchrotronF(double x) {
  if (x <= 0) {
    return 0.0;
  }

  const SynchrotronBesselValues<double> values = scaledSynchrotronBessel(x);
  return x * std::exp(-x) * values.scaledTailFiveThirds;
}

/**
 * @brief Synchrotron function G(x) for polarized emission.
 *
 * G(x) = x * K_{2/3}(x)
 *
 * Used for calculating polarization degree.
 *
 * @param x Dimensionless frequency nu/nu_c
 * @return G(x) function value
 */
[[nodiscard]] inline double synchrotronG(double x) {
  if (x <= 0) {
    return 0.0;
  }

  const SynchrotronBesselValues<double> values = scaledSynchrotronBessel(x);
  return x * std::exp(-x) * values.scaledKTwoThirds;
}

/**
 * @brief Compute synchrotron polarization degree.
 *
 * Pi = G(x) / F(x)
 *
 * For power-law electron distribution with index p:
 * Pi_max = (p + 1) / (p + 7/3)
 *
 * @param x Dimensionless frequency nu/nu_c
 * @return Polarization degree (0 to 1)
 */
[[nodiscard]] inline double synchrotronPolarization(double x) {
  if (x <= 0) {
    return 0.0;
  }
  // G/F = e^x K_{2/3}(x) / (e^x int_x^inf K_{5/3}): the common factor x e^-x
  // cancels, so the ratio stays finite where F and G themselves underflow.
  const SynchrotronBesselValues<double> values = scaledSynchrotronBessel(x);
  return values.scaledKTwoThirds / values.scaledTailFiveThirds;
}

// ============================================================================
// Power-Law Electron Distribution
// ============================================================================

/**
 * @brief Compute synchrotron spectrum from power-law electrons.
 *
 * For electron distribution N(gamma) ~ gamma^(-p) between gammaMin and gammaMax,
 * the spectrum is F_nu ~ nu^(-(p-1)/2) between break frequencies.
 *
 * @param nu Frequency [Hz]
 * @param bField Magnetic field [Gauss]
 * @param gammaMin Minimum electron Lorentz factor
 * @param gammaMax Maximum electron Lorentz factor
 * @param p Power-law index (typically 2-3)
 * @return Relative spectral power (normalized)
 */
[[nodiscard]] inline double synchrotronSpectrumPowerLaw(double nu, double bField, double gammaMin,
                                                        double gammaMax, double p) {
  // Characteristic frequencies
  const double nuMin = synchrotronFrequencyCritical(gammaMin, bField);
  const double nuMax = synchrotronFrequencyCritical(gammaMax, bField);

  if (nu <= 0) {
    return 0.0;
  }

  // Spectral index for optically thin synchrotron
  const double alpha = -(p - 1.0) / 2.0;

  if (nu < nuMin) {
    // Below minimum: self-absorbed regime, F ~ nu^(5/2)
    return std::pow(nu / nuMin, 2.5);
  }
  if (nu < nuMax) {
    // Power-law regime
    return std::pow(nu / nuMin, alpha);
  }
  // Exponential cutoff above gammaMax
  return std::pow(nuMax / nuMin, alpha) * std::exp(-(nu - nuMax) / nuMax);
}

/**
 * @brief Compute spectral index for power-law electrons.
 *
 * alpha = -(p - 1)/2 where F_nu ~ nu^alpha
 *
 * @param p Electron power-law index
 * @return Spectral index
 */
[[nodiscard]] inline double synchrotronSpectralIndex(double p) {
  return -(p - 1.0) / 2.0;
}

/**
 * @brief Compute electron index from spectral index.
 *
 * p = 1 - 2*alpha
 *
 * @param alpha Spectral index
 * @return Electron power-law index
 */
[[nodiscard]] inline double electronIndexFromSpectral(double alpha) {
  return 1.0 - (2.0 * alpha);
}

// ============================================================================
// Self-Absorption
// ============================================================================

/**
 * @brief Compute synchrotron self-absorption coefficient.
 *
 * The absorption coefficient scales as:
 * alpha_nu ~ nu^(-(p+4)/2) for power-law electrons
 *
 * Below the self-absorption frequency nu_a, the source becomes
 * optically thick and the spectrum changes to F_nu ~ nu^(5/2).
 *
 * @param nu Frequency [Hz]
 * @param bField Magnetic field [Gauss]
 * @param nE Electron density [cm^-3]
 * @param p Electron power-law index
 * @return Absorption coefficient [cm^-1]
 */
[[nodiscard]] inline double synchrotronAbsorptionCoefficient(double nu, double bField, double nE,
                                                             double p) {
  // Simplified formula (order of magnitude)
  const double nuB = gyrofrequency(bField);
  const double prefactor = 0.02 * E_CHARGE * nE / (M_ELECTRON * C);

  const double exponent = -(p + 4.0) / 2.0;
  return prefactor * std::pow(nuB, (p + 2.0) / 2.0) * std::pow(nu, exponent);
}

/**
 * @brief Compute self-absorption frequency.
 *
 * The frequency where tau_nu = 1 (optical depth unity).
 *
 * @param bField Magnetic field [Gauss]
 * @param nE Electron density [cm^-3]
 * @param rSize Source size [cm]
 * @param p Electron power-law index
 * @return Self-absorption frequency [Hz]
 */
[[nodiscard]] inline double synchrotronSelfAbsorptionFrequency(double bField, double nE,
                                                               double rSize, double p) {
  // Approximation: nu_a where tau = alpha_nu * R = 1
  const double nuB = gyrofrequency(bField);

  // Scaling: nu_a ~ (n_e R)^(2/(p+4)) * B^((p+2)/(p+4))
  const double exponent = 2.0 / (p + 4.0);
  return nuB * std::pow(nE * rSize / 1e20, exponent);
}

// ============================================================================
// GPU LUT Generation for G(x)
// ============================================================================

/**
 * @brief Generate a 1D lookup table for G(x) = x * K_{2/3}(x).
 *
 * WHY: We precompute G(x) on the CPU and upload it as a 1D float texture.
 * The shader samples this LUT
 * using log-spaced u = log(x/xMin) / log(xMax/xMin).
 *
 * The LUT covers x in [xMin, xMax] with nEntries entries, log-spaced for
 * uniform fractional resolution across the dynamic range.
 *
 * @param lut       Output array (must hold nEntries floats)
 * @param nEntries  Number of LUT entries (256 recommended)
 * @param xMin      Minimum x value (0.001 recommended)
 * @param xMax      Maximum x value (30.0 recommended -- G(30) ~ 1e-13)
 */
inline void synchrotronFGenerateLut(float *lut, int nEntries, double xMin = 0.001,
                                    double xMax = 30.0) {
  const double logRatio = std::log(xMax / xMin);
  for (int i = 0; i < nEntries; ++i) {
    const double u = static_cast<double>(i) / (nEntries - 1);
    const double x = xMin * std::exp(u * logRatio);
    lut[i] = static_cast<float>(synchrotronF(x));
  }
}

inline void synchrotronGGenerateLut(float *lut, int nEntries, double xMin = 0.001,
                                    double xMax = 30.0) {
  const double logRatio = std::log(xMax / xMin);
  for (int i = 0; i < nEntries; ++i) {
    const double u = static_cast<double>(i) / (nEntries - 1);
    const double x = xMin * std::exp(u * logRatio);
    lut[i] = static_cast<float>(synchrotronG(x));
  }
}

/// LUT range constants matching the generation defaults above.
/// Shaders read the same single-source values via the shared header.
constexpr float SYNCH_G_LUT_X_MIN = static_cast<float>(SYNCH_G_LUT_DOMAIN_X_MIN);
constexpr float SYNCH_G_LUT_X_MAX = static_cast<float>(SYNCH_G_LUT_DOMAIN_X_MAX);

} // namespace physics

#endif // PHYSICS_SYNCHROTRON_H
