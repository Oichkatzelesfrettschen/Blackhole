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
 *   Critical frequency: ν_c = (3/2) × (eB)/(2πm_e c) × γ²
 *   Power per electron: P = (4/3) σ_T c γ² U_B
 *   Cooling time: t_cool = γm_e c² / P
 *
 * References:
 *   - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 6
 *   - Longair (2011) "High Energy Astrophysics" Ch. 8
 *
 * Cleanroom implementation based on standard formulas.
 */

#ifndef PHYSICS_SYNCHROTRON_H
#define PHYSICS_SYNCHROTRON_H

#include "constants.h"
#include "safe_limits.h"
#include <cmath>

namespace physics {

// ============================================================================
// Synchrotron Constants (CGS)
// ============================================================================

/// Electron mass [g]
inline constexpr double M_ELECTRON = 9.1093837015e-28;

/// Electron charge [esu = g^1/2 cm^3/2 / s]
inline constexpr double E_CHARGE = 4.80320425e-10;

/// Classical electron radius r_e = e²/(m_e c²) [cm]
inline constexpr double R_ELECTRON = 2.8179403262e-13;

/// Thomson cross section σ_T = (8π/3) r_e² [cm²]
inline constexpr double SIGMA_THOMSON = 6.6524587321e-25;

/// Fine structure constant α ≈ 1/137
inline constexpr double ALPHA_FINE = 7.2973525693e-3;

/// Synchrotron constant: 3e/(4π m_e³ c⁵) for critical frequency
inline constexpr double SYNCHROTRON_CONST = 3.0 * E_CHARGE / (4.0 * PI * M_ELECTRON * M_ELECTRON * M_ELECTRON * C * C * C * C * C);

// ============================================================================
// Electron Gyration
// ============================================================================

/**
 * @brief Compute electron gyrofrequency (cyclotron frequency).
 *
 * ω_B = eB/(m_e c)
 * ν_B = ω_B/(2π) = eB/(2π m_e c)
 *
 * @param B Magnetic field strength [Gauss]
 * @return Gyrofrequency [Hz]
 */
inline double gyrofrequency(double B) {
  return E_CHARGE * std::abs(B) / (TWO_PI * M_ELECTRON * C);
}

/**
 * @brief Compute electron gyroradius (Larmor radius).
 *
 * r_L = γ m_e c² / (eB) = γ v_⊥ / ω_B
 *
 * For relativistic electrons with v ≈ c:
 * r_L ≈ γ m_e c / (eB)
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Gyroradius [cm]
 */
inline double gyroradius(double gamma, double B) {
  if (std::abs(B) < 1e-30) {
    return safe_infinity<double>();
  }
  return gamma * M_ELECTRON * C / (E_CHARGE * std::abs(B));
}

// ============================================================================
// Synchrotron Emission
// ============================================================================

/**
 * @brief Compute synchrotron critical frequency.
 *
 * ν_c = (3/2) × (eB)/(2π m_e c) × γ² × sin α
 *
 * For pitch angle α = π/2 (perpendicular to field):
 * ν_c = (3/4π) × (eB)/(m_e c) × γ²
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @param pitch_angle Pitch angle [rad], default π/2
 * @return Critical frequency [Hz]
 */
inline double synchrotron_frequency_critical(double gamma, double B,
                                              double pitch_angle = PI / 2.0) {
  double sin_alpha = std::sin(pitch_angle);
  return (3.0 / (4.0 * PI)) * (E_CHARGE * std::abs(B)) / (M_ELECTRON * C) *
         gamma * gamma * sin_alpha;
}

/**
 * @brief Compute peak synchrotron frequency.
 *
 * The spectrum peaks at ν_peak ≈ 0.29 ν_c
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Peak frequency [Hz]
 */
inline double synchrotron_frequency_peak(double gamma, double B) {
  return 0.29 * synchrotron_frequency_critical(gamma, B);
}

/**
 * @brief Compute synchrotron power radiated by single electron.
 *
 * P = (4/3) σ_T c γ² β² U_B
 *
 * where U_B = B²/(8π) is magnetic energy density.
 * For ultrarelativistic electrons (β ≈ 1):
 * P = (4/3) σ_T c γ² (B²/8π)
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Power radiated [erg/s]
 */
inline double synchrotron_power_single_electron(double gamma, double B) {
  double U_B = B * B / (8.0 * PI); // Magnetic energy density
  double beta_sq = 1.0 - 1.0 / (gamma * gamma);
  return (4.0 / 3.0) * SIGMA_THOMSON * C * gamma * gamma * beta_sq * U_B;
}

/**
 * @brief Compute synchrotron cooling time.
 *
 * t_cool = E / P = γ m_e c² / P
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field strength [Gauss]
 * @return Cooling time [s]
 */
inline double synchrotron_cooling_time(double gamma, double B) {
  double P = synchrotron_power_single_electron(gamma, B);
  if (P < 1e-50) {
    return safe_infinity<double>();
  }
  return gamma * M_ELECTRON * C * C / P;
}

/**
 * @brief Compute cooling Lorentz factor at given time.
 *
 * Electrons above γ_cool have cooled significantly.
 * γ_cool = 6π m_e c / (σ_T B² t)
 *
 * @param B Magnetic field strength [Gauss]
 * @param t Time since injection [s]
 * @return Cooling Lorentz factor
 */
inline double synchrotron_cooling_lorentz_factor(double B, double t) {
  if (t < 1e-50 || std::abs(B) < 1e-30) {
    return safe_infinity<double>();
  }
  return 6.0 * PI * M_ELECTRON * C / (SIGMA_THOMSON * B * B * t);
}

// ============================================================================
// Synchrotron Spectrum Functions
// ============================================================================

/**
 * @brief Synchrotron function F(x) for single electron.
 *
 * F(x) = x ∫_x^∞ K_{5/3}(ξ) dξ
 *
 * where x = ν/ν_c and K is modified Bessel function.
 * Approximations used for numerical stability.
 *
 * @param x Dimensionless frequency ν/ν_c
 * @return F(x) synchrotron function value
 */
inline double synchrotron_F(double x) {
  if (x <= 0) return 0.0;

  // Asymptotic approximations
  if (x < 0.01) {
    // Low frequency: F(x) ≈ (4π/√3/Γ(1/3)) × (x/2)^(1/3)
    // Simplified: F(x) ≈ 1.8 × x^(1/3)
    return 1.8084 * std::pow(x, 1.0 / 3.0);
  } else if (x > 10) {
    // High frequency: F(x) ≈ √(π/2) × √x × exp(-x)
    return std::sqrt(PI / 2.0) * std::sqrt(x) * std::exp(-x);
  } else {
    // Intermediate: use polynomial fit (Fouka & Ouichaoui 2013)
    double ln_x = std::log(x);
    double F_approx = 1.8084 * std::pow(x, 1.0 / 3.0) *
                      std::exp(-x) *
                      (1.0 + 0.884 * std::pow(x, 2.0 / 3.0) +
                       0.471 * std::pow(x, 4.0 / 3.0));
    return F_approx;
  }
}

/**
 * @brief Synchrotron function G(x) for polarized emission.
 *
 * G(x) = x × K_{2/3}(x)
 *
 * Used for calculating polarization degree.
 *
 * @param x Dimensionless frequency ν/ν_c
 * @return G(x) function value
 */
inline double synchrotron_G(double x) {
  if (x <= 0) return 0.0;

  // Approximations for modified Bessel function K_{2/3}
  if (x < 0.01) {
    // K_{2/3}(x) ≈ Γ(2/3) × (2/x)^(2/3) / 2
    return 1.3541 * std::pow(x, 1.0 / 3.0);
  } else if (x > 10) {
    return std::sqrt(PI / 2.0) * std::sqrt(x) * std::exp(-x);
  } else {
    // Polynomial approximation
    return 1.3541 * std::pow(x, 1.0 / 3.0) * std::exp(-x) *
           (1.0 + 0.6 * std::pow(x, 2.0 / 3.0));
  }
}

/**
 * @brief Compute synchrotron polarization degree.
 *
 * Π = G(x) / F(x)
 *
 * For power-law electron distribution with index p:
 * Π_max = (p + 1) / (p + 7/3)
 *
 * @param x Dimensionless frequency ν/ν_c
 * @return Polarization degree (0 to 1)
 */
inline double synchrotron_polarization(double x) {
  double F = synchrotron_F(x);
  double G = synchrotron_G(x);
  if (F < 1e-50) return 0.0;
  return G / F;
}

// ============================================================================
// Power-Law Electron Distribution
// ============================================================================

/**
 * @brief Compute synchrotron spectrum from power-law electrons.
 *
 * For electron distribution N(γ) ∝ γ^(-p) between γ_min and γ_max,
 * the spectrum is F_ν ∝ ν^(-(p-1)/2) between break frequencies.
 *
 * @param nu Frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param gamma_min Minimum electron Lorentz factor
 * @param gamma_max Maximum electron Lorentz factor
 * @param p Power-law index (typically 2-3)
 * @return Relative spectral power (normalized)
 */
inline double synchrotron_spectrum_power_law(double nu, double B,
                                              double gamma_min, double gamma_max,
                                              double p) {
  // Characteristic frequencies
  double nu_min = synchrotron_frequency_critical(gamma_min, B);
  double nu_max = synchrotron_frequency_critical(gamma_max, B);

  if (nu <= 0) return 0.0;

  // Spectral index for optically thin synchrotron
  double alpha = -(p - 1.0) / 2.0;

  if (nu < nu_min) {
    // Below minimum: self-absorbed regime, F ∝ ν^(5/2)
    return std::pow(nu / nu_min, 2.5);
  } else if (nu < nu_max) {
    // Power-law regime
    return std::pow(nu / nu_min, alpha);
  } else {
    // Exponential cutoff above γ_max
    return std::pow(nu_max / nu_min, alpha) * std::exp(-(nu - nu_max) / nu_max);
  }
}

/**
 * @brief Compute spectral index for power-law electrons.
 *
 * α = -(p - 1)/2 where F_ν ∝ ν^α
 *
 * @param p Electron power-law index
 * @return Spectral index
 */
inline double synchrotron_spectral_index(double p) {
  return -(p - 1.0) / 2.0;
}

/**
 * @brief Compute electron index from spectral index.
 *
 * p = 1 - 2α
 *
 * @param alpha Spectral index
 * @return Electron power-law index
 */
inline double electron_index_from_spectral(double alpha) {
  return 1.0 - 2.0 * alpha;
}

// ============================================================================
// Self-Absorption
// ============================================================================

/**
 * @brief Compute synchrotron self-absorption coefficient.
 *
 * The absorption coefficient scales as:
 * α_ν ∝ ν^(-(p+4)/2) for power-law electrons
 *
 * Below the self-absorption frequency ν_a, the source becomes
 * optically thick and the spectrum changes to F_ν ∝ ν^(5/2).
 *
 * @param nu Frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param n_e Electron density [cm^-3]
 * @param gamma_min Minimum Lorentz factor
 * @param p Electron power-law index
 * @return Absorption coefficient [cm^-1]
 */
inline double synchrotron_absorption_coefficient(double nu, double B,
                                                  double n_e, double gamma_min,
                                                  double p) {
  // Simplified formula (order of magnitude)
  double nu_B = gyrofrequency(B);
  double prefactor = 0.02 * E_CHARGE * n_e / (M_ELECTRON * C);

  double exponent = -(p + 4.0) / 2.0;
  return prefactor * std::pow(nu_B, (p + 2.0) / 2.0) * std::pow(nu, exponent);
}

/**
 * @brief Compute self-absorption frequency.
 *
 * The frequency where τ_ν = 1 (optical depth unity).
 *
 * @param B Magnetic field [Gauss]
 * @param n_e Electron density [cm^-3]
 * @param R Source size [cm]
 * @param gamma_min Minimum Lorentz factor
 * @param p Electron power-law index
 * @return Self-absorption frequency [Hz]
 */
inline double synchrotron_self_absorption_frequency(double B, double n_e,
                                                     double R, double gamma_min,
                                                     double p) {
  // Approximation: ν_a where τ = α_ν × R = 1
  double nu_B = gyrofrequency(B);

  // Scaling: ν_a ∝ (n_e R)^(2/(p+4)) × B^((p+2)/(p+4))
  double exponent = 2.0 / (p + 4.0);
  return nu_B * std::pow(n_e * R / 1e20, exponent);
}

} // namespace physics

#endif // PHYSICS_SYNCHROTRON_H
