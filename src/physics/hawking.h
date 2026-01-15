/**
 * @file hawking.h
 * @brief Hawking radiation and black hole thermodynamics.
 *
 * Hawking (1974) showed that black holes emit thermal radiation with
 * temperature inversely proportional to their mass. Combined with
 * Bekenstein's entropy formula, this establishes black hole thermodynamics.
 *
 * Key formulas:
 *   Temperature: T_H = ℏc³/(8πGMk_B)
 *   Luminosity: L_H = ℏc⁶/(15360πG²M²)
 *   Entropy: S_BH = k_B c³ A / (4Gℏ) = k_B A / (4 l_P²)
 *   Evaporation time: t_evap ≈ 5120πG²M³/(ℏc⁴)
 *
 * References:
 *   - Hawking (1974) "Black hole explosions?" Nature 248, 30
 *   - Bekenstein (1973) "Black Holes and Entropy" PRD 7, 2333
 *   - Page (1976) "Particle emission rates from a black hole"
 *
 * Cleanroom implementation based on standard formulas.
 */

#ifndef PHYSICS_HAWKING_H
#define PHYSICS_HAWKING_H

#include "constants.h"
#include "kerr.h"
#include "schwarzschild.h"
#include <algorithm>
#include <cmath>
#include <limits>

namespace physics {

// ============================================================================
// Planck Scale Constants
// ============================================================================

/// Planck mass m_P = √(ℏc/G) ≈ 2.176e-5 g
inline const double M_PLANCK = std::sqrt(HBAR * C / G);

/// Planck length l_P = √(ℏG/c³) ≈ 1.616e-33 cm
inline const double L_PLANCK = std::sqrt(HBAR * G / (C * C * C));

/// Planck time t_P = √(ℏG/c⁵) ≈ 5.391e-44 s
inline const double T_PLANCK = std::sqrt(HBAR * G / (C * C * C * C * C));

/// Planck temperature T_P = √(ℏc⁵/(Gk_B²)) ≈ 1.417e32 K
inline const double TEMP_PLANCK = std::sqrt(HBAR * C * C * C * C * C / (G * K_B * K_B));

// ============================================================================
// Hawking Temperature
// ============================================================================

/**
 * @brief Compute Hawking temperature for Schwarzschild black hole.
 *
 * T_H = ℏc³ / (8πGMk_B) = ℏc / (4π r_s k_B)
 *
 * For 1 solar mass: T_H ≈ 6.2 × 10^-8 K (extremely cold!)
 * Becomes significant only for M < ~10^15 g (asteroid mass)
 *
 * @param mass Black hole mass [g]
 * @return Hawking temperature [K]
 */
inline double hawking_temperature(double mass) {
  if (mass <= 0) {
    return std::numeric_limits<double>::infinity();
  }
  return HBAR * C * C * C / (8.0 * PI * G * mass * K_B);
}

/**
 * @brief Compute Hawking temperature for Kerr black hole.
 *
 * T_H = ℏ κ / (2π k_B c)
 *
 * where κ is the surface gravity at the horizon:
 * κ = (r_+ - r_-) / (2(r_+² + a²))
 *
 * For extremal Kerr (a* = 1), T_H = 0 (third law of BH thermodynamics).
 *
 * @param mass Black hole mass [g]
 * @param a_star Dimensionless spin
 * @return Hawking temperature [K]
 */
inline double hawking_temperature_kerr(double mass, double a_star) {
  a_star = std::clamp(std::abs(a_star), 0.0, 0.9999);

  double M = G * mass / C2;
  double sqrt_factor = std::sqrt(1.0 - a_star * a_star);
  double r_plus = M * (1.0 + sqrt_factor);
  double r_minus = M * (1.0 - sqrt_factor);
  double a = a_star * M;

  // Surface gravity
  double kappa = (r_plus - r_minus) / (2.0 * (r_plus * r_plus + a * a));

  // Convert from geometric to CGS units
  kappa *= C * C; // Now in cm/s²

  return HBAR * kappa / (TWO_PI * K_B * C);
}

// ============================================================================
// Hawking Luminosity and Evaporation
// ============================================================================

/**
 * @brief Compute Hawking luminosity (power radiated).
 *
 * L_H = σ_SB × A × T_H⁴ = ℏc⁶ / (15360 π G² M²)
 *
 * For Stefan-Boltzmann radiation from a sphere of radius r_s.
 *
 * @param mass Black hole mass [g]
 * @return Luminosity [erg/s]
 */
inline double hawking_luminosity(double mass) {
  if (mass <= 0) {
    return std::numeric_limits<double>::infinity();
  }
  // L = ℏc⁶ / (15360 π G² M²)
  return HBAR * std::pow(C, 6) / (15360.0 * PI * G * G * mass * mass);
}

/**
 * @brief Compute black hole evaporation time.
 *
 * t_evap = 5120 π G² M³ / (ℏ c⁴)
 *
 * For 1 solar mass: t_evap ~ 10^67 years
 * For M ~ 10^15 g: t_evap ~ age of universe
 *
 * @param mass Black hole mass [g]
 * @return Evaporation time [s]
 */
inline double hawking_evaporation_time(double mass) {
  if (mass <= 0) {
    return 0.0;
  }
  return 5120.0 * PI * G * G * mass * mass * mass / (HBAR * std::pow(C, 4));
}

/**
 * @brief Compute mass at which evaporation time equals given time.
 *
 * M = (ℏ c⁴ t / (5120 π G²))^(1/3)
 *
 * @param t Time [s]
 * @return Mass [g]
 */
inline double evaporating_mass(double t) {
  if (t <= 0) {
    return 0.0;
  }
  return std::cbrt(HBAR * std::pow(C, 4) * t / (5120.0 * PI * G * G));
}

/**
 * @brief Compute mass loss rate.
 *
 * dM/dt = -L_H / c² = -ℏc⁴ / (15360 π G² M²)
 *
 * @param mass Black hole mass [g]
 * @return Mass loss rate [g/s] (negative)
 */
inline double mass_loss_rate(double mass) {
  return -hawking_luminosity(mass) / (C * C);
}

// ============================================================================
// Hawking Spectrum
// ============================================================================

/**
 * @brief Compute peak wavelength of Hawking radiation.
 *
 * From Wien's displacement law:
 * λ_peak = b / T_H where b = 2.898 × 10^-3 m·K
 *
 * @param mass Black hole mass [g]
 * @return Peak wavelength [cm]
 */
inline double hawking_peak_wavelength(double mass) {
  double T = hawking_temperature(mass);
  if (T <= 0) {
    return std::numeric_limits<double>::infinity();
  }
  // Wien displacement constant in CGS
  constexpr double b_wien = 0.2898; // cm·K
  return b_wien / T;
}

/**
 * @brief Compute peak frequency of Hawking radiation.
 *
 * ν_peak ≈ 2.82 k_B T_H / h ≈ 5.88 × 10^10 T_H Hz
 *
 * @param mass Black hole mass [g]
 * @return Peak frequency [Hz]
 */
inline double hawking_peak_frequency(double mass) {
  double T = hawking_temperature(mass);
  // ν_peak = 2.821 k_B T / h
  return 2.821 * K_B * T / (TWO_PI * HBAR);
}

/**
 * @brief Compute Hawking radiation power spectrum.
 *
 * For a scalar field, the spectrum is approximately blackbody
 * modified by greybody factors:
 *
 * dE/dω dt = Γ(ω) × ℏω / (exp(ℏω/k_B T) - 1) × (dσ/dω)
 *
 * Simplified to blackbody here.
 *
 * @param nu Frequency [Hz]
 * @param mass Black hole mass [g]
 * @return Spectral power [erg/s/Hz]
 */
inline double hawking_spectrum(double nu, double mass) {
  double T = hawking_temperature(mass);
  if (T <= 0 || nu <= 0) return 0.0;

  double x = TWO_PI * HBAR * nu / (K_B * T);
  if (x > 700) return 0.0; // Avoid overflow

  // Planck distribution
  double r_s = schwarzschild_radius(mass);
  double area = 4.0 * PI * r_s * r_s;

  // B_ν = 2hν³/c² × 1/(exp(hν/kT) - 1)
  double B_nu = 2.0 * TWO_PI * HBAR * nu * nu * nu / (C * C) /
                (std::exp(x) - 1.0);

  return area * PI * B_nu;
}

// ============================================================================
// Bekenstein-Hawking Entropy
// ============================================================================

/**
 * @brief Compute Bekenstein-Hawking entropy.
 *
 * S_BH = k_B × A / (4 l_P²) = k_B c³ A / (4 G ℏ)
 *
 * where A = 4π r_s² is the horizon area.
 *
 * For 1 solar mass: S ~ 10^77 k_B (enormous!)
 *
 * @param mass Black hole mass [g]
 * @return Entropy [erg/K]
 */
inline double bekenstein_hawking_entropy(double mass) {
  double r_s = schwarzschild_radius(mass);
  double area = 4.0 * PI * r_s * r_s;
  return K_B * C * C * C * area / (4.0 * G * HBAR);
}

/**
 * @brief Compute entropy in natural units (A/4 in Planck units).
 *
 * S/k_B = A / (4 l_P²)
 *
 * @param mass Black hole mass [g]
 * @return Dimensionless entropy
 */
inline double entropy_dimensionless(double mass) {
  double r_s = schwarzschild_radius(mass);
  double area = 4.0 * PI * r_s * r_s;
  return area / (4.0 * L_PLANCK * L_PLANCK);
}

/**
 * @brief Compute Kerr black hole entropy.
 *
 * S = k_B × A / (4 l_P²)
 *
 * where A = 4π(r_+² + a²) for Kerr
 *
 * @param mass Black hole mass [g]
 * @param a_star Dimensionless spin
 * @return Entropy [erg/K]
 */
inline double bekenstein_hawking_entropy_kerr(double mass, double a_star) {
  a_star = std::clamp(std::abs(a_star), 0.0, 0.9999);

  double M = G * mass / C2;
  double sqrt_factor = std::sqrt(1.0 - a_star * a_star);
  double r_plus = M * (1.0 + sqrt_factor);
  double a = a_star * M;

  double area = 4.0 * PI * (r_plus * r_plus + a * a);
  return K_B * C * C * C * area / (4.0 * G * HBAR);
}

// ============================================================================
// Information Paradox Related
// ============================================================================

/**
 * @brief Compute Page time.
 *
 * The Page time is when roughly half the entropy has been radiated
 * and the entanglement entropy of radiation peaks.
 *
 * t_Page ≈ t_evap / 2^(2/3) ≈ 0.63 × t_evap
 *
 * After Page time, information should start coming out.
 *
 * @param mass Black hole mass [g]
 * @return Page time [s]
 */
inline double page_time(double mass) {
  return hawking_evaporation_time(mass) / std::pow(2.0, 2.0 / 3.0);
}

/**
 * @brief Compute scrambling time.
 *
 * The scrambling time is how long it takes for information
 * thrown into a black hole to become "scrambled":
 *
 * t_scr = (r_s/c) × ln(S/k_B) ≈ (r_s/c) × ln(A/l_P²)
 *
 * This is fast compared to Page time but slow compared to
 * light-crossing time.
 *
 * @param mass Black hole mass [g]
 * @return Scrambling time [s]
 */
inline double scrambling_time(double mass) {
  double r_s = schwarzschild_radius(mass);
  double S = entropy_dimensionless(mass);
  if (S <= 1) S = 1; // Avoid log of zero
  return (r_s / C) * std::log(S);
}

/**
 * @brief Check if black hole is "primordial" (evaporating now).
 *
 * A primordial black hole with evaporation time ~ age of universe
 * has mass ~ 5 × 10^14 g ~ 10^-19 M_sun.
 *
 * @param mass Black hole mass [g]
 * @return true if evaporation time is comparable to Hubble time
 */
inline bool is_primordial_evaporating(double mass) {
  double t_evap = hawking_evaporation_time(mass);
  constexpr double hubble_time = 4.35e17; // seconds (~13.8 Gyr)
  return t_evap < 10.0 * hubble_time && t_evap > 0.1 * hubble_time;
}

} // namespace physics

#endif // PHYSICS_HAWKING_H
