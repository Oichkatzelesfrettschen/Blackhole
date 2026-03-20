/**
 * @file hawking.h
 * @brief Hawking radiation and black hole thermodynamics.
 *
 * Hawking (1974) showed that black holes emit thermal radiation with
 * temperature inversely proportional to their mass. Combined with
 * Bekenstein's entropy formula, this establishes black hole thermodynamics.
 *
 * Key formulas:
 *   Temperature: T_H = hbar*c^3/(8*pi*G*M*k_B)
 *   Luminosity: L_H = hbar*c^6/(15360*pi*G^2*M^2)
 *   Entropy: S_BH = k_B*c^3*A / (4*G*hbar) = k_B*A / (4*l_P^2)
 *   Evaporation time: t_evap ~= 5120*pi*G^2*M^3/(hbar*c^4)
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
#include "safe_limits.h"
#include "schwarzschild.h"
#include <algorithm>
#include <cmath>

namespace physics {

// ============================================================================
// Planck Scale Constants
// ============================================================================

/// Planck mass m_P = sqrt(hbar*c/G) ~= 2.176e-5 g
inline const double M_PLANCK = std::sqrt((HBAR * C) / G);

/// Planck length l_P = sqrt(hbar*G/c^3) ~= 1.616e-33 cm
inline const double L_PLANCK = std::sqrt((HBAR * G) / (C * C * C));

/// Planck time t_P = sqrt(hbar*G/c^5) ~= 5.391e-44 s
inline const double T_PLANCK = std::sqrt((HBAR * G) / (C * C * C * C * C));

/// Planck temperature T_P = sqrt(hbar*c^5/(G*k_B^2)) ~= 1.417e32 K
inline const double TEMP_PLANCK = std::sqrt((HBAR * C * C * C * C * C) / (G * K_B * K_B));

// ============================================================================
// Hawking Temperature
// ============================================================================

/**
 * @brief Compute Hawking temperature for Schwarzschild black hole.
 *
 * T_H = hbar*c^3 / (8*pi*G*M*k_B) = hbar*c / (4*pi*r_s*k_B)
 *
 * For 1 solar mass: T_H ~= 6.2 x 10^-8 K (extremely cold!)
 * Becomes significant only for M < ~10^15 g (asteroid mass)
 *
 * @param mass Black hole mass [g]
 * @return Hawking temperature [K]
 */
[[nodiscard]] inline double hawkingTemperature(double mass) {
  if (mass <= 0) { return safeInfinity<double>(); }
  return (HBAR * C * C * C) / (8.0 * PI * G * mass * K_B);
}

/**
 * @brief Compute Hawking temperature for Kerr black hole.
 *
 * T_H = hbar * kappa / (2*pi*k_B*c)
 *
 * where kappa is the surface gravity at the horizon:
 * kappa = (r+ - r-) / (2*(r+^2 + a^2))
 *
 * For extremal Kerr (a* = 1), T_H = 0 (third law of BH thermodynamics).
 *
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin
 * @return Hawking temperature [K]
 */
[[nodiscard]] inline double hawkingTemperatureKerr(double mass, double aStar) {
  const double aStarC = std::clamp(std::abs(aStar), 0.0, 0.9999);

  const double mGeo       = (G * mass) / C2;
  const double sqrtFactor = std::sqrt(1.0 - (aStarC * aStarC));
  const double rPlus  = mGeo * (1.0 + sqrtFactor);
  const double rMinus = mGeo * (1.0 - sqrtFactor);
  const double aSpin  = aStarC * mGeo;

  // Surface gravity
  double kappa = (rPlus - rMinus) / (2.0 * ((rPlus * rPlus) + (aSpin * aSpin)));

  // Convert from geometric to CGS units
  kappa *= C * C; // Now in cm/s^2

  return (HBAR * kappa) / (TWO_PI * K_B * C);
}

// ============================================================================
// Hawking Luminosity and Evaporation
// ============================================================================

/**
 * @brief Compute Hawking luminosity (power radiated).
 *
 * L_H = sigma_SB * A * T_H^4 = hbar*c^6 / (15360*pi*G^2*M^2)
 *
 * For Stefan-Boltzmann radiation from a sphere of radius r_s.
 *
 * @param mass Black hole mass [g]
 * @return Luminosity [erg/s]
 */
[[nodiscard]] inline double hawkingLuminosity(double mass) {
  if (mass <= 0) { return safeInfinity<double>(); }
  return (HBAR * std::pow(C, 6)) / (15360.0 * PI * G * G * mass * mass);
}

/**
 * @brief Compute black hole evaporation time.
 *
 * t_evap = 5120*pi*G^2*M^3 / (hbar*c^4)
 *
 * For 1 solar mass: t_evap ~ 10^67 years
 * For M ~ 10^15 g: t_evap ~ age of universe
 *
 * @param mass Black hole mass [g]
 * @return Evaporation time [s]
 */
[[nodiscard]] inline double hawkingEvaporationTime(double mass) {
  if (mass <= 0) { return 0.0; }
  return (5120.0 * PI * G * G * mass * mass * mass) / (HBAR * std::pow(C, 4));
}

/**
 * @brief Compute mass at which evaporation time equals given time.
 *
 * M = (hbar*c^4*t / (5120*pi*G^2))^(1/3)
 *
 * @param t Time [s]
 * @return Mass [g]
 */
[[nodiscard]] inline double evaporatingMass(double t) {
  if (t <= 0) { return 0.0; }
  return std::cbrt((HBAR * std::pow(C, 4) * t) / (5120.0 * PI * G * G));
}

/**
 * @brief Compute mass loss rate.
 *
 * dM/dt = -L_H / c^2 = -hbar*c^4 / (15360*pi*G^2*M^2)
 *
 * @param mass Black hole mass [g]
 * @return Mass loss rate [g/s] (negative)
 */
[[nodiscard]] inline double massLossRate(double mass) {
  return -hawkingLuminosity(mass) / (C * C);
}

// ============================================================================
// Hawking Spectrum
// ============================================================================

/**
 * @brief Compute peak wavelength of Hawking radiation.
 *
 * From Wien's displacement law:
 * lambda_peak = b / T_H where b = 2.898e-3 m*K
 *
 * @param mass Black hole mass [g]
 * @return Peak wavelength [cm]
 */
[[nodiscard]] inline double hawkingPeakWavelength(double mass) {
  const double tempK = hawkingTemperature(mass);
  if ((tempK <= 0) || isEffectivelyInfinite(tempK)) {
    return safeInfinity<double>();
  }
  // Wien displacement constant in CGS
  constexpr double bWien = 0.2898; // cm*K
  return bWien / tempK;
}

/**
 * @brief Compute peak frequency of Hawking radiation.
 *
 * nu_peak ~= 2.82 k_B T_H / h ~= 5.88e10 T_H Hz
 *
 * @param mass Black hole mass [g]
 * @return Peak frequency [Hz]
 */
[[nodiscard]] inline double hawkingPeakFrequency(double mass) {
  const double tempK = hawkingTemperature(mass);
  return (2.821 * K_B * tempK) / (TWO_PI * HBAR);
}

/**
 * @brief Compute Hawking radiation power spectrum.
 *
 * For a scalar field, the spectrum is approximately blackbody
 * modified by greybody factors:
 *
 * dE/(domega dt) = Gamma(omega) * hbar*omega / (exp(hbar*omega/k_B*T) - 1) * dsigma/domega
 *
 * Simplified to blackbody here.
 *
 * @param nu Frequency [Hz]
 * @param mass Black hole mass [g]
 * @return Spectral power [erg/s/Hz]
 */
[[nodiscard]] inline double hawkingSpectrum(double nu, double mass) {
  const double tempK = hawkingTemperature(mass);
  if ((tempK <= 0) || (nu <= 0)) { return 0.0; }

  const double x = (TWO_PI * HBAR * nu) / (K_B * tempK);
  if (x > 700) { return 0.0; } // Avoid overflow

  // Planck distribution
  const double rS   = schwarzschildRadius(mass);
  const double area = 4.0 * PI * rS * rS;

  // B_nu = 2*h*nu^3/c^2 * 1/(exp(h*nu/k*T) - 1)
  const double bNu = (2.0 * TWO_PI * HBAR * nu * nu * nu) /
                     ((C * C) * (std::exp(x) - 1.0));

  return area * PI * bNu;
}

// ============================================================================
// Bekenstein-Hawking Entropy
// ============================================================================

/**
 * @brief Compute Bekenstein-Hawking entropy.
 *
 * S_BH = k_B * A / (4*l_P^2) = k_B*c^3*A / (4*G*hbar)
 *
 * where A = 4*pi*r_s^2 is the horizon area.
 *
 * For 1 solar mass: S ~ 10^77 k_B (enormous!)
 *
 * @param mass Black hole mass [g]
 * @return Entropy [erg/K]
 */
[[nodiscard]] inline double bekensteinHawkingEntropy(double mass) {
  const double rS   = schwarzschildRadius(mass);
  const double area = 4.0 * PI * rS * rS;
  return (K_B * C * C * C * area) / (4.0 * G * HBAR);
}

/**
 * @brief Compute entropy in natural units (A/4 in Planck units).
 *
 * S/k_B = A / (4*l_P^2)
 *
 * @param mass Black hole mass [g]
 * @return Dimensionless entropy
 */
[[nodiscard]] inline double entropyDimensionless(double mass) {
  const double rS   = schwarzschildRadius(mass);
  const double area = 4.0 * PI * rS * rS;
  return area / (4.0 * L_PLANCK * L_PLANCK);
}

/**
 * @brief Compute Kerr black hole entropy.
 *
 * S = k_B * A / (4*l_P^2)
 *
 * where A = 4*pi*(r+^2 + a^2) for Kerr
 *
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin
 * @return Entropy [erg/K]
 */
[[nodiscard]] inline double bekensteinHawkingEntropyKerr(double mass, double aStar) {
  const double aStarC     = std::clamp(std::abs(aStar), 0.0, 0.9999);
  const double mGeo       = (G * mass) / C2;
  const double sqrtFactor = std::sqrt(1.0 - (aStarC * aStarC));
  const double rPlus      = mGeo * (1.0 + sqrtFactor);
  const double aSpin      = aStarC * mGeo;

  const double area = 4.0 * PI * ((rPlus * rPlus) + (aSpin * aSpin));
  return (K_B * C * C * C * area) / (4.0 * G * HBAR);
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
 * t_Page ~= t_evap / 2^(2/3) ~= 0.63 * t_evap
 *
 * After Page time, information should start coming out.
 *
 * @param mass Black hole mass [g]
 * @return Page time [s]
 */
[[nodiscard]] inline double pageTime(double mass) {
  return hawkingEvaporationTime(mass) / std::pow(2.0, 2.0 / 3.0);
}

/**
 * @brief Compute scrambling time.
 *
 * The scrambling time is how long it takes for information
 * thrown into a black hole to become "scrambled":
 *
 * t_scr = (r_s/c) * ln(S/k_B) ~= (r_s/c) * ln(A/l_P^2)
 *
 * This is fast compared to Page time but slow compared to
 * light-crossing time.
 *
 * @param mass Black hole mass [g]
 * @return Scrambling time [s]
 */
[[nodiscard]] inline double scramblingTime(double mass) {
  const double rS = schwarzschildRadius(mass);
  const double sVal = std::max(entropyDimensionless(mass), 1.0); // Avoid log of zero
  return (rS / C) * std::log(sVal);
}

/**
 * @brief Check if black hole is "primordial" (evaporating now).
 *
 * A primordial black hole with evaporation time ~ age of universe
 * has mass ~ 5 x 10^14 g ~ 10^-19 M_sun.
 *
 * @param mass Black hole mass [g]
 * @return true if evaporation time is comparable to Hubble time
 */
[[nodiscard]] inline bool isPrimordialEvaporating(double mass) {
  const double tEvap = hawkingEvaporationTime(mass);
  constexpr double hubbleTime = 4.35e17; // seconds (~13.8 Gyr)
  return (tEvap < (10.0 * hubbleTime)) && (tEvap > (0.1 * hubbleTime));
}

} // namespace physics

#endif // PHYSICS_HAWKING_H
