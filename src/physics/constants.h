/**
 * @file constants.h
 * @brief Physical constants for black hole and relativistic physics.
 *
 * All constants in CGS units unless otherwise noted.
 * Reference: CODATA 2022, IAU 2015 nominal solar values.
 *
 * Cleanroom implementation based on standard physics references.
 */

#ifndef PHYSICS_CONSTANTS_H
#define PHYSICS_CONSTANTS_H

#include <cmath>

namespace physics {

// ============================================================================
// Fundamental Constants (CGS)
// ============================================================================

/// Speed of light [cm/s]
inline constexpr double C = 2.99792458e10;

/// Speed of light squared [cm²/s²]
inline constexpr double C2 = C * C;

/// Gravitational constant [cm³/(g·s²)]
inline constexpr double G = 6.67430e-8;

/// Reduced Planck constant [erg·s]
inline constexpr double HBAR = 1.054571817e-27;

/// Boltzmann constant [erg/K]
inline constexpr double K_B = 1.380649e-16;

/// Stefan-Boltzmann constant [erg/(cm²·s·K⁴)]
inline constexpr double SIGMA_SB = 5.670374419e-5;

// ============================================================================
// Astronomical Constants (CGS)
// ============================================================================

/// Solar mass [g]
inline constexpr double M_SUN = 1.98841e33;

/// Solar radius [cm]
inline constexpr double R_SUN = 6.9634e10;

/// Solar luminosity [erg/s]
inline constexpr double L_SUN = 3.828e33;

/// Schwarzschild radius of 1 solar mass [cm]
/// r_s = 2GM/c² ≈ 2.95 km for 1 M_sun
inline constexpr double R_SCHW_SUN = 2.0 * G * M_SUN / C2;

/// Parsec [cm]
inline constexpr double PARSEC = 3.0856775814913673e18;

/// Megaparsec [cm]
inline constexpr double MPC = PARSEC * 1.0e6;

// ============================================================================
// Cosmological Constants
// ============================================================================

/// Hubble constant H0 [km/s/Mpc] (Planck 2018)
inline constexpr double H0_PLANCK = 67.4;

/// Matter density parameter Omega_m (Planck 2018)
inline constexpr double OMEGA_M_PLANCK = 0.315;

/// Dark energy density parameter Omega_Lambda (Planck 2018)
inline constexpr double OMEGA_LAMBDA_PLANCK = 1.0 - OMEGA_M_PLANCK;

// ============================================================================
// Mathematical Constants
// ============================================================================

/// Pi
inline constexpr double PI = 3.14159265358979323846;

/// 2*Pi
inline constexpr double TWO_PI = 2.0 * PI;

/// 4*Pi
inline constexpr double FOUR_PI = 4.0 * PI;

/// 4*Pi/3
inline constexpr double FOUR_PI_OVER_3 = FOUR_PI / 3.0;

// ============================================================================
// Derived Constants for Black Hole Physics
// ============================================================================

/// Gravitational radius scale factor: G/c²
inline constexpr double G_OVER_C2 = G / C2;

/// 2G/c² for Schwarzschild radius calculation
inline constexpr double TWO_G_OVER_C2 = 2.0 * G_OVER_C2;

/// 4G/c² for light deflection calculation
inline constexpr double FOUR_G_OVER_C2 = 4.0 * G_OVER_C2;

// ============================================================================
// Unit Conversion Helpers
// ============================================================================

/// Convert solar masses to grams
inline constexpr double solar_masses_to_g(double m_sun) {
  return m_sun * M_SUN;
}

/// Convert grams to solar masses
inline constexpr double g_to_solar_masses(double g) {
  return g / M_SUN;
}

/// Convert km to cm
inline constexpr double km_to_cm(double km) {
  return km * 1.0e5;
}

/// Convert cm to km
inline constexpr double cm_to_km(double cm) {
  return cm * 1.0e-5;
}

/// Convert Schwarzschild radii to cm (given mass in solar masses)
inline constexpr double r_s_to_cm(double r_s_units, double mass_solar) {
  return r_s_units * TWO_G_OVER_C2 * mass_solar * M_SUN;
}

} // namespace physics

#endif // PHYSICS_CONSTANTS_H
