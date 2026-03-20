/**
 * @file unit_system.h
 * @brief Unit system documentation and conversion utilities.
 *
 * WHY: The codebase uses multiple unit systems across different modules:
 *   - CGS (constants.h, synchrotron.h, hawking.h): electromagnetic + thermal
 *   - Geometric (kerr.h metric functions, geodesics): G = c = 1
 *   - Code units (GRMHD snapshots): rho_0 = c = GM/c^2 = 1
 *
 * Without explicit documentation and conversion utilities, unit
 * inconsistencies can silently corrupt physics results. This file:
 *   1. Documents which modules use which unit system
 *   2. Provides conversion factors between systems
 *   3. Enables dimensional analysis at compile time (future: std::units)
 *
 * WHAT: Conversion functions between CGS, geometric, and code units.
 * All existing physics modules remain unchanged; this file adds the
 * missing bridge between them.
 *
 * HOW: Include this header when converting between unit systems.
 * Each conversion function is named: <source>_to_<target>_<quantity>.
 *
 * MODULE UNIT AUDIT (as of 2026-03-19):
 *
 *   CGS (c = 3e10 cm/s, G = 6.67e-8 cgs):
 *     - constants.h: all fundamental constants
 *     - synchrotron.h: emissivities, absorption coefficients
 *     - hawking.h: Hawking temperature, luminosity
 *     - novikov_thorne.h: disk flux, temperature profiles
 *     - doppler.h: Doppler shift factors
 *     - electron_temperature.h: thermal synchrotron
 *     - fits_writer.h: WCS pixel scales in degrees
 *
 *   Geometric (G = c = 1, length in units of M):
 *     - kerr.h: metric functions (Sigma, Delta, horizons, ISCO)
 *       Note: some functions take mass in grams and convert internally
 *     - coordinates.h: BL/MKS/KS transformations
 *     - connection.h: Christoffel symbols
 *     - verified/rk4.h: geodesic integrator state vectors
 *     - event_detection.h: crossing detectors
 *     - conservation_monitor.h: E, L, Q computation
 *     - johannsen_psaltis.h: JP metric deviations
 *
 *   Code units (GRMHD, dimensionless):
 *     - grmhd_streaming.h: tile data (density, pressure, B-field)
 *     - mad_disk.h: MAD disk model
 *     - Shaders (GLSL): all computations in dimensionless units
 *
 *   Mixed / Needs attention:
 *     - gravitational_waves.h: chirp mass in SOLAR MASSES, frequency in Hz
 *     - cosmology.h: H0 in km/s/Mpc, distances in Mpc
 *     - source_presets.h: mass in Msun, distance in cm
 */

#ifndef PHYSICS_UNIT_SYSTEM_H
#define PHYSICS_UNIT_SYSTEM_H

#include "constants.h"
#include <cmath>

namespace physics {
namespace units {

// ============================================================================
// CGS <-> Geometric Unit Conversions
// ============================================================================

/**
 * @brief Convert mass from grams to geometric units (length).
 *
 * M_geom = G * M_cgs / c^2  [cm]
 *
 * @param mass_g Mass in grams
 * @return Geometric mass [cm]
 */
inline constexpr double mass_cgs_to_geom(double mass_g) {
  return G * mass_g / C2;
}

/**
 * @brief Convert mass from geometric units back to grams.
 *
 * @param M_geom Geometric mass [cm]
 * @return Mass in grams
 */
inline constexpr double mass_geom_to_cgs(double M_geom) {
  return M_geom * C2 / G;
}

/**
 * @brief Convert mass from solar masses to geometric units.
 *
 * @param mass_msun Mass in solar masses
 * @return Geometric mass [cm]
 */
inline constexpr double mass_msun_to_geom(double mass_msun) {
  return G * mass_msun * M_SUN / C2;
}

/**
 * @brief Convert time from seconds to geometric units.
 *
 * t_geom = c * t_cgs  [cm]
 *
 * @param t_s Time in seconds
 * @return Time in geometric units [cm]
 */
inline constexpr double time_cgs_to_geom(double t_s) {
  return C * t_s;
}

/**
 * @brief Convert time from geometric units to seconds.
 */
inline constexpr double time_geom_to_cgs(double t_geom) {
  return t_geom / C;
}

/**
 * @brief Gravitational radius r_g = GM/c^2.
 *
 * @param mass_msun Mass in solar masses
 * @return r_g [cm]
 */
inline constexpr double r_g(double mass_msun) {
  return G * mass_msun * M_SUN / C2;
}

/**
 * @brief Schwarzschild radius r_s = 2GM/c^2.
 *
 * @param mass_msun Mass in solar masses
 * @return r_s [cm]
 */
inline constexpr double r_s(double mass_msun) {
  return 2.0 * G * mass_msun * M_SUN / C2;
}

// ============================================================================
// GRMHD Code Unit Conversions
// ============================================================================

/**
 * @brief Convert GRMHD code density to CGS.
 *
 * rho_cgs = rho_code * rho_unit
 * where rho_unit = M_dot / (4 * pi * r_g^2 * c) in typical scaling
 *
 * The actual scale factor depends on the mass accretion rate M_dot,
 * which is a free parameter set to match observed flux.
 *
 * @param rho_code Code density (dimensionless)
 * @param rho_unit Density scale factor [g/cm^3]
 * @return Density in CGS [g/cm^3]
 */
inline double density_code_to_cgs(double rho_code, double rho_unit) {
  return rho_code * rho_unit;
}

/**
 * @brief Convert GRMHD code magnetic field to CGS (Gauss).
 *
 * B_cgs = B_code * B_unit
 * where B_unit = c * sqrt(4 * pi * rho_unit)
 *
 * @param B_code Code magnetic field (dimensionless)
 * @param rho_unit Density scale factor [g/cm^3]
 * @return Magnetic field in Gauss
 */
inline double B_code_to_cgs(double B_code, double rho_unit) {
  double B_unit = C * std::sqrt(FOUR_PI * rho_unit);
  return B_code * B_unit;
}

/**
 * @brief Compute GRMHD density unit from mass accretion rate.
 *
 * rho_unit = M_dot / (4 * pi * r_g^2 * c)
 *
 * @param M_dot Mass accretion rate [g/s]
 * @param mass_msun Black hole mass [solar masses]
 * @return Density unit [g/cm^3]
 */
inline double rho_unit_from_mdot(double M_dot, double mass_msun) {
  double rg = r_g(mass_msun);
  return M_dot / (FOUR_PI * rg * rg * C);
}

// ============================================================================
// Angular Size Conversions
// ============================================================================

/**
 * @brief Convert physical size to angular size.
 *
 * @param size_cm Physical size [cm]
 * @param distance_cm Distance [cm]
 * @return Angular size [radians]
 */
inline double size_to_angle_rad(double size_cm, double distance_cm) {
  return size_cm / distance_cm;
}

/**
 * @brief Convert angular size to microarcseconds.
 *
 * @param angle_rad Angle in radians
 * @return Angle in microarcseconds
 */
inline constexpr double rad_to_uas(double angle_rad) {
  return angle_rad * 206265.0e6; // 1 rad = 206265 arcsec = 206265e6 uas
}

/**
 * @brief Convert microarcseconds to radians.
 */
inline constexpr double uas_to_rad(double uas) {
  return uas / 206265.0e6;
}

} // namespace units
} // namespace physics

#endif // PHYSICS_UNIT_SYSTEM_H
