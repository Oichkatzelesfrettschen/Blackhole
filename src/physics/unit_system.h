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

#include <cmath>

#include "constants.h"

namespace physics::units {

// ============================================================================
// CGS <-> Geometric Unit Conversions
// ============================================================================

/**
 * @brief Convert mass from grams to geometric units (length).
 *
 * M_geom = G * M_cgs / c^2  [cm]
 *
 * @param massG Mass in grams
 * @return Geometric mass [cm]
 */
[[nodiscard]] constexpr double massCgsToGeom(double massG) {
  return (G * massG) / C2;
}

/**
 * @brief Convert mass from geometric units back to grams.
 *
 * @param mGeom Geometric mass [cm]
 * @return Mass in grams
 */
[[nodiscard]] constexpr double massGeomToCgs(double mGeom) {
  return (mGeom * C2) / G;
}

/**
 * @brief Convert mass from solar masses to geometric units.
 *
 * @param massMsun Mass in solar masses
 * @return Geometric mass [cm]
 */
[[nodiscard]] constexpr double massMsunToGeom(double massMsun) {
  return (G * massMsun * M_SUN) / C2;
}

/**
 * @brief Convert time from seconds to geometric units.
 *
 * t_geom = c * t_cgs  [cm]
 *
 * @param tS Time in seconds
 * @return Time in geometric units [cm]
 */
[[nodiscard]] constexpr double timeCgsToGeom(double tS) {
  return C * tS;
}

/**
 * @brief Convert time from geometric units to seconds.
 *
 * @param tGeom Time in geometric units [cm]
 * @return Time in seconds
 */
[[nodiscard]] constexpr double timeGeomToCgs(double tGeom) {
  return tGeom / C;
}

/**
 * @brief Gravitational radius r_g = GM/c^2.
 *
 * @param massMsun Mass in solar masses
 * @return r_g [cm]
 */
[[nodiscard]] constexpr double rG(double massMsun) {
  return (G * massMsun * M_SUN) / C2;
}

/**
 * @brief Schwarzschild radius r_s = 2GM/c^2.
 *
 * @param massMsun Mass in solar masses
 * @return r_s [cm]
 */
[[nodiscard]] constexpr double rS(double massMsun) {
  return (2.0 * G * massMsun * M_SUN) / C2;
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
 * @param rhoCode Code density (dimensionless)
 * @param rhoUnit Density scale factor [g/cm^3]
 * @return Density in CGS [g/cm^3]
 */
[[nodiscard]] inline double densityCodeToCgs(double rhoCode, double rhoUnit) {
  return rhoCode * rhoUnit;
}

/**
 * @brief Convert GRMHD code magnetic field to CGS (Gauss).
 *
 * B_cgs = B_code * B_unit
 * where B_unit = c * sqrt(4 * pi * rho_unit)
 *
 * @param bCode Code magnetic field (dimensionless)
 * @param rhoUnit Density scale factor [g/cm^3]
 * @return Magnetic field in Gauss
 */
[[nodiscard]] inline double bCodeToCgs(double bCode, double rhoUnit) {
  const double bUnit = C * std::sqrt(FOUR_PI * rhoUnit);
  return bCode * bUnit;
}

/**
 * @brief Compute GRMHD density unit from mass accretion rate.
 *
 * rho_unit = M_dot / (4 * pi * r_g^2 * c)
 *
 * @param mDot Mass accretion rate [g/s]
 * @param massMsun Black hole mass [solar masses]
 * @return Density unit [g/cm^3]
 */
[[nodiscard]] inline double rhoUnitFromMdot(double mDot, double massMsun) {
  const double rg = rG(massMsun);
  return mDot / (FOUR_PI * rg * rg * C);
}

// ============================================================================
// Angular Size Conversions
// ============================================================================

/**
 * @brief Convert physical size to angular size.
 *
 * @param sizeCm Physical size [cm]
 * @param distanceCm Distance [cm]
 * @return Angular size [radians]
 */
[[nodiscard]] inline double sizeToAngleRad(double sizeCm, double distanceCm) {
  return sizeCm / distanceCm;
}

/**
 * @brief Convert angular size to microarcseconds.
 *
 * @param angleRad Angle in radians
 * @return Angle in microarcseconds
 */
[[nodiscard]] constexpr double radToUas(double angleRad) {
  return angleRad * 206265.0e6; // 1 rad = 206265 arcsec = 206265e6 uas
}

/**
 * @brief Convert microarcseconds to radians.
 *
 * @param uas Angle in microarcseconds
 * @return Angle in radians
 */
[[nodiscard]] constexpr double uasToRad(double uas) {
  return uas / 206265.0e6;
}

} // namespace physics::units

#endif // PHYSICS_UNIT_SYSTEM_H
