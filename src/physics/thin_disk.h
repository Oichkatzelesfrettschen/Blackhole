/**
 * @file thin_disk.h
 * @brief Novikov-Thorne thin accretion disk model.
 *
 * The Novikov-Thorne (1973) model describes a geometrically thin,
 * optically thick accretion disk in the equatorial plane.
 *
 * Key assumptions:
 * - Disk is geometrically thin: H/r << 1
 * - Gas follows circular Keplerian orbits
 * - Viscous torque transports angular momentum outward
 * - Energy is radiated locally as blackbody
 * - Inner edge at ISCO (zero-torque boundary)
 *
 * Radiative flux (Page & Thorne 1974):
 *   F(r) = (3 G M Ṁ)/(8π r³) * (1 - √(r_ISCO/r)) * f(r)
 *
 * where f(r) contains relativistic corrections.
 *
 * Temperature profile:
 *   T(r) = [F(r) / σ]^(1/4)
 *
 * Radiative efficiency:
 *   η = 1 - E_ISCO/c² ≈ 0.057 (Schwarzschild) to 0.42 (maximal Kerr)
 *
 * References:
 * - Novikov & Thorne (1973), in "Black Holes"
 * - Page & Thorne (1974), ApJ 191, 499
 * - Shakura & Sunyaev (1973), A&A 24, 337
 *
 * Cleanroom implementation based on standard formulas.
 */

#ifndef PHYSICS_THIN_DISK_H
#define PHYSICS_THIN_DISK_H

#include "constants.h"
#include "kerr.h"
#include "schwarzschild.h"
#include <algorithm>
#include <cmath>
#include <functional>
#include <vector>

namespace physics {

// ============================================================================
// Physical Constants for Disk Physics
// ============================================================================

/// Stefan-Boltzmann constant [erg/(cm² s K⁴)]
constexpr double STEFAN_BOLTZMANN = 5.670374419e-5;

/// Radiation constant a = 4σ/c [erg/(cm³ K⁴)]
constexpr double RADIATION_CONSTANT = 4.0 * STEFAN_BOLTZMANN / C;

// ============================================================================
// Disk Parameters
// ============================================================================

/**
 * @brief Parameters for a thin accretion disk.
 */
struct DiskParams {
  double M;           ///< Black hole mass [g]
  double M_dot;       ///< Accretion rate [g/s]
  double a;           ///< Spin parameter [cm] (0 for Schwarzschild)
  double r_in;        ///< Inner radius [cm] (typically ISCO)
  double r_out;       ///< Outer radius [cm]
  double inclination; ///< Viewing inclination [rad]
};

/**
 * @brief Create disk parameters for Schwarzschild black hole.
 *
 * @param M_solar Black hole mass in solar masses
 * @param M_dot_edd Accretion rate in Eddington units
 * @param r_out_rg Outer radius in gravitational radii
 * @return DiskParams
 */
inline DiskParams schwarzschild_disk(double M_solar, double M_dot_edd = 0.1,
                                     double r_out_rg = 1000.0) {
  DiskParams disk;
  disk.M = M_solar * M_SUN;
  disk.a = 0.0;

  // Eddington luminosity: L_Edd = 4π G M m_p c / σ_T
  double L_edd = 1.26e38 * M_solar; // erg/s

  // Eddington accretion rate (assuming η = 0.1)
  double M_dot_edd_cgs = L_edd / (0.1 * C2);
  disk.M_dot = M_dot_edd * M_dot_edd_cgs;

  // Radii in cm
  double r_g = G * disk.M / C2;
  disk.r_in = 6.0 * r_g; // ISCO for Schwarzschild
  disk.r_out = r_out_rg * r_g;
  disk.inclination = 0.0;

  return disk;
}

/**
 * @brief Create disk parameters for Kerr black hole.
 *
 * @param M_solar Black hole mass in solar masses
 * @param a_star Dimensionless spin (-1 to 1)
 * @param M_dot_edd Accretion rate in Eddington units
 * @param prograde True for prograde disk
 * @return DiskParams
 */
inline DiskParams kerr_disk(double M_solar, double a_star,
                            double M_dot_edd = 0.1, bool prograde = true) {
  DiskParams disk;
  disk.M = M_solar * M_SUN;

  // Spin parameter
  double M_geo = G * disk.M / C2;
  disk.a = a_star * M_geo;

  // Eddington rate
  double L_edd = 1.26e38 * M_solar;
  double eta = 1.0 - std::sqrt(1.0 - 2.0 / 3.0); // Approximate
  if (std::abs(a_star) > 0.9) {
    eta = 0.3; // Higher for high spin
  }
  disk.M_dot = M_dot_edd * L_edd / (eta * C2);

  // ISCO
  disk.r_in = kerr_isco_radius(disk.M, disk.a, prograde);
  disk.r_out = 1000.0 * M_geo;
  disk.inclination = 0.0;

  return disk;
}

// ============================================================================
// Novikov-Thorne Functions
// ============================================================================

/**
 * @brief Compute specific energy at radius r (Schwarzschild).
 *
 * E/c² = (1 - 2M/r) / √(1 - 3M/r)
 *
 * @param r Radius [cm]
 * @param M Black hole mass [g]
 * @return Specific energy (dimensionless, per unit rest mass)
 */
inline double specific_energy_schwarzschild(double r, double M) {
  double r_g = G * M / C2;
  double x = r_g / r;

  if (r <= 3.0 * r_g) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  double numerator = 1.0 - 2.0 * x;
  double denominator = std::sqrt(1.0 - 3.0 * x);

  return numerator / denominator;
}

/**
 * @brief Compute specific angular momentum at radius r (Schwarzschild).
 *
 * L/(Mc) = √(Mr) / √(1 - 3M/r)
 *
 * @param r Radius [cm]
 * @param M Black hole mass [g]
 * @return Specific angular momentum / (Mc)
 */
inline double specific_angular_momentum_schwarzschild(double r, double M) {
  double r_g = G * M / C2;
  double x = r_g / r;

  if (r <= 3.0 * r_g) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  return std::sqrt(r_g * r) / std::sqrt(1.0 - 3.0 * x);
}

/**
 * @brief Compute angular velocity at radius r (Schwarzschild).
 *
 * Ω = √(GM/r³)
 *
 * @param r Radius [cm]
 * @param M Black hole mass [g]
 * @return Angular velocity [rad/s]
 */
inline double angular_velocity_schwarzschild(double r, double M) {
  return std::sqrt(G * M / (r * r * r));
}

/**
 * @brief Compute relativistic correction factor for flux.
 *
 * The Novikov-Thorne flux involves an integral:
 * f(r) = ∫[r_in to r] (L - L_in) dE/dr dr / (Ω(E - Ω L))
 *
 * For Schwarzschild, this has a closed-form solution.
 *
 * @param r Radius [cm]
 * @param r_in Inner radius [cm]
 * @param M Black hole mass [g]
 * @return Correction factor (dimensionless)
 */
inline double novikov_thorne_factor_schwarzschild(double r, double r_in, double M) {
  double r_g = G * M / C2;

  // Dimensionless radii
  double x = std::sqrt(r / r_g);
  double x_in = std::sqrt(r_in / r_g);

  // Page & Thorne (1974) formula
  // Simplified version for computational stability:
  // Leading term: 1 - √(r_in/r)
  double term1 = 1.0 - std::sqrt(r_in / r);

  // First relativistic correction
  double term2 = (3.0 / (2.0 * x * x)) * std::log(x / x_in);

  // Higher-order terms (simplified)
  double term3 = -(3.0 * (x - x_in)) / (x * x * x_in);

  return term1 - term2 + term3;
}

/**
 * @brief Compute radiative flux from disk surface.
 *
 * F(r) = (3 G M Ṁ)/(8π r³) * f(r)
 *
 * where f(r) is the relativistic correction.
 *
 * @param r Radius [cm]
 * @param disk Disk parameters
 * @return Radiative flux [erg/(cm² s)]
 */
inline double disk_flux(double r, const DiskParams &disk) {
  if (r < disk.r_in || r > disk.r_out) {
    return 0.0;
  }

  // Leading coefficient
  double prefactor = 3.0 * G * disk.M * disk.M_dot / (8.0 * M_PI * r * r * r);

  // Relativistic correction
  double f_r;
  if (std::abs(disk.a) < 1e-10) {
    // Schwarzschild
    f_r = novikov_thorne_factor_schwarzschild(r, disk.r_in, disk.M);
  } else {
    // Kerr - simplified approximation
    // Full formula requires numerical integration
    double r_g = G * disk.M / C2;
    double basic = 1.0 - std::sqrt(disk.r_in / r);

    // Spin correction (approximate)
    double a_star = disk.a / r_g;
    double spin_factor = 1.0 + 0.5 * a_star * std::sqrt(r_g / r);

    f_r = basic * spin_factor;
  }

  return prefactor * f_r;
}

/**
 * @brief Compute disk temperature from flux.
 *
 * T(r) = [F(r) / σ]^(1/4)
 *
 * @param flux Radiative flux [erg/(cm² s)]
 * @return Temperature [K]
 */
inline double disk_temperature_from_flux(double flux) {
  if (flux <= 0) return 0.0;
  return std::pow(flux / STEFAN_BOLTZMANN, 0.25);
}

/**
 * @brief Compute disk temperature at radius r.
 *
 * @param r Radius [cm]
 * @param disk Disk parameters
 * @return Temperature [K]
 */
inline double disk_temperature(double r, const DiskParams &disk) {
  double flux = disk_flux(r, disk);
  return disk_temperature_from_flux(flux);
}

/**
 * @brief Compute peak temperature and its radius.
 *
 * For Schwarzschild: T_max at r ≈ 49/12 * r_ISCO
 *
 * @param disk Disk parameters
 * @param T_max Output: peak temperature [K]
 * @param r_peak Output: radius of peak [cm]
 */
inline void disk_peak_temperature(const DiskParams &disk,
                                  double &T_max, double &r_peak) {
  // Peak is roughly at (49/12) * r_ISCO for Schwarzschild
  r_peak = (49.0 / 12.0) * disk.r_in;

  // Ensure within disk bounds
  if (r_peak > disk.r_out) {
    r_peak = disk.r_out;
  }

  T_max = disk_temperature(r_peak, disk);
}

// ============================================================================
// Disk Spectrum
// ============================================================================

/**
 * @brief Compute Planck function at temperature T.
 *
 * B_ν(T) = (2h ν³/c²) / (exp(hν/kT) - 1)
 *
 * @param nu Frequency [Hz]
 * @param T Temperature [K]
 * @return Specific intensity [erg/(s cm² Hz sr)]
 */
inline double planck_function(double nu, double T) {
  if (T <= 0 || nu <= 0) return 0.0;

  double h = 6.62607015e-27;  // Planck constant [erg s]
  double k_B = K_B;

  double x = h * nu / (k_B * T);

  // Avoid overflow
  if (x > 700) return 0.0;

  double prefactor = 2.0 * h * nu * nu * nu / (C * C);
  return prefactor / (std::exp(x) - 1.0);
}

/**
 * @brief Compute disk spectrum at frequency ν.
 *
 * Integrates blackbody emission over the disk:
 * L_ν = 4π cos(i) ∫ B_ν(T(r)) 2πr dr
 *
 * @param nu Frequency [Hz]
 * @param disk Disk parameters
 * @param n_points Number of integration points
 * @return Specific luminosity [erg/(s Hz)]
 */
inline double disk_spectrum(double nu, const DiskParams &disk,
                            int n_points = 100) {
  double sum = 0.0;
  double log_r_in = std::log(disk.r_in);
  double log_r_out = std::log(disk.r_out);
  double d_log_r = (log_r_out - log_r_in) / n_points;

  for (int i = 0; i < n_points; ++i) {
    double log_r = log_r_in + (i + 0.5) * d_log_r;
    double r = std::exp(log_r);

    double T = disk_temperature(r, disk);
    double B_nu = planck_function(nu, T);

    // Integrate r dr = r² d(log r)
    sum += B_nu * r * r * d_log_r;
  }

  // Factor of 2 for both sides, cos(i) for projection
  return 4.0 * M_PI * std::cos(disk.inclination) * 2.0 * M_PI * sum;
}

/**
 * @brief Compute bolometric disk luminosity.
 *
 * L = η Ṁ c²
 *
 * where η is the radiative efficiency.
 *
 * @param disk Disk parameters
 * @return Luminosity [erg/s]
 */
inline double disk_luminosity(const DiskParams &disk) {
  double r_isco = disk.r_in;

  // Efficiency from ISCO binding energy
  // E_ISCO/c² for Schwarzschild: 1 - √(8/9) ≈ 0.0572
  double E_isco = specific_energy_schwarzschild(r_isco, disk.M);

  double eta = 1.0 - E_isco;

  return eta * disk.M_dot * C2;
}

// ============================================================================
// Relativistic Effects
// ============================================================================

/**
 * @brief Compute gravitational redshift factor for disk emission.
 *
 * g = √(1 - 3M/r)
 *
 * @param r Emission radius [cm]
 * @param M Black hole mass [g]
 * @return Redshift factor (0-1)
 */
inline double disk_redshift_factor(double r, double M) {
  double r_g = G * M / C2;
  double x = 3.0 * r_g / r;

  if (x >= 1.0) return 0.0;
  return std::sqrt(1.0 - x);
}

/**
 * @brief Compute Doppler factor for orbiting disk element.
 *
 * δ = 1 / (γ(1 - β cos φ))
 *
 * where γ = 1/√(1-β²), β = v/c
 *
 * @param r Orbital radius [cm]
 * @param phi Azimuthal angle relative to observer [rad]
 * @param inclination Disk inclination [rad]
 * @param M Black hole mass [g]
 * @return Doppler factor
 */
inline double disk_doppler_factor(double r, double phi, double inclination,
                                  double M) {
  // Orbital velocity
  double v = std::sqrt(G * M / r);
  double beta = v / C;

  // Velocity component toward observer
  double sin_i = std::sin(inclination);
  double beta_los = beta * std::sin(phi) * sin_i;

  // Lorentz factor
  double gamma = 1.0 / std::sqrt(1.0 - beta * beta);

  return 1.0 / (gamma * (1.0 - beta_los));
}

/**
 * @brief Compute observed flux including relativistic effects.
 *
 * F_obs = F_emit * g^4 * δ^4
 *
 * @param r Emission radius [cm]
 * @param phi Azimuthal angle [rad]
 * @param disk Disk parameters
 * @return Observed flux [erg/(cm² s)]
 */
inline double disk_flux_observed(double r, double phi, const DiskParams &disk) {
  double F_emit = disk_flux(r, disk);

  double g = disk_redshift_factor(r, disk.M);
  double delta = disk_doppler_factor(r, phi, disk.inclination, disk.M);

  // Combined factor: I_obs/I_emit = (g δ)^4 for specific intensity
  double factor = g * delta;
  double factor4 = factor * factor * factor * factor;

  return F_emit * factor4;
}

// ============================================================================
// Disk Structure (for visualization)
// ============================================================================

/**
 * @brief Radial profile point.
 */
struct DiskProfilePoint {
  double r;           ///< Radius [cm]
  double r_rg;        ///< Radius in gravitational radii
  double flux;        ///< Surface flux [erg/(cm² s)]
  double temperature; ///< Temperature [K]
  double v_orb;       ///< Orbital velocity [cm/s]
  double omega;       ///< Angular velocity [rad/s]
};

/**
 * @brief Generate radial profile of disk.
 *
 * @param disk Disk parameters
 * @param n_points Number of radial points
 * @return Vector of profile points
 */
inline std::vector<DiskProfilePoint> disk_profile(const DiskParams &disk,
                                                  int n_points = 100) {
  std::vector<DiskProfilePoint> profile;
  if (n_points <= 0) {
    return profile;
  }
  profile.reserve(static_cast<size_t>(n_points));

  double r_g = G * disk.M / C2;
  double log_r_in = std::log(disk.r_in);
  double log_r_out = std::log(disk.r_out);
  double d_log_r = (log_r_out - log_r_in) / (n_points - 1);

  for (int i = 0; i < n_points; ++i) {
    double log_r = log_r_in + i * d_log_r;
    double r = std::exp(log_r);

    DiskProfilePoint pt;
    pt.r = r;
    pt.r_rg = r / r_g;
    pt.flux = disk_flux(r, disk);
    pt.temperature = disk_temperature_from_flux(pt.flux);
    pt.v_orb = std::sqrt(G * disk.M / r);
    pt.omega = angular_velocity_schwarzschild(r, disk.M);

    profile.push_back(pt);
  }

  return profile;
}

// ============================================================================
// Color Temperature Mapping
// ============================================================================

/**
 * @brief Convert temperature to RGB color (approximate blackbody).
 *
 * Uses Planckian locus approximation for T > 1000 K.
 *
 * @param T Temperature [K]
 * @param r Output: red (0-1)
 * @param g Output: green (0-1)
 * @param b Output: blue (0-1)
 */
inline void temperature_to_rgb(double T, double &r, double &g, double &b) {
  // Clamp temperature range
  T = std::clamp(T, 1000.0, 40000.0);

  double t = T / 100.0;

  // Red
  if (T <= 6600) {
    r = 1.0;
  } else {
    r = 329.698727446 * std::pow(t - 60.0, -0.1332047592);
    r = std::clamp(r / 255.0, 0.0, 1.0);
  }

  // Green
  if (T <= 6600) {
    g = 99.4708025861 * std::log(t) - 161.1195681661;
  } else {
    g = 288.1221695283 * std::pow(t - 60.0, -0.0755148492);
  }
  g = std::clamp(g / 255.0, 0.0, 1.0);

  // Blue
  if (T >= 6600) {
    b = 1.0;
  } else if (T <= 1900) {
    b = 0.0;
  } else {
    b = 138.5177312231 * std::log(t - 10.0) - 305.0447927307;
    b = std::clamp(b / 255.0, 0.0, 1.0);
  }
}

} // namespace physics

#endif // PHYSICS_THIN_DISK_H
