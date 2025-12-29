/**
 * @file cosmology.h
 * @brief Cosmological calculations for distance and redshift.
 *
 * Implements distance-redshift relations for flat ΛCDM cosmology.
 * All distances returned in Mpc unless otherwise specified.
 *
 * Cleanroom implementation based on standard cosmology textbooks.
 */

#ifndef PHYSICS_COSMOLOGY_H
#define PHYSICS_COSMOLOGY_H

#include <cmath>

namespace physics {

// ============================================================================
// Hubble Parameter
// ============================================================================

/**
 * @brief Compute dimensionless Hubble parameter E(z) = H(z)/H0.
 *
 * For flat ΛCDM: E(z) = √(Ωm(1+z)³ + ΩΛ)
 *
 * @param z Redshift
 * @param omega_m Matter density parameter (default: Planck 2018)
 * @return E(z) dimensionless
 */
double hubble_E(double z, double omega_m = 0.315);

/**
 * @brief Compute Hubble parameter H(z) in km/s/Mpc.
 *
 * H(z) = H0 * E(z)
 *
 * @param z Redshift
 * @param H0 Hubble constant [km/s/Mpc] (default: Planck 2018)
 * @param omega_m Matter density parameter (default: Planck 2018)
 * @return Hubble parameter [km/s/Mpc]
 */
double hubble_parameter(double z, double H0 = 67.4, double omega_m = 0.315);

// ============================================================================
// Cosmological Distances
// ============================================================================

/**
 * @brief Compute comoving distance in Mpc.
 *
 * D_C(z) = (c/H0) ∫₀^z dz'/E(z')
 *
 * Uses trapezoidal integration.
 *
 * @param z Redshift
 * @param H0 Hubble constant [km/s/Mpc]
 * @param omega_m Matter density parameter
 * @param n_steps Integration steps
 * @return Comoving distance [Mpc]
 */
double comoving_distance(double z, double H0 = 67.4, double omega_m = 0.315,
                         int n_steps = 1000);

/**
 * @brief Compute luminosity distance in Mpc.
 *
 * For flat universe: D_L(z) = (1+z) * D_C(z)
 *
 * @param z Redshift
 * @param H0 Hubble constant [km/s/Mpc]
 * @param omega_m Matter density parameter
 * @return Luminosity distance [Mpc]
 */
double luminosity_distance(double z, double H0 = 67.4, double omega_m = 0.315);

/**
 * @brief Compute angular diameter distance in Mpc.
 *
 * For flat universe: D_A(z) = D_C(z) / (1+z)
 *
 * @param z Redshift
 * @param H0 Hubble constant [km/s/Mpc]
 * @param omega_m Matter density parameter
 * @return Angular diameter distance [Mpc]
 */
double angular_diameter_distance(double z, double H0 = 67.4,
                                 double omega_m = 0.315);

/**
 * @brief Compute distance modulus μ = m - M.
 *
 * μ = 5 log₁₀(D_L [Mpc]) + 25
 *
 * @param z Redshift
 * @param H0 Hubble constant [km/s/Mpc]
 * @param omega_m Matter density parameter
 * @return Distance modulus [magnitudes]
 */
double distance_modulus(double z, double H0 = 67.4, double omega_m = 0.315);

// ============================================================================
// Redshift Relations
// ============================================================================

/**
 * @brief Convert wavelength ratio to redshift.
 *
 * z = λ_obs/λ_emit - 1
 *
 * @param lambda_observed Observed wavelength
 * @param lambda_emitted Emitted wavelength
 * @return Redshift z
 */
double wavelength_to_redshift(double lambda_observed, double lambda_emitted);

/**
 * @brief Apply redshift to wavelength.
 *
 * λ_obs = λ_emit * (1 + z)
 *
 * @param lambda_emitted Emitted wavelength
 * @param z Redshift
 * @return Observed wavelength
 */
double apply_redshift_to_wavelength(double lambda_emitted, double z);

/**
 * @brief Compute flux dimming factor from redshift.
 *
 * F_obs/F_emit = 1/(1+z)⁴
 *
 * This includes:
 * - (1+z)⁻¹ from energy decrease per photon
 * - (1+z)⁻¹ from photon arrival rate decrease
 * - (1+z)⁻² from angular diameter distance squared
 *
 * @param z Redshift
 * @return Flux ratio F_obs/F_emit
 */
double redshift_flux_dimming(double z);

// ============================================================================
// Lookback Time
// ============================================================================

/**
 * @brief Compute lookback time in Gyr.
 *
 * t_L(z) = (1/H0) ∫₀^z dz' / ((1+z') E(z'))
 *
 * @param z Redshift
 * @param H0 Hubble constant [km/s/Mpc]
 * @param omega_m Matter density parameter
 * @return Lookback time [Gyr]
 */
double lookback_time(double z, double H0 = 67.4, double omega_m = 0.315);

/**
 * @brief Compute age of universe at redshift z in Gyr.
 *
 * @param z Redshift
 * @param H0 Hubble constant [km/s/Mpc]
 * @param omega_m Matter density parameter
 * @return Age [Gyr]
 */
double universe_age_at_z(double z, double H0 = 67.4, double omega_m = 0.315);

} // namespace physics

#endif // PHYSICS_COSMOLOGY_H
