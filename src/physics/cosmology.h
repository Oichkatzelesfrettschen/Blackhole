/**
 * @file cosmology.h
 * @brief Cosmological calculations for distance and redshift.
 *
 * Implements distance-redshift relations for flat LCDM cosmology.
 * All distances returned in Mpc unless otherwise specified.
 *
 * Cleanroom implementation based on standard cosmology textbooks.
 */

#ifndef PHYSICS_COSMOLOGY_H
#define PHYSICS_COSMOLOGY_H

namespace physics {

// ============================================================================
// Hubble Parameter
// ============================================================================

/**
 * @brief Compute dimensionless Hubble parameter E(z) = H(z)/H0.
 *
 * For flat LCDM: E(z) = sqrt(Om(1+z)^3 + OL)
 *
 * @param z Redshift
 * @param omegaM Matter density parameter (default: Planck 2018)
 * @return E(z) dimensionless
 */
double hubbleE(double z, double omegaM = 0.315);

/**
 * @brief Compute Hubble parameter H(z) in km/s/Mpc.
 *
 * H(z) = H0 * E(z)
 *
 * @param z Redshift
 * @param h0 Hubble constant [km/s/Mpc] (default: Planck 2018)
 * @param omegaM Matter density parameter (default: Planck 2018)
 * @return Hubble parameter [km/s/Mpc]
 */
double hubbleParameter(double z, double h0 = 67.4, double omegaM = 0.315);

// ============================================================================
// Cosmological Distances
// ============================================================================

/**
 * @brief Compute comoving distance in Mpc.
 *
 * D_C(z) = (c/H0) int_0^z dz'/E(z')
 *
 * Uses trapezoidal integration.
 *
 * @param z Redshift
 * @param h0 Hubble constant [km/s/Mpc]
 * @param omegaM Matter density parameter
 * @param nSteps Integration steps
 * @return Comoving distance [Mpc]
 */
double comovingDistance(double z, double h0 = 67.4, double omegaM = 0.315, int nSteps = 1000);

/**
 * @brief Compute luminosity distance in Mpc.
 *
 * For flat universe: D_L(z) = (1+z) * D_C(z)
 *
 * @param z Redshift
 * @param h0 Hubble constant [km/s/Mpc]
 * @param omegaM Matter density parameter
 * @return Luminosity distance [Mpc]
 */
double luminosityDistance(double z, double h0 = 67.4, double omegaM = 0.315);

/**
 * @brief Compute angular diameter distance in Mpc.
 *
 * For flat universe: D_A(z) = D_C(z) / (1+z)
 *
 * @param z Redshift
 * @param h0 Hubble constant [km/s/Mpc]
 * @param omegaM Matter density parameter
 * @return Angular diameter distance [Mpc]
 */
double angularDiameterDistance(double z, double h0 = 67.4, double omegaM = 0.315);

/**
 * @brief Compute distance modulus mu = m - M.
 *
 * mu = 5 log10(D_L [Mpc]) + 25
 *
 * @param z Redshift
 * @param h0 Hubble constant [km/s/Mpc]
 * @param omegaM Matter density parameter
 * @return Distance modulus [magnitudes]
 */
double distanceModulus(double z, double h0 = 67.4, double omegaM = 0.315);

// ============================================================================
// Redshift Relations
// ============================================================================

/**
 * @brief Convert wavelength ratio to redshift.
 *
 * z = lambda_obs/lambda_emit - 1
 *
 * @param lambdaObserved Observed wavelength
 * @param lambdaEmitted Emitted wavelength
 * @return Redshift z
 */
double wavelengthToRedshift(double lambdaObserved, double lambdaEmitted);

/**
 * @brief Apply redshift to wavelength.
 *
 * lambda_obs = lambda_emit * (1 + z)
 *
 * @param lambdaEmitted Emitted wavelength
 * @param z Redshift
 * @return Observed wavelength
 */
double applyRedshiftToWavelength(double lambdaEmitted, double z);

/**
 * @brief Compute flux dimming factor from redshift.
 *
 * F_obs/F_emit = 1/(1+z)^4
 *
 * This includes:
 * - (1+z)^-1 from energy decrease per photon
 * - (1+z)^-1 from photon arrival rate decrease
 * - (1+z)^-2 from angular diameter distance squared
 *
 * @param z Redshift
 * @return Flux ratio F_obs/F_emit
 */
double redshiftFluxDimming(double z);

// ============================================================================
// Lookback Time
// ============================================================================

/**
 * @brief Compute lookback time in Gyr.
 *
 * t_L(z) = (1/H0) int_0^z dz' / ((1+z') E(z'))
 *
 * @param z Redshift
 * @param h0 Hubble constant [km/s/Mpc]
 * @param omegaM Matter density parameter
 * @return Lookback time [Gyr]
 */
double lookbackTime(double z, double h0 = 67.4, double omegaM = 0.315);

/**
 * @brief Compute age of universe at redshift z in Gyr.
 *
 * @param z Redshift
 * @param h0 Hubble constant [km/s/Mpc]
 * @param omegaM Matter density parameter
 * @return Age [Gyr]
 */
double universeAgeAtZ(double z, double h0 = 67.4, double omegaM = 0.315);

} // namespace physics

#endif // PHYSICS_COSMOLOGY_H
