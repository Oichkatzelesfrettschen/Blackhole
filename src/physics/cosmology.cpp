/**
 * @file cosmology.cpp
 * @brief Implementation of cosmological calculations.
 */

#include "cosmology.h"
#include "constants.h"

namespace physics {

// Speed of light in km/s for cosmology calculations
static constexpr double C_KM_S = 299792.458;

// Seconds per Gyr
static constexpr double SEC_PER_GYR = 3.15576e16;

// km/s/Mpc to 1/s conversion (H0 units)
static constexpr double KM_S_MPC_TO_PER_SEC = 1.0 / (MPC * 1.0e-5);

// ============================================================================
// Hubble Parameter
// ============================================================================

double hubble_E(double z, double omega_m) {
  double omega_lambda = 1.0 - omega_m;
  double one_plus_z = 1.0 + z;
  double one_plus_z_cubed = one_plus_z * one_plus_z * one_plus_z;
  return std::sqrt(omega_m * one_plus_z_cubed + omega_lambda);
}

double hubble_parameter(double z, double H0, double omega_m) {
  return H0 * hubble_E(z, omega_m);
}

// ============================================================================
// Cosmological Distances
// ============================================================================

double comoving_distance(double z, double H0, double omega_m, int n_steps) {
  if (z <= 0.0) {
    return 0.0;
  }

  // Trapezoidal integration of 1/E(z') from 0 to z
  double dz = z / static_cast<double>(n_steps);
  double integral = 0.0;

  // Endpoints
  integral += 0.5 / hubble_E(0.0, omega_m);
  integral += 0.5 / hubble_E(z, omega_m);

  // Interior points
  for (int i = 1; i < n_steps; ++i) {
    double zi = static_cast<double>(i) * dz;
    integral += 1.0 / hubble_E(zi, omega_m);
  }

  integral *= dz;

  // D_C = (c/H0) * integral [Mpc]
  return (C_KM_S / H0) * integral;
}

double luminosity_distance(double z, double H0, double omega_m) {
  // D_L = (1+z) * D_C
  return (1.0 + z) * comoving_distance(z, H0, omega_m);
}

double angular_diameter_distance(double z, double H0, double omega_m) {
  // D_A = D_C / (1+z)
  return comoving_distance(z, H0, omega_m) / (1.0 + z);
}

double distance_modulus(double z, double H0, double omega_m) {
  double D_L = luminosity_distance(z, H0, omega_m);
  // μ = 5 log₁₀(D_L [Mpc]) + 25
  return 5.0 * std::log10(D_L) + 25.0;
}

// ============================================================================
// Redshift Relations
// ============================================================================

double wavelength_to_redshift(double lambda_observed, double lambda_emitted) {
  return lambda_observed / lambda_emitted - 1.0;
}

double apply_redshift_to_wavelength(double lambda_emitted, double z) {
  return lambda_emitted * (1.0 + z);
}

double redshift_flux_dimming(double z) {
  double one_plus_z = 1.0 + z;
  double factor = one_plus_z * one_plus_z * one_plus_z * one_plus_z;
  return 1.0 / factor;
}

// ============================================================================
// Lookback Time
// ============================================================================

double lookback_time(double z, double H0, double omega_m) {
  if (z <= 0.0) {
    return 0.0;
  }

  // t_L = (1/H0) ∫₀^z dz' / ((1+z') E(z'))
  int n_steps = 1000;
  double dz = z / static_cast<double>(n_steps);
  double integral = 0.0;

  // Trapezoidal integration
  auto integrand = [omega_m](double zp) {
    return 1.0 / ((1.0 + zp) * hubble_E(zp, omega_m));
  };

  integral += 0.5 * integrand(0.0);
  integral += 0.5 * integrand(z);

  for (int i = 1; i < n_steps; ++i) {
    double zi = static_cast<double>(i) * dz;
    integral += integrand(zi);
  }

  integral *= dz;

  // Convert H0 from km/s/Mpc to 1/Gyr
  // H0 [km/s/Mpc] * [Mpc/km] * [s/Gyr]^{-1} = [1/Gyr]
  // 1 Mpc = 3.086e19 km
  // 1 Gyr = 3.156e16 s
  // H0 [1/Gyr] = H0 [km/s/Mpc] * 3.086e19 / 3.156e16 = H0 * 977.8
  double H0_per_Gyr = H0 * 0.001022; // 1/(977.8)

  return integral / H0_per_Gyr;
}

double universe_age_at_z(double z, double H0, double omega_m) {
  // Age at z = current age - lookback time
  // For Planck 2018 cosmology, current age ≈ 13.8 Gyr
  double age_now = lookback_time(1000.0, H0, omega_m); // Approximate
  return age_now - lookback_time(z, H0, omega_m);
}

} // namespace physics
