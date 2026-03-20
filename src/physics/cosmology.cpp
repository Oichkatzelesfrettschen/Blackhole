/**
 * @file cosmology.cpp
 * @brief Implementation of cosmological calculations.
 */

#include "cosmology.h"
#include "constants.h"

#include <cmath>

namespace physics {

// Speed of light in km/s for cosmology calculations
static constexpr double C_KM_S = 299792.458;

// Conversion factor: seconds per gigayear
// 1 Gyr = 10^9 years x 365.25 days/year x 24 hours/day x 3600 s/hour
// Reserved for future age-of-universe calculations with higher precision.
[[maybe_unused]] static constexpr double SEC_PER_GYR = 3.15576e16;

// Conversion: H0 [km/s/Mpc] to [1/s]
// Reserved for use in future lookback time refinements.
// The current implementation uses a simplified h0PerGyr factor.
[[maybe_unused]] static constexpr double KM_S_MPC_TO_PER_SEC = 1.0 / (MPC * 1.0e-5);

// ============================================================================
// Hubble Parameter
// ============================================================================

double hubbleE(double z, double omegaM) {
  const double omegaLambda = 1.0 - omegaM;
  const double onePlusZ = 1.0 + z;
  const double onePlusZCubed = onePlusZ * onePlusZ * onePlusZ;
  return std::sqrt((omegaM * onePlusZCubed) + omegaLambda);
}

double hubbleParameter(double z, double h0, double omegaM) {
  return h0 * hubbleE(z, omegaM);
}

// ============================================================================
// Cosmological Distances
// ============================================================================

double comovingDistance(double z, double h0, double omegaM, int nSteps) {
  if (z <= 0.0) {
    return 0.0;
  }

  // Trapezoidal integration of 1/E(z') from 0 to z
  const double dz = z / static_cast<double>(nSteps);
  double integral = 0.0;

  // Endpoints
  integral += 0.5 / hubbleE(0.0, omegaM);
  integral += 0.5 / hubbleE(z, omegaM);

  // Interior points
  for (int i = 1; i < nSteps; ++i) {
    const double zi = static_cast<double>(i) * dz;
    integral += 1.0 / hubbleE(zi, omegaM);
  }

  integral *= dz;

  // D_C = (c/H0) * integral [Mpc]
  return (C_KM_S / h0) * integral;
}

double luminosityDistance(double z, double h0, double omegaM) {
  // D_L = (1+z) * D_C
  return (1.0 + z) * comovingDistance(z, h0, omegaM);
}

double angularDiameterDistance(double z, double h0, double omegaM) {
  // D_A = D_C / (1+z)
  return comovingDistance(z, h0, omegaM) / (1.0 + z);
}

double distanceModulus(double z, double h0, double omegaM) {
  const double dL = luminosityDistance(z, h0, omegaM);
  // mu = 5 log10(D_L [Mpc]) + 25
  return (5.0 * std::log10(dL)) + 25.0;
}

// ============================================================================
// Redshift Relations
// ============================================================================

double wavelengthToRedshift(double lambdaObserved, double lambdaEmitted) {
  return (lambdaObserved / lambdaEmitted) - 1.0;
}

double applyRedshiftToWavelength(double lambdaEmitted, double z) {
  return lambdaEmitted * (1.0 + z);
}

double redshiftFluxDimming(double z) {
  const double onePlusZ = 1.0 + z;
  const double factor = onePlusZ * onePlusZ * onePlusZ * onePlusZ;
  return 1.0 / factor;
}

// ============================================================================
// Lookback Time
// ============================================================================

double lookbackTime(double z, double h0, double omegaM) {
  if (z <= 0.0) {
    return 0.0;
  }

  // t_L = (1/H0) int_0^z dz' / ((1+z') E(z'))
  const int nSteps = 1000;
  const double dz = z / static_cast<double>(nSteps);
  double integral = 0.0;

  // Trapezoidal integration
  auto integrand = [omegaM](double zp) {
    return 1.0 / ((1.0 + zp) * hubbleE(zp, omegaM));
  };

  integral += 0.5 * integrand(0.0);
  integral += 0.5 * integrand(z);

  for (int i = 1; i < nSteps; ++i) {
    const double zi = static_cast<double>(i) * dz;
    integral += integrand(zi);
  }

  integral *= dz;

  // Convert H0 from km/s/Mpc to 1/Gyr
  // H0 [km/s/Mpc] * [Mpc/km] * [s/Gyr]^{-1} = [1/Gyr]
  // 1 Mpc = 3.086e19 km
  // 1 Gyr = 3.156e16 s
  // H0 [1/Gyr] = H0 [km/s/Mpc] * 3.086e19 / 3.156e16 = H0 * 977.8
  const double h0PerGyr = h0 * 0.001022; // 1/(977.8)

  return integral / h0PerGyr;
}

double universeAgeAtZ(double z, double h0, double omegaM) {
  // Age at z = current age - lookback time
  // For Planck 2018 cosmology, current age approx 13.8 Gyr
  const double ageNow = lookbackTime(1000.0, h0, omegaM); // Approximate
  return ageNow - lookbackTime(z, h0, omegaM);
}

} // namespace physics
