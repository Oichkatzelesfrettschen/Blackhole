/**
 * @file electron_temperature_test.cpp
 * @brief Tests for two-temperature electron thermodynamics.
 */

#include <gtest/gtest.h>
#include "physics/electron_temperature.h"
#include <cmath>

// --------------------------------------------------------------------------
// R_high = 1: equal temperatures (T_p/T_e = 1 for all beta)
// --------------------------------------------------------------------------
TEST(ElectronTemperature, RHighOneEqualTemps) {
  // R_high = 1: ratio = 1 * beta^2/(1+beta^2) + 1
  // For large beta: ratio -> 2
  // For small beta: ratio -> 1
  EXPECT_NEAR(physics::temperature_ratio(0.0, 1.0), 1.0, 1e-14);
  EXPECT_NEAR(physics::temperature_ratio(100.0, 1.0), 2.0, 0.01);
}

// --------------------------------------------------------------------------
// R_high = 160: large temperature disparity at high beta
// --------------------------------------------------------------------------
TEST(ElectronTemperature, RHighLargeDisparity) {
  // At large beta: ratio -> R_high + 1 = 161
  double ratio = physics::temperature_ratio(100.0, 160.0);
  EXPECT_NEAR(ratio, 161.0, 0.1);

  // At beta = 0 (magnetically dominated): ratio = 1
  EXPECT_NEAR(physics::temperature_ratio(0.0, 160.0), 1.0, 1e-14);
}

// --------------------------------------------------------------------------
// Electron temperature is lower than gas temperature for R_high > 1
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ElectronCoolerThanGas) {
  double T_gas = 1e12; // K
  double beta = 10.0;

  double T_e_low = physics::electron_temperature(T_gas, beta, 160.0);
  double T_e_high = physics::electron_temperature(T_gas, beta, 1.0);

  EXPECT_LT(T_e_low, T_e_high);
  EXPECT_GT(T_e_low, 0.0);
  EXPECT_LT(T_e_high, T_gas * 1.01);
}

// --------------------------------------------------------------------------
// Gas temperature from rho, P
// --------------------------------------------------------------------------
TEST(ElectronTemperature, GasTemperature) {
  // T = P * mu * m_p / (rho * k_B)
  // For rho = 1e-16 g/cm^3, P = 1e-6 erg/cm^3, mu = 0.5:
  double T = physics::gas_temperature(1e-16, 1e-6, 0.5);
  EXPECT_GT(T, 0.0);

  // Check scaling: double P -> double T
  double T2 = physics::gas_temperature(1e-16, 2e-6, 0.5);
  EXPECT_NEAR(T2 / T, 2.0, 1e-10);
}

// --------------------------------------------------------------------------
// Plasma beta
// --------------------------------------------------------------------------
TEST(ElectronTemperature, PlasmaBeta) {
  EXPECT_NEAR(physics::plasma_beta(1.0, 2.0), 1.0, 1e-14);
  EXPECT_NEAR(physics::plasma_beta(0.5, 1.0), 1.0, 1e-14);

  // Unmagnetized: very large beta
  EXPECT_GT(physics::plasma_beta(1.0, 0.0), 1e9);
}

// --------------------------------------------------------------------------
// Dimensionless temperature Theta_e
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ThetaE) {
  // At T ~ 5.9e9 K, Theta_e ~ 1
  double theta = physics::theta_e(5.93e9);
  EXPECT_NEAR(theta, 1.0, 0.05);

  // Linear in temperature
  EXPECT_NEAR(physics::theta_e(1e10) / physics::theta_e(5e9), 2.0, 1e-10);
}

// --------------------------------------------------------------------------
// Thermal synchrotron emissivity is positive and finite
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ThermalEmissivity) {
  double j = physics::thermal_synchrotron_emissivity(
      230e9,    // 230 GHz (EHT)
      1e5,      // n_e [cm^-3]
      10.0,     // Theta_e = 10 (hot)
      10.0      // B = 10 Gauss
  );

  EXPECT_GT(j, 0.0);
  EXPECT_TRUE(std::isfinite(j));
}

// --------------------------------------------------------------------------
// Emissivity vanishes for zero inputs
// --------------------------------------------------------------------------
TEST(ElectronTemperature, EmissivityZeroInputs) {
  EXPECT_EQ(physics::thermal_synchrotron_emissivity(0.0, 1e5, 10.0, 10.0), 0.0);
  EXPECT_EQ(physics::thermal_synchrotron_emissivity(230e9, 1e5, 0.0, 10.0), 0.0);
  EXPECT_EQ(physics::thermal_synchrotron_emissivity(230e9, 1e5, 10.0, 0.0), 0.0);
}

// --------------------------------------------------------------------------
// Absorptivity via Kirchhoff's law
// --------------------------------------------------------------------------
TEST(ElectronTemperature, Absorptivity) {
  double j = physics::thermal_synchrotron_emissivity(230e9, 1e5, 10.0, 10.0);
  double alpha = physics::thermal_synchrotron_absorptivity(j, 230e9, 10.0);

  EXPECT_GT(alpha, 0.0);
  EXPECT_TRUE(std::isfinite(alpha));
}

// --------------------------------------------------------------------------
// Electron density from rho
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ElectronDensity) {
  double n_e = physics::electron_density(1e-16); // g/cm^3
  // n_e = rho / m_p ~ 1e-16 / 1.67e-24 ~ 6e7
  EXPECT_NEAR(n_e, 5.975e7, 1e5);
}
