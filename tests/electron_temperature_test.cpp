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
  EXPECT_NEAR(physics::temperatureRatio(0.0, 1.0), 1.0, 1e-14);
  EXPECT_NEAR(physics::temperatureRatio(100.0, 1.0), 2.0, 0.01);
}

// --------------------------------------------------------------------------
// R_high = 160: large temperature disparity at high beta
// --------------------------------------------------------------------------
TEST(ElectronTemperature, RHighLargeDisparity) {
  // At large beta: ratio -> R_high + 1 = 161
  double const ratio = physics::temperatureRatio(100.0, 160.0);
  EXPECT_NEAR(ratio, 161.0, 0.1);

  // At beta = 0 (magnetically dominated): ratio = 1
  EXPECT_NEAR(physics::temperatureRatio(0.0, 160.0), 1.0, 1e-14);
}

// --------------------------------------------------------------------------
// Electron temperature is lower than gas temperature for R_high > 1
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ElectronCoolerThanGas) {
  double const tGas = 1e12; // K
  double const beta = 10.0;

  double const tELow = physics::electronTemperature(tGas, beta, 160.0);
  double const tEHigh = physics::electronTemperature(tGas, beta, 1.0);

  EXPECT_LT(tELow, tEHigh);
  EXPECT_GT(tELow, 0.0);
  EXPECT_LT(tEHigh, tGas * 1.01);
}

// --------------------------------------------------------------------------
// Gas temperature from rho, P
// --------------------------------------------------------------------------
TEST(ElectronTemperature, GasTemperature) {
  // T = P * mu * m_p / (rho * k_B)
  // For rho = 1e-16 g/cm^3, P = 1e-6 erg/cm^3, mu = 0.5:
  double const t = physics::gasTemperature(1e-16, 1e-6, 0.5);
  EXPECT_GT(t, 0.0);

  // Check scaling: double P -> double T
  double const t2 = physics::gasTemperature(1e-16, 2e-6, 0.5);
  EXPECT_NEAR(t2 / t, 2.0, 1e-10);
}

// --------------------------------------------------------------------------
// Plasma beta
// --------------------------------------------------------------------------
TEST(ElectronTemperature, PlasmaBeta) {
  EXPECT_NEAR(physics::plasmaBeta(1.0, 2.0), 1.0, 1e-14);
  EXPECT_NEAR(physics::plasmaBeta(0.5, 1.0), 1.0, 1e-14);

  // Unmagnetized: very large beta
  EXPECT_GT(physics::plasmaBeta(1.0, 0.0), 1e9);
}

// --------------------------------------------------------------------------
// Dimensionless temperature Theta_e
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ThetaE) {
  // At T ~ 5.9e9 K, Theta_e ~ 1
  double const theta = physics::thetaE(5.93e9);
  EXPECT_NEAR(theta, 1.0, 0.05);

  // Linear in temperature
  EXPECT_NEAR(physics::thetaE(1e10) / physics::thetaE(5e9), 2.0, 1e-10);
}

// --------------------------------------------------------------------------
// Thermal synchrotron emissivity is positive and finite
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ThermalEmissivity) {
  double const j = physics::thermalSynchrotronEmissivity(230e9, // 230 GHz (EHT)
                                                         1e5,   // n_e [cm^-3]
                                                         10.0,  // Theta_e = 10 (hot)
                                                         10.0   // B = 10 Gauss
  );

  EXPECT_GT(j, 0.0);
  EXPECT_TRUE(std::isfinite(j));
}

// --------------------------------------------------------------------------
// Emissivity vanishes for zero inputs
// --------------------------------------------------------------------------
TEST(ElectronTemperature, EmissivityZeroInputs) {
  EXPECT_EQ(physics::thermalSynchrotronEmissivity(0.0, 1e5, 10.0, 10.0), 0.0);
  EXPECT_EQ(physics::thermalSynchrotronEmissivity(230e9, 1e5, 0.0, 10.0), 0.0);
  EXPECT_EQ(physics::thermalSynchrotronEmissivity(230e9, 1e5, 10.0, 0.0), 0.0);
}

// --------------------------------------------------------------------------
// Absorptivity via Kirchhoff's law
// --------------------------------------------------------------------------
TEST(ElectronTemperature, Absorptivity) {
  double const j = physics::thermalSynchrotronEmissivity(230e9, 1e5, 10.0, 10.0);
  double const alpha = physics::thermalSynchrotronAbsorptivity(j, 230e9, 10.0);

  EXPECT_GT(alpha, 0.0);
  EXPECT_TRUE(std::isfinite(alpha));
}

// --------------------------------------------------------------------------
// Electron density from rho
// --------------------------------------------------------------------------
TEST(ElectronTemperature, ElectronDensity) {
  double const nE = physics::electronDensity(1e-16); // g/cm^3
  // n_e = rho / m_p ~ 1e-16 / 1.67e-24 ~ 6e7
  EXPECT_NEAR(nE, 5.975e7, 1e5);
}
