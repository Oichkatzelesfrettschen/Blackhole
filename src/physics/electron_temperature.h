/**
 * @file electron_temperature.h
 * @brief Two-temperature electron thermodynamics for EHT modeling.
 *
 * WHY: In black hole accretion flows, ions and electrons are not in
 * thermal equilibrium. The electron temperature T_e determines synchrotron
 * emission, and the R_high prescription is the primary free parameter
 * in EHT GRMHD model fitting (EHT M87* Paper V, 2019).
 *
 * WHAT: The R_high model parameterizes the ion-to-electron temperature
 * ratio as a function of the plasma beta parameter:
 *
 *   T_p / T_e = R_high * beta^2 / (1 + beta^2) + 1
 *
 * where beta = P_gas / P_mag is the plasma beta. In magnetically
 * dominated regions (beta << 1), T_e ~ T_p (electrons are hot).
 * In gas-dominated regions (beta >> 1), T_p/T_e ~ R_high (electrons
 * are cooler by factor R_high).
 *
 * This naturally produces:
 *   - Hot electrons in the jet/funnel (low beta) -> bright synchrotron
 *   - Cold electrons in the disk midplane (high beta) -> dim emission
 *
 * Typical EHT values: R_high in {1, 10, 20, 40, 80, 160}.
 *
 * HOW: Given GRMHD fluid variables (rho, P_gas, B^2), compute T_e
 * and thermal synchrotron emissivity/absorptivity.
 *
 * References:
 *   - Moscibrodzka, Falcke, Shiber (2016), A&A 586, A38
 *   - EHT Collaboration Paper V (2019), ApJL 875, L5
 *   - EHT GRMHD Model Library (2024), arXiv:2411.12647
 */

#ifndef PHYSICS_ELECTRON_TEMPERATURE_H
#define PHYSICS_ELECTRON_TEMPERATURE_H

#include "constants.h"
#include <cmath>

namespace physics {

// ============================================================================
// Physical Constants for Electron Thermodynamics
// ============================================================================

/// Proton mass [g]
inline constexpr double M_PROTON = 1.67262192369e-24;

/// Proton-to-electron mass ratio
inline constexpr double MP_ME = M_PROTON / 9.1093837015e-28;

// ============================================================================
// R_high Temperature Prescription
// ============================================================================

/**
 * @brief Compute ion-to-electron temperature ratio using R_high model.
 *
 *   T_p / T_e = R_high * beta^2 / (1 + beta^2) + 1
 *
 * @param beta Plasma beta = P_gas / P_mag
 * @param R_high Temperature ratio parameter (1 = equal, 160 = very unequal)
 * @return T_p / T_e ratio (always >= 1)
 */
inline double temperature_ratio(double beta, double R_high) {
  double beta2 = beta * beta;
  return R_high * beta2 / (1.0 + beta2) + 1.0;
}

/**
 * @brief Compute electron temperature from gas temperature.
 *
 * Given the single-fluid gas temperature T_gas and plasma beta:
 *   T_e = T_gas * (m_p + m_e) / (m_p * (1 + 1/ratio) + m_e * (1 + ratio))
 *
 * Simplified (m_p >> m_e):
 *   T_e ~ T_gas / ratio  (for ratio >> 1)
 *   T_e ~ T_gas           (for ratio ~ 1)
 *
 * The exact formula accounts for the two-species equation of state:
 *   T_gas = (T_p * m_e + T_e * m_p) / (m_p + m_e)
 *
 * @param T_gas Single-fluid gas temperature [K]
 * @param beta Plasma beta
 * @param R_high Temperature ratio parameter
 * @return Electron temperature T_e [K]
 */
inline double electron_temperature(double T_gas, double beta, double R_high) {
  double ratio = temperature_ratio(beta, R_high);
  // Exact two-species formula: T_e = T_gas / (1 + (m_e/m_p)*(ratio - 1))
  // Since m_e/m_p << 1, this is very close to T_gas / ratio for large ratio
  return T_gas / (1.0 + (1.0 / MP_ME) * (ratio - 1.0));
}

/**
 * @brief Compute gas temperature from GRMHD primitive variables.
 *
 *   T_gas = P_gas * mu * m_p / (rho * k_B)
 *
 * where mu is the mean molecular weight (0.5 for fully ionized H+e).
 *
 * @param rho Gas density [g/cm^3]
 * @param P_gas Gas pressure [erg/cm^3]
 * @param mu Mean molecular weight (default 0.5 for ionized hydrogen)
 * @return Gas temperature [K]
 */
inline double gas_temperature(double rho, double P_gas, double mu = 0.5) {
  if (rho <= 0.0) return 0.0;
  return P_gas * mu * M_PROTON / (rho * K_B);
}

/**
 * @brief Compute plasma beta from GRMHD variables.
 *
 *   beta = P_gas / P_mag = 2 * P_gas / B^2
 *
 * (In Gaussian CGS, P_mag = B^2 / (8*pi), but GRMHD codes typically
 * use Heaviside units where P_mag = B^2 / 2.)
 *
 * @param P_gas Gas pressure [code units]
 * @param B_sq Magnetic field squared B^2 = B_i B^i [code units]
 * @return Plasma beta (dimensionless)
 */
inline double plasma_beta(double P_gas, double B_sq) {
  if (B_sq <= 0.0) return 1e10; // Unmagnetized limit
  return 2.0 * P_gas / B_sq;
}

// ============================================================================
// Electron Thermodynamic Quantities
// ============================================================================

/**
 * @brief Dimensionless electron temperature Theta_e = k_B T_e / (m_e c^2).
 *
 * This is the natural temperature scale for synchrotron emission.
 * Theta_e ~ 1 corresponds to T_e ~ 6e9 K (mildly relativistic electrons).
 *
 * @param T_e Electron temperature [K]
 * @return Dimensionless temperature
 */
inline double theta_e(double T_e) {
  constexpr double ME_C2 = 9.1093837015e-28 * C * C; // m_e c^2 [erg]
  return K_B * T_e / ME_C2;
}

/**
 * @brief Electron number density from gas density.
 *
 * For fully ionized hydrogen: n_e = rho / m_p
 *
 * @param rho Gas density [g/cm^3]
 * @return Electron number density [cm^-3]
 */
inline double electron_density(double rho) {
  return rho / M_PROTON;
}

// ============================================================================
// Thermal Synchrotron Emission
// ============================================================================

/**
 * @brief Thermal synchrotron emissivity (Leung, Gammie, Noble 2011).
 *
 * For a thermal (Maxwell-Juttner) electron distribution:
 *
 *   j_nu = (n_e * e^2 * nu) / (sqrt(3) * c * Theta_e^2)
 *        * I'(x_M) * exp(-x_M^(1/3))
 *
 * where x_M = nu / nu_s, nu_s = (2/9) * nu_c * Theta_e^2,
 * and nu_c = eB/(2*pi*m_e*c) is the cyclotron frequency.
 *
 * Approximate form (Dexter 2016, Eq. 25):
 *   j_nu ~ C * n_e * nu * exp(-(nu/nu_c)^(1/3)) / Theta_e^2
 *
 * @param nu Observing frequency [Hz]
 * @param n_e Electron density [cm^-3]
 * @param Theta_e Dimensionless electron temperature
 * @param B Magnetic field strength [Gauss]
 * @return Emissivity j_nu [erg/s/cm^3/Hz/sr]
 */
inline double thermal_synchrotron_emissivity(double nu, double n_e,
                                              double Theta_e, double B) {
  if (Theta_e <= 0.0 || B <= 0.0 || nu <= 0.0) return 0.0;

  constexpr double E_CHARGE = 4.80320425e-10; // [esu]
  constexpr double MASS_E = 9.1093837015e-28;    // [g]

  // Cyclotron frequency
  double nu_c = E_CHARGE * std::abs(B) / (TWO_PI * MASS_E * C);

  // Synchrotron peak frequency for thermal electrons
  double nu_s = (2.0 / 9.0) * nu_c * Theta_e * Theta_e;

  if (nu_s <= 0.0) return 0.0;

  double x_M = nu / nu_s;

  // Fitting formula from Leung+ 2011, Eq. 24
  // Valid for Theta_e > 1 (relativistic regime)
  double x_M_13 = std::cbrt(x_M);
  double prefactor = n_e * E_CHARGE * E_CHARGE * nu /
                     (std::sqrt(3.0) * C * Theta_e * Theta_e);

  // Approximate spectral shape
  double shape = 4.0505 / x_M_13 *
                 (1.0 + 0.40 / std::sqrt(x_M_13) + 0.5316 / x_M_13) *
                 std::exp(-1.8899 * x_M_13);

  return prefactor * shape;
}

/**
 * @brief Thermal synchrotron absorption coefficient.
 *
 * Related to emissivity via Kirchhoff's law:
 *   alpha_nu = j_nu / B_nu
 *
 * where B_nu is the Planck function. For relativistic electrons:
 *   B_nu ~ 2 * nu^2 * m_e * c * Theta_e / c^2
 *        = 2 * nu^2 * k_B * T_e / c^2
 *
 * @param j_nu Emissivity [erg/s/cm^3/Hz/sr]
 * @param nu Frequency [Hz]
 * @param Theta_e Dimensionless electron temperature
 * @return Absorption coefficient [cm^-1]
 */
inline double thermal_synchrotron_absorptivity(double j_nu, double nu,
                                                double Theta_e) {
  if (nu <= 0.0 || Theta_e <= 0.0 || j_nu <= 0.0) return 0.0;

  // Relativistic Planck function (Rayleigh-Jeans limit for kT >> hv)
  constexpr double MASS_E = 9.1093837015e-28;
  double B_nu = 2.0 * nu * nu * MASS_E * C * Theta_e / (C * C);

  if (B_nu <= 0.0) return 0.0;

  return j_nu / B_nu;
}

// ============================================================================
// EHT Model Presets
// ============================================================================

/**
 * @brief Standard R_high values used in EHT GRMHD model library.
 *
 * From EHT M87* Paper V (2019) and arXiv:2411.12647.
 * Each R_high produces a different image morphology:
 *   R_high = 1: electrons everywhere hot (disk-dominated)
 *   R_high = 10-40: intermediate (ring + disk)
 *   R_high = 80-160: only jet/funnel electrons hot (jet-dominated)
 */
inline constexpr double EHT_R_HIGH_VALUES[] = {1.0, 10.0, 20.0, 40.0, 80.0, 160.0};
inline constexpr int EHT_R_HIGH_COUNT = 6;

} // namespace physics

#endif // PHYSICS_ELECTRON_TEMPERATURE_H
