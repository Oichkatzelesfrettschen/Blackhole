/**
 * @file penrose.h
 * @brief Penrose process for energy extraction from rotating black holes.
 *
 * The Penrose process (1969) allows extraction of rotational energy
 * from a Kerr black hole's ergosphere. A particle entering the ergosphere
 * can split such that one fragment falls into the hole with negative
 * energy (as measured at infinity), while the other escapes with
 * more energy than the original particle.
 *
 * Key concepts:
 *   - Ergosphere: region between horizon and static limit
 *   - Static limit: where g_tt = 0, observers must co-rotate
 *   - Maximum efficiency: η_max = (1 - 1/√2) ≈ 29.3% for maximal spin
 *
 * Also includes Blandford-Znajek mechanism for electromagnetic
 * energy extraction from rotating black holes with magnetic fields.
 *
 * References:
 *   - Penrose (1969) "Gravitational Collapse: The Role of GR"
 *   - Blandford & Znajek (1977) MNRAS 179, 433
 *   - Chandrasekhar (1983) "Mathematical Theory of Black Holes"
 *
 * Cleanroom implementation based on standard GR formulas.
 */

#ifndef PHYSICS_PENROSE_H
#define PHYSICS_PENROSE_H

#include <cmath>

#include "constants.h"
#include "kerr.h"
#include "safe_limits.h"

namespace physics {

// ============================================================================
// Penrose Process Energy Extraction
// ============================================================================

/**
 * @brief Result of Penrose process calculation.
 */
struct PenroseResult {
  double eIn{};        ///< Input particle energy
  double eOut{};       ///< Output (escaping) particle energy
  double eAbsorbed{};  ///< Energy absorbed by black hole (can be negative!)
  double efficiency{}; ///< Extraction efficiency (eOut - eIn) / eIn
  bool successful{};   ///< Whether extraction was possible
};

/**
 * @brief Compute energy extraction via Penrose process.
 *
 * For a particle with energy E and angular momentum L at radius r,
 * the effective potential and binding energy determine whether
 * negative-energy orbits are possible.
 *
 * In the ergosphere, it's possible to have E < 0 (as measured at
 * infinity) while the particle has positive local energy.
 *
 * @param kerr Kerr black hole
 * @param eIn Input particle energy at infinity
 * @param lIn Input particle angular momentum
 * @return PenroseResult with extraction details
 */
[[nodiscard]] inline PenroseResult penroseProcessEnergyExtraction(const Kerr &kerr, double eIn,
                                                                  [[maybe_unused]] double lIn) {
  PenroseResult result;
  result.eIn = eIn;
  result.successful = false;

  const double aStar = kerr.dimensionlessSpin();

  // Check if spin is sufficient for Penrose process
  if (std::abs(aStar) < 1e-10) {
    // Schwarzschild: no ergosphere, no Penrose process
    result.eOut = eIn;
    result.eAbsorbed = 0;
    result.efficiency = 0;
    return result;
  }

  // Maximum energy extractable is limited by irreducible mass
  // M_irr = M * sqrt((1 + sqrt(1 - a*^2))/2)
  const double sqrtFactor = std::sqrt(1.0 - (aStar * aStar));
  const double mIrrRatio = std::sqrt((1.0 + sqrtFactor) / 2.0);

  // Energy extractable: E_rot = M - M_irr = M * (1 - mIrrRatio)
  const double eRotFraction = 1.0 - mIrrRatio;

  // Simple efficiency model based on spin
  const double eta = 0.5 * aStar * aStar * eRotFraction;

  result.eOut = eIn * (1.0 + eta);
  result.eAbsorbed = -(eIn * eta); // Negative energy absorbed
  result.efficiency = eta;
  result.successful = (eta > 0);

  return result;
}

/**
 * @brief Compute maximum Penrose process efficiency.
 *
 * For a maximally spinning black hole (a* = 1):
 * η_max = 1 - 1/√2 ≈ 0.293 (29.3%)
 *
 * For general spin:
 * η_max = 1 - √((1 + √(1 - a*²))/2)
 *
 * @param aStar Dimensionless spin parameter |a*| <= 1
 * @return Maximum efficiency (0 to ~0.293)
 */
[[nodiscard]] inline double penroseMaximumEfficiency(double aStar) {
  aStar = std::clamp(std::abs(aStar), 0.0, 1.0);
  const double sqrtFactor = std::sqrt(1.0 - (aStar * aStar));
  return 1.0 - std::sqrt((1.0 + sqrtFactor) / 2.0);
}

/**
 * @brief Compute irreducible mass of Kerr black hole.
 *
 * M_irr = √(A/(16π)) where A is horizon area
 * M_irr = M × √((1 + √(1 - a*²))/2)
 *
 * This mass cannot be reduced; it only increases.
 *
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin
 * @return Irreducible mass [g]
 */
[[nodiscard]] inline double irreducibleMass(double mass, double aStar) {
  aStar = std::clamp(std::abs(aStar), 0.0, 1.0);
  const double sqrtFactor = std::sqrt(1.0 - (aStar * aStar));
  return mass * std::sqrt((1.0 + sqrtFactor) / 2.0);
}

/**
 * @brief Compute rotational energy of Kerr black hole.
 *
 * E_rot = M - M_irr = M × (1 - √((1 + √(1 - a*²))/2))
 *
 * This is the maximum energy extractable via the Penrose process.
 *
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin
 * @return Rotational energy [erg]
 */
[[nodiscard]] inline double rotationalEnergy(double mass, double aStar) {
  const double mIrr = irreducibleMass(mass, aStar);
  return (mass - mIrr) * C2;
}

// ============================================================================
// Horizon Angular Velocity
// ============================================================================

// Penrose-process helper for the Kerr horizon angular velocity.
[[nodiscard]] inline double horizonAngularVelocity(double mass, double a) {
  const Kerr kerr(mass, a);
  const double rPlus = kerr.outerHorizon();
  return (a * C) / ((rPlus * rPlus) + (a * a));
}

/**
 * @brief Compute horizon surface area.
 *
 * A = 4π(r_+² + a²) = 8π M r_+
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Horizon area [cm^2]
 */
[[nodiscard]] inline double horizonArea(double mass, double a) {
  const Kerr kerr(mass, a);
  const double rPlus = kerr.outerHorizon();
  return 4.0 * PI * ((rPlus * rPlus) + (a * a));
}

// ============================================================================
// Blandford-Znajek Mechanism
// ============================================================================

/**
 * @brief Compute Blandford-Znajek power output.
 *
 * The BZ mechanism extracts rotational energy electromagnetically
 * via magnetic field lines threading the horizon.
 *
 * P_BZ ≈ (1/32) × (B² r_+² c) × a*² × f(a*)
 *
 * where f(a*) is a spin-dependent factor.
 *
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin
 * @param bField Magnetic field strength at horizon [Gauss]
 * @return Power output [erg/s]
 */
[[nodiscard]] inline double blandfordZnajekPower(double mass, double aStar, double bField) {
  aStar = std::clamp(std::abs(aStar), 0.0, 0.998);

  const double mGeo = G * mass / C2; // Geometric mass [cm]
  const double rPlus = mGeo * (1.0 + std::sqrt(1.0 - (aStar * aStar)));

  // Blandford-Znajek formula with Tchekhovskoy et al. correction
  // P ~ (kappa/4*pi*c) * Phi^2 * Omega_H^2 * f(Omega_H)
  // Simplified: P ~ B^2 r_+^2 c a*^2

  const double phiSquared = bField * bField * PI * rPlus * rPlus; // Magnetic flux squared
  const double omegaH = (aStar * C) / (2.0 * rPlus);

  // Numerical factor from simulations (Tchekhovskoy+2010)
  const double kappa = 0.05;

  return kappa * phiSquared * (omegaH * omegaH) / C;
}

/**
 * @brief Estimate magnetic field for Eddington-limited BZ power.
 *
 * For L_BZ = L_Edd, the required field is approximately:
 * B ∼ 10^4 × (M/M_sun)^(-1/2) Gauss
 *
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin
 * @return Required magnetic field [Gauss]
 */
[[nodiscard]] inline double bzEddingtonField(double mass, double aStar) {
  // Eddington luminosity: L_Edd = 4*pi*G*M*m_p*c / sigma_T
  const double lEdd = (4.0 * PI * G * mass * 1.6726e-24 * C) / SIGMA_THOMSON;

  // Invert BZ formula to find B
  const double mGeo = G * mass / C2;
  const double rPlus = mGeo * (1.0 + std::sqrt(1.0 - (aStar * aStar)));
  const double omegaH = (aStar * C) / (2.0 * rPlus);

  if (std::abs(omegaH) < 1e-30) {
    return safeInfinity<double>();
  }

  const double kappa = 0.05;
  const double bSquared = (lEdd * C) / (kappa * PI * rPlus * rPlus * omegaH * omegaH);

  return std::sqrt(bSquared);
}

// ============================================================================
// Superradiant Scattering
// ============================================================================

/**
 * @brief Check if frequency allows superradiant scattering.
 *
 * Waves with ω < m Ω_H (where m is azimuthal number) can extract
 * energy from a rotating black hole.
 *
 * @param omega Wave frequency [rad/s]
 * @param m Azimuthal mode number
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return true if superradiance is possible
 */
[[nodiscard]] inline bool isSuperradiant(double omega, int m, double mass, double a) {
  const double omegaH = horizonAngularVelocity(mass, a);
  return omega < (static_cast<double>(m) * omegaH);
}

/**
 * @brief Compute superradiant amplification factor.
 *
 * For scalar waves, maximum amplification is ~0.4% per scattering.
 * For gravitational waves, can be up to ~138% for extremal Kerr.
 *
 * @param omega Wave frequency [rad/s]
 * @param m Azimuthal mode number
 * @param mass Black hole mass [g]
 * @param aStar Dimensionless spin
 * @return Amplification factor (1 = no amplification)
 */
[[nodiscard]] inline double superradiantAmplification(double omega, int m, double mass,
                                                      double aStar) {
  aStar = std::clamp(std::abs(aStar), 0.0, 0.998);

  const double mGeo = G * mass / C2;
  const double rPlus = mGeo * (1.0 + std::sqrt(1.0 - (aStar * aStar)));
  const double omegaH = (aStar * C) / (2.0 * rPlus);

  const double mOmegaH = static_cast<double>(m) * omegaH;

  if (omega >= mOmegaH) {
    return 1.0; // No superradiance
  }

  // Simplified amplification factor (exact requires solving Teukolsky equation)
  const double superradiantFactor = (mOmegaH - omega) / mOmegaH;
  return 1.0 + (0.05 * superradiantFactor * aStar * aStar);
}

} // namespace physics

#endif // PHYSICS_PENROSE_H
