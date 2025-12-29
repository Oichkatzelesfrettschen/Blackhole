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

#include "constants.h"
#include "kerr.h"
#include <cmath>
#include <limits>

namespace physics {

// ============================================================================
// Penrose Process Energy Extraction
// ============================================================================

/**
 * @brief Result of Penrose process calculation.
 */
struct PenroseResult {
  double E_in;        ///< Input particle energy
  double E_out;       ///< Output (escaping) particle energy
  double E_absorbed;  ///< Energy absorbed by black hole (can be negative!)
  double efficiency;  ///< Extraction efficiency (E_out - E_in) / E_in
  bool successful;    ///< Whether extraction was possible
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
 * @param E_in Input particle energy at infinity
 * @param L_in Input particle angular momentum
 * @return PenroseResult with extraction details
 */
inline PenroseResult penrose_process_energy_extraction(const Kerr &kerr,
                                                        double E_in,
                                                        double L_in) {
  PenroseResult result;
  result.E_in = E_in;
  result.successful = false;

  double a = kerr.spin();
  double M = G * kerr.mass() / C2; // Geometric mass
  double a_star = kerr.dimensionless_spin();

  // Check if spin is sufficient for Penrose process
  if (std::abs(a_star) < 1e-10) {
    // Schwarzschild: no ergosphere, no Penrose process
    result.E_out = E_in;
    result.E_absorbed = 0;
    result.efficiency = 0;
    return result;
  }

  // Maximum energy extractable is limited by irreducible mass
  // M_irr = M × √((1 + √(1 - a*²))/2)
  double sqrt_factor = std::sqrt(1.0 - a_star * a_star);
  double M_irr_ratio = std::sqrt((1.0 + sqrt_factor) / 2.0);

  // Energy extractable: E_rot = M - M_irr = M × (1 - M_irr_ratio)
  double E_rot_fraction = 1.0 - M_irr_ratio;

  // Simplified model: assume optimal split in ergosphere
  // The escaping particle gets the input energy plus some rotational energy
  // Maximum efficiency for single split is about 20.7% (a* = 1)

  // For given angular momentum, compute extraction
  double omega_H = a_star * C / (2.0 * kerr.outer_horizon()); // Horizon angular velocity

  // Condition for negative energy: L > E/ω_H
  // Energy that can be extracted: ΔE = ω_H × ΔL - E_absorbed

  // Simple efficiency model based on spin
  double eta = 0.5 * a_star * a_star * E_rot_fraction;

  result.E_out = E_in * (1.0 + eta);
  result.E_absorbed = -E_in * eta; // Negative energy absorbed
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
 * @param a_star Dimensionless spin parameter |a*| ≤ 1
 * @return Maximum efficiency (0 to ~0.293)
 */
inline double penrose_maximum_efficiency(double a_star) {
  a_star = std::clamp(std::abs(a_star), 0.0, 1.0);
  double sqrt_factor = std::sqrt(1.0 - a_star * a_star);
  return 1.0 - std::sqrt((1.0 + sqrt_factor) / 2.0);
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
 * @param a_star Dimensionless spin
 * @return Irreducible mass [g]
 */
inline double irreducible_mass(double mass, double a_star) {
  a_star = std::clamp(std::abs(a_star), 0.0, 1.0);
  double sqrt_factor = std::sqrt(1.0 - a_star * a_star);
  return mass * std::sqrt((1.0 + sqrt_factor) / 2.0);
}

/**
 * @brief Compute rotational energy of Kerr black hole.
 *
 * E_rot = M - M_irr = M × (1 - √((1 + √(1 - a*²))/2))
 *
 * This is the maximum energy extractable via the Penrose process.
 *
 * @param mass Black hole mass [g]
 * @param a_star Dimensionless spin
 * @return Rotational energy [erg]
 */
inline double rotational_energy(double mass, double a_star) {
  double M_irr = irreducible_mass(mass, a_star);
  return (mass - M_irr) * C2;
}

// ============================================================================
// Horizon Angular Velocity
// ============================================================================

/**
 * @brief Compute angular velocity of the event horizon.
 *
 * Ω_H = a/(r_+² + a²) where r_+ is outer horizon
 *
 * For a* → 1: Ω_H → c/(2M)
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Horizon angular velocity [rad/s]
 */
inline double horizon_angular_velocity(double mass, double a) {
  Kerr kerr(mass, a);
  double r_plus = kerr.outer_horizon();
  return a * C / (r_plus * r_plus + a * a);
}

/**
 * @brief Compute horizon surface area.
 *
 * A = 4π(r_+² + a²) = 8π M r_+
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Horizon area [cm²]
 */
inline double horizon_area(double mass, double a) {
  Kerr kerr(mass, a);
  double r_plus = kerr.outer_horizon();
  return 4.0 * PI * (r_plus * r_plus + a * a);
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
 * @param a_star Dimensionless spin
 * @param B_field Magnetic field strength at horizon [Gauss]
 * @return Power output [erg/s]
 */
inline double blandford_znajek_power(double mass, double a_star, double B_field) {
  a_star = std::clamp(std::abs(a_star), 0.0, 0.998);

  double M = G * mass / C2; // Geometric mass [cm]
  double r_plus = M * (1.0 + std::sqrt(1.0 - a_star * a_star));

  // Blandford-Znajek formula with Tchekhovskoy et al. correction
  // P ≈ (κ/4π c) × Φ² × Ω_H² × f(Ω_H)
  // Simplified: P ∝ B² r_+² c a*²

  double Phi_squared = B_field * B_field * PI * r_plus * r_plus; // Magnetic flux squared
  double omega_H = a_star * C / (2.0 * r_plus);

  // Numerical factor from simulations (Tchekhovskoy+2010)
  double kappa = 0.05;

  double P_BZ = kappa * Phi_squared * omega_H * omega_H / C;

  return P_BZ;
}

/**
 * @brief Estimate magnetic field for Eddington-limited BZ power.
 *
 * For L_BZ = L_Edd, the required field is approximately:
 * B ∼ 10^4 × (M/M_sun)^(-1/2) Gauss
 *
 * @param mass Black hole mass [g]
 * @param a_star Dimensionless spin
 * @return Required magnetic field [Gauss]
 */
inline double bz_eddington_field(double mass, double a_star) {
  // Eddington luminosity: L_Edd = 4π G M m_p c / σ_T
  double L_Edd = 4.0 * PI * G * mass * 1.6726e-24 * C / SIGMA_THOMSON;

  // Invert BZ formula to find B
  double M_geo = G * mass / C2;
  double r_plus = M_geo * (1.0 + std::sqrt(1.0 - a_star * a_star));
  double omega_H = a_star * C / (2.0 * r_plus);

  if (std::abs(omega_H) < 1e-30) {
    return std::numeric_limits<double>::infinity();
  }

  double kappa = 0.05;
  double B_squared = L_Edd * C / (kappa * PI * r_plus * r_plus * omega_H * omega_H);

  return std::sqrt(B_squared);
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
inline bool is_superradiant(double omega, int m, double mass, double a) {
  double Omega_H = horizon_angular_velocity(mass, a);
  return omega < static_cast<double>(m) * Omega_H;
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
 * @param a_star Dimensionless spin
 * @return Amplification factor (1 = no amplification)
 */
inline double superradiant_amplification(double omega, int m,
                                          double mass, double a_star) {
  a_star = std::clamp(std::abs(a_star), 0.0, 0.998);

  double M = G * mass / C2;
  double r_plus = M * (1.0 + std::sqrt(1.0 - a_star * a_star));
  double Omega_H = a_star * C / (2.0 * r_plus);

  double m_omega_H = static_cast<double>(m) * Omega_H;

  if (omega >= m_omega_H) {
    return 1.0; // No superradiance
  }

  // Simplified amplification factor (exact requires solving Teukolsky equation)
  // Z ∝ (m Ω_H - ω) × (product of reflection coefficients)
  double superradiant_factor = (m_omega_H - omega) / m_omega_H;
  return 1.0 + 0.05 * superradiant_factor * a_star * a_star;
}

} // namespace physics

#endif // PHYSICS_PENROSE_H
