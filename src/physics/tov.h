/**
 * @file tov.h
 * @brief Tolman-Oppenheimer-Volkoff equation for relativistic stellar structure.
 *
 * The TOV equation describes hydrostatic equilibrium for spherically symmetric,
 * static, relativistic stars:
 *
 *   dP/dr = -(G/c²) * (ρ + P/c²) * (m + 4πr³P/c²) / (r(r - 2Gm/c²))
 *   dm/dr = 4πr²ρ
 *
 * Combined with an equation of state P(ρ), this determines:
 * - Neutron star mass-radius relation
 * - Maximum mass (TOV limit ~2-3 M☉)
 * - Central density for given mass
 *
 * References:
 * - Tolman (1939), Oppenheimer & Volkoff (1939)
 * - Shapiro & Teukolsky "Black Holes, White Dwarfs, and Neutron Stars"
 *
 * Cleanroom implementation based on standard GR formulas.
 */

#ifndef PHYSICS_TOV_H
#define PHYSICS_TOV_H

#include "constants.h"
#include "safe_limits.h"
#include "schwarzschild.h"
#include <cmath>
#include <functional>
#include <vector>

namespace physics {

// ============================================================================
// Equation of State Interface
// ============================================================================

/**
 * @brief Equation of state: pressure as function of density.
 *
 * P = P(ρ) where ρ is rest-mass density [g/cm³]
 * Returns pressure [dyn/cm²] = [g/(cm·s²)]
 */
using EOS = std::function<double(double)>;

/**
 * @brief Polytropic equation of state.
 *
 * P = K * ρ^γ
 *
 * @param K Polytropic constant [cgs]
 * @param gamma Adiabatic index (>1)
 * @return EOS function
 */
inline EOS polytropic_eos(double K, double gamma) {
  return [K, gamma](double rho) -> double {
    if (rho <= 0)
      return 0.0;
    return K * std::pow(rho, gamma);
  };
}

/**
 * @brief Common polytrope parameters for neutron stars.
 *
 * SLy4-like: K ~ 3.6e13, γ ~ 3.0 (stiff)
 * APR4-like: K ~ 2.2e13, γ ~ 2.8 (moderate)
 */
namespace eos_params {
// Soft EOS (smaller maximum mass)
constexpr double K_SOFT = 1.0e13;
constexpr double GAMMA_SOFT = 2.5;

// Stiff EOS (larger maximum mass)
constexpr double K_STIFF = 5.0e13;
constexpr double GAMMA_STIFF = 3.0;

// SLy4 approximation (realistic)
constexpr double K_SLY4 = 3.6e13;
constexpr double GAMMA_SLY4 = 3.0;

// APR4 approximation
constexpr double K_APR4 = 2.2e13;
constexpr double GAMMA_APR4 = 2.8;
} // namespace eos_params

// ============================================================================
// TOV Structure
// ============================================================================

/**
 * @brief Result of TOV integration at a single radius.
 */
struct TOVPoint {
  double r;       ///< Radius [cm]
  double m;       ///< Enclosed mass [g]
  double P;       ///< Pressure [dyn/cm²]
  double rho;     ///< Density [g/cm³]
  double phi;     ///< Metric potential (for redshift)
};

/**
 * @brief Complete stellar profile from TOV integration.
 */
struct TOVProfile {
  std::vector<TOVPoint> points; ///< Radial profile
  double R;                     ///< Total radius [cm]
  double M;                     ///< Total mass [g]
  double rho_c;                 ///< Central density [g/cm³]
  double P_c;                   ///< Central pressure [dyn/cm²]
  double compactness;           ///< C = GM/(Rc²)
  double surface_redshift;      ///< z = 1/√(1-2C) - 1
};

// ============================================================================
// TOV Integration
// ============================================================================

/**
 * @brief Compute TOV right-hand side for dm/dr.
 *
 * dm/dr = 4πr²ρ
 */
inline double tov_dmdr(double r, double rho) {
  return 4.0 * M_PI * r * r * rho;
}

/**
 * @brief Compute TOV right-hand side for dP/dr.
 *
 * dP/dr = -(G/c²) * (ρ + P/c²) * (m + 4πr³P/c²) / (r(r - 2Gm/c²))
 *
 * Returns 0 at center (r=0) to avoid singularity.
 */
inline double tov_dPdr(double r, double m, double P, double rho) {
  if (r < 1e-10) {
    return 0.0; // Regular at center
  }

  double r_s = 2.0 * G * m / C2; // Schwarzschild radius of enclosed mass

  // Avoid singularity at r = r_s (shouldn't happen for stable stars)
  if (r <= r_s * 1.001) {
    return -safe_infinity<double>();
  }

  double G_over_c2 = G / C2;
  double rho_eff = rho + P / C2;             // Effective density
  double m_eff = m + 4.0 * M_PI * r * r * r * P / C2; // Effective mass

  double numerator = G_over_c2 * rho_eff * m_eff;
  double denominator = r * (r - r_s);

  return -numerator / denominator;
}

/**
 * @brief Inverse EOS: density from pressure.
 *
 * For polytrope: ρ = (P/K)^(1/γ)
 *
 * @param P Pressure [dyn/cm²]
 * @param K Polytropic constant
 * @param gamma Adiabatic index
 * @return Density [g/cm³]
 */
inline double inverse_polytrope(double P, double K, double gamma) {
  if (P <= 0)
    return 0.0;
  return std::pow(P / K, 1.0 / gamma);
}

/**
 * @brief Integrate TOV equations from center to surface.
 *
 * Uses 4th-order Runge-Kutta with adaptive step size.
 *
 * @param rho_c Central density [g/cm³]
 * @param eos Equation of state P(ρ)
 * @param K Polytropic constant (for inverse EOS)
 * @param gamma Adiabatic index (for inverse EOS)
 * @param dr_init Initial step size [cm]
 * @param max_steps Maximum integration steps
 * @return TOV profile, or empty if integration fails
 */
inline TOVProfile integrate_tov(double rho_c, const EOS &eos, double K, double gamma,
                                double dr_init = 1e3, int max_steps = 100000) {
  TOVProfile profile;
  profile.rho_c = rho_c;
  profile.P_c = eos(rho_c);

  // Initial conditions at center
  double r = dr_init;
  double P = profile.P_c;
  double m = (4.0 / 3.0) * M_PI * rho_c * r * r * r; // Central mass

  double dr = dr_init;

  for (int step = 0; step < max_steps; ++step) {
    // Get density from pressure via inverse EOS
    double rho = inverse_polytrope(P, K, gamma);

    // Store point
    TOVPoint pt;
    pt.r = r;
    pt.m = m;
    pt.P = P;
    pt.rho = rho;
    profile.points.push_back(pt);

    // Check for surface (P → 0)
    if (P < 1e-10 * profile.P_c || rho < 1e-10 * rho_c) {
      break;
    }

    // RK4 integration
    double rho1 = rho;
    double k1_m = tov_dmdr(r, rho1);
    double k1_P = tov_dPdr(r, m, P, rho1);

    double rho2 = inverse_polytrope(P + 0.5 * dr * k1_P, K, gamma);
    double k2_m = tov_dmdr(r + 0.5 * dr, rho2);
    double k2_P = tov_dPdr(r + 0.5 * dr, m + 0.5 * dr * k1_m, P + 0.5 * dr * k1_P, rho2);

    double rho3 = inverse_polytrope(P + 0.5 * dr * k2_P, K, gamma);
    double k3_m = tov_dmdr(r + 0.5 * dr, rho3);
    double k3_P = tov_dPdr(r + 0.5 * dr, m + 0.5 * dr * k2_m, P + 0.5 * dr * k2_P, rho3);

    double rho4 = inverse_polytrope(P + dr * k3_P, K, gamma);
    double k4_m = tov_dmdr(r + dr, rho4);
    double k4_P = tov_dPdr(r + dr, m + dr * k3_m, P + dr * k3_P, rho4);

    // Update
    m += (dr / 6.0) * (k1_m + 2.0 * k2_m + 2.0 * k3_m + k4_m);
    P += (dr / 6.0) * (k1_P + 2.0 * k2_P + 2.0 * k3_P + k4_P);
    r += dr;

    // Pressure must decrease monotonically
    if (P < 0) {
      P = 0;
      break;
    }

    // Adaptive step size (smaller near surface)
    if (P < 0.01 * profile.P_c) {
      dr = std::max(dr * 0.5, 100.0); // Minimum 100 cm
    }
  }

  // Final values
  profile.R = r;
  profile.M = m;
  profile.compactness = G * m / (profile.R * C2);
  profile.surface_redshift = 1.0 / std::sqrt(1.0 - 2.0 * profile.compactness) - 1.0;

  return profile;
}

// ============================================================================
// Tidal Deformability (for Gravitational Waves)
// ============================================================================

/**
 * @brief Compute tidal Love number k₂.
 *
 * Uses the Hinderer (2008) fitting formula as approximation:
 * k₂ ≈ 0.05 + 0.1(1 - 5C), clamped to [0, 0.15]
 *
 * For exact calculation, need to integrate tidal perturbation equations.
 *
 * @param compactness C = GM/(Rc²)
 * @return Tidal Love number k₂
 */
inline double tidal_love_number_k2(double compactness) {
  // Yagi & Yunes (2013) fitting formula (approximate)
  double k2 = 0.05 + 0.1 * (1.0 - 5.0 * compactness);
  return std::clamp(k2, 0.0, 0.15);
}

/**
 * @brief Compute dimensionless tidal deformability Λ.
 *
 * Λ = (2/3) * k₂ / C⁵
 *
 * This is the key observable for binary neutron star mergers (GW170817).
 *
 * @param compactness C = GM/(Rc²)
 * @return Dimensionless tidal deformability Λ
 */
inline double tidal_deformability(double compactness) {
  double k2 = tidal_love_number_k2(compactness);
  double C5 = std::pow(compactness, 5);
  if (C5 < 1e-30)
    return 0.0;
  return (2.0 / 3.0) * k2 / C5;
}

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * @brief Compute neutron star for given central density with SLy4 EOS.
 */
inline TOVProfile neutron_star_sly4(double rho_c) {
  auto eos = polytropic_eos(eos_params::K_SLY4, eos_params::GAMMA_SLY4);
  return integrate_tov(rho_c, eos, eos_params::K_SLY4, eos_params::GAMMA_SLY4);
}

/**
 * @brief Compute maximum mass for given EOS.
 *
 * Scans central density to find the turning point (dM/dρ_c = 0).
 */
inline double tov_maximum_mass(double K, double gamma,
                               double rho_min = 1e14, double rho_max = 2e15,
                               int n_samples = 50) {
  auto eos = polytropic_eos(K, gamma);
  double max_mass = 0;

  double log_rho_min = std::log10(rho_min);
  double log_rho_max = std::log10(rho_max);
  double d_log_rho = (log_rho_max - log_rho_min) / n_samples;

  for (int i = 0; i <= n_samples; ++i) {
    double rho_c = std::pow(10.0, log_rho_min + i * d_log_rho);
    auto profile = integrate_tov(rho_c, eos, K, gamma);
    if (profile.M > max_mass) {
      max_mass = profile.M;
    }
  }

  return max_mass;
}

} // namespace physics

#endif // PHYSICS_TOV_H
