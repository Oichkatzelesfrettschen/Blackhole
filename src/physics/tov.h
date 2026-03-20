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
#include <algorithm>
#include <cmath>
#include <functional>
#include <numbers>
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
[[nodiscard]] inline EOS polytropicEos(double k, double gamma) {
  return [k, gamma](double rho) -> double {
    if (rho <= 0) {
      return 0.0;
    }
    return k * std::pow(rho, gamma);
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
  double r{};     ///< Radius [cm]
  double m{};     ///< Enclosed mass [g]
  double press{}; ///< Pressure [dyn/cm^2]
  double rho{};   ///< Density [g/cm^3]
  double phi{};   ///< Metric potential (for redshift)
};

/**
 * @brief Complete stellar profile from TOV integration.
 */
struct TOVProfile {
  std::vector<TOVPoint> points; ///< Radial profile
  double rSurface{};            ///< Total radius [cm]
  double mTotal{};              ///< Total mass [g]
  double rhoCenter{};           ///< Central density [g/cm^3]
  double pCenter{};             ///< Central pressure [dyn/cm^2]
  double compactness{};         ///< C = GM/(Rc^2)
  double surfaceRedshift{};     ///< z = 1/sqrt(1-2C) - 1
};

// ============================================================================
// TOV Integration
// ============================================================================

/**
 * @brief Compute TOV right-hand side for dm/dr.
 *
 * dm/dr = 4πr²ρ
 */
[[nodiscard]] inline double tovDmdr(double r, double rho) {
  return 4.0 * std::numbers::pi * r * r * rho;
}

/**
 * @brief Compute TOV right-hand side for dP/dr.
 *
 * dP/dr = -(G/c²) * (ρ + P/c²) * (m + 4πr³P/c²) / (r(r - 2Gm/c²))
 *
 * Returns 0 at center (r=0) to avoid singularity.
 */
[[nodiscard]] inline double tovDPdr(double r, double m, double press, double rho) {
  if (r < 1e-10) {
    return 0.0; // Regular at center
  }

  const double rS = (2.0 * G * m) / C2; // Schwarzschild radius of enclosed mass

  // Avoid singularity at r = rS (shouldn't happen for stable stars)
  if (r <= (rS * 1.001)) {
    return -safeInfinity<double>();
  }

  const double gOverC2 = G / C2;
  const double rhoEff = rho + (press / C2);                                        // Effective density
  const double mEff = m + ((4.0 * std::numbers::pi * r * r * r * press) / C2);    // Effective mass

  const double numerator = gOverC2 * rhoEff * mEff;
  const double denominator = r * (r - rS);

  return -(numerator / denominator);
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
[[nodiscard]] inline double inversePolytrope(double press, double k, double gamma) {
  if (press <= 0) {
    return 0.0;
  }
  return std::pow(press / k, 1.0 / gamma);
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
[[nodiscard]] inline TOVProfile integrateTov(double rhoC, const EOS &eos, double k, double gamma,
                                             double drInit = 1e3, int maxSteps = 100000) {
  TOVProfile profile;
  profile.rhoCenter = rhoC;
  profile.pCenter = eos(rhoC);

  // Initial conditions at center
  double r = drInit;
  double press = profile.pCenter;
  double m = ((4.0 / 3.0) * std::numbers::pi * rhoC * r * r * r); // Central mass

  double dr = drInit;

  for (int step = 0; step < maxSteps; ++step) {
    // Get density from pressure via inverse EOS
    const double rho = inversePolytrope(press, k, gamma);

    // Store point
    TOVPoint pt;
    pt.r = r;
    pt.m = m;
    pt.press = press;
    pt.rho = rho;
    profile.points.push_back(pt);

    // Check for surface (press -> 0)
    if ((press < (1e-10 * profile.pCenter)) || (rho < (1e-10 * rhoC))) {
      break;
    }

    // RK4 integration
    const double rho1 = rho;
    const double k1M = tovDmdr(r, rho1);
    const double k1P = tovDPdr(r, m, press, rho1);

    const double rho2 = inversePolytrope(press + (0.5 * dr * k1P), k, gamma);
    const double k2M = tovDmdr(r + (0.5 * dr), rho2);
    const double k2P = tovDPdr(r + (0.5 * dr), m + (0.5 * dr * k1M), press + (0.5 * dr * k1P), rho2);

    const double rho3 = inversePolytrope(press + (0.5 * dr * k2P), k, gamma);
    const double k3M = tovDmdr(r + (0.5 * dr), rho3);
    const double k3P = tovDPdr(r + (0.5 * dr), m + (0.5 * dr * k2M), press + (0.5 * dr * k2P), rho3);

    const double rho4 = inversePolytrope(press + (dr * k3P), k, gamma);
    const double k4M = tovDmdr(r + dr, rho4);
    const double k4P = tovDPdr(r + dr, m + (dr * k3M), press + (dr * k3P), rho4);

    // Update
    m     += (dr / 6.0) * (k1M + (2.0 * k2M) + (2.0 * k3M) + k4M);
    press += (dr / 6.0) * (k1P + (2.0 * k2P) + (2.0 * k3P) + k4P);
    r     += dr;

    // Pressure must decrease monotonically
    if (press < 0) {
      press = 0; // NOLINT(clang-analyzer-deadcode.DeadStores) -- clamp before break for clarity
      break;
    }

    // Adaptive step size (smaller near surface)
    if (press < (0.01 * profile.pCenter)) {
      dr = std::max(dr * 0.5, 100.0); // Minimum 100 cm
    }
  }

  // Final values
  profile.rSurface = r;
  profile.mTotal = m;
  profile.compactness = (G * m) / (profile.rSurface * C2);
  profile.surfaceRedshift = (1.0 / std::sqrt(1.0 - (2.0 * profile.compactness))) - 1.0;

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
[[nodiscard]] inline double tidalLoveNumberK2(double compactness) {
  // Yagi & Yunes (2013) fitting formula (approximate)
  const double k2 = 0.05 + (0.1 * (1.0 - (5.0 * compactness)));
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
[[nodiscard]] inline double tidalDeformability(double compactness) {
  const double k2 = tidalLoveNumberK2(compactness);
  const double c5 = std::pow(compactness, 5);
  if (c5 < 1e-30) {
    return 0.0;
  }
  return ((2.0 / 3.0) * k2) / c5;
}

// ============================================================================
// Convenience Functions
// ============================================================================

/**
 * @brief Compute neutron star for given central density with SLy4 EOS.
 */
[[nodiscard]] inline TOVProfile neutronStarSly4(double rhoC) {
  const auto eos = polytropicEos(eos_params::K_SLY4, eos_params::GAMMA_SLY4);
  return integrateTov(rhoC, eos, eos_params::K_SLY4, eos_params::GAMMA_SLY4);
}

/**
 * @brief Compute maximum mass for given EOS.
 *
 * Scans central density to find the turning point (dM/dρ_c = 0).
 */
[[nodiscard]] inline double tovMaximumMass(double k, double gamma, double rhoMin = 1e14,
                                           double rhoMax = 2e15, int nSamples = 50) {
  const auto eos = polytropicEos(k, gamma);
  double maxMass = 0;

  const double logRhoMin = std::log10(rhoMin);
  const double logRhoMax = std::log10(rhoMax);
  const double dLogRho = (logRhoMax - logRhoMin) / nSamples;

  for (int i = 0; i <= nSamples; ++i) {
    const double rhoC = std::pow(10.0, logRhoMin + (i * dLogRho));
    const auto profile = integrateTov(rhoC, eos, k, gamma);
    maxMass = std::max(profile.mTotal, maxMass);
  }

  return maxMass;
}

} // namespace physics

#endif // PHYSICS_TOV_H
