/**
 * @file jet_physics.h
 * @brief Relativistic jet physics for supermassive black holes.
 *
 * Implements physics of relativistic jets launched from black hole systems:
 * - Blandford-Znajek mechanism (electromagnetic energy extraction)
 * - Jet collimation and opening angles
 * - Lorentz factors and bulk velocities
 * - Jet base positioning (EHT-constrained for M87)
 * - State-dependent jet power (MAD vs SANE)
 *
 * Key observations:
 * - M87 jet base: ~0.09 light-years from horizon (EHT Jan 2026)
 * - Sgr A*: Weak jets, Γ ~ 5-15
 * - M87: Powerful jets, Γ ~ 10-20
 * - Blazars: Highly relativistic, Γ up to 50
 *
 * References:
 * - Blandford & Znajek (1977), MNRAS 179, 433
 * - Tchekhovskoy et al. (2011), MNRAS 418, L79 (MAD jets)
 * - EHT Collaboration (2026), M87 jet base detection
 * - Narayan & McClintock (2012), MNRAS 419, L69 (ADAF jets)
 *
 * Cleanroom implementation based on standard astrophysics formulas.
 */

#ifndef PHYSICS_JET_PHYSICS_H
#define PHYSICS_JET_PHYSICS_H

#include "constants.h"
#include "kerr.h"
#include "mad_disk.h"
#include <cmath>
#include <algorithm>

namespace physics {

// ============================================================================
// Jet Parameters
// ============================================================================

/**
 * @brief Jet configuration parameters.
 */
struct JetParams {
  double mass;              ///< Black hole mass [g]
  double a;                 ///< Spin parameter [cm]
  double mdot;              ///< Accretion rate [g/s]
  AccretionState state;     ///< Accretion state (affects jet power)
  double magnetic_flux;     ///< Dimensionless magnetic flux Φ_BH

  // Jet properties
  double lorentz_factor;    ///< Bulk Lorentz factor Γ
  double opening_angle;     ///< Half-opening angle [rad]
  double base_distance;     ///< Distance of jet base from horizon [cm]
};

/**
 * @brief Create jet parameters for M87.
 *
 * Based on EHT observations (Jan 2026).
 *
 * @param a_star Dimensionless spin (~0.9 from EHT)
 * @param mdot_edd Accretion rate in Eddington units (~0.001)
 * @return JetParams
 */
inline JetParams m87_jet(double a_star = 0.9, double mdot_edd = 0.001) {
  JetParams jet;

  // M87* mass: ~6.5 billion solar masses
  double M_solar = 6.5e9;
  jet.mass = M_solar * M_SUN;

  // Spin
  double M_geo = G * jet.mass / C2;
  jet.a = a_star * M_geo;

  // Low accretion rate
  double L_edd = 1.26e38 * M_solar;
  jet.mdot = mdot_edd * L_edd / (0.1 * C2);

  // MAD state (favored by EHT observations)
  jet.state = AccretionState::MAD;
  jet.magnetic_flux = 50.0;

  // Jet properties
  jet.lorentz_factor = 15.0;  // Γ ~ 10-20 for M87
  jet.opening_angle = 10.0 * (PI / 180.0);  // ~10 degrees

  // Jet base: 0.09 light-years = 8.5×10^17 cm
  jet.base_distance = 0.09 * 9.461e17;  // Convert ly to cm

  return jet;
}

/**
 * @brief Create jet parameters for Sgr A*.
 *
 * @param a_star Dimensionless spin (0.94 from EHT-GRMHD)
 * @param mdot_edd Accretion rate (~10^-5 for Sgr A*)
 * @return JetParams
 */
inline JetParams sgr_a_star_jet(double a_star = 0.94, double mdot_edd = 1e-5) {
  JetParams jet;

  // Sgr A* mass: 4.3 million solar masses
  double M_solar = 4.3e6;
  jet.mass = M_solar * M_SUN;

  // High spin (EHT-constrained)
  double M_geo = G * jet.mass / C2;
  jet.a = a_star * M_geo;

  // Very low accretion rate
  double L_edd = 1.26e38 * M_solar;
  jet.mdot = mdot_edd * L_edd / (0.1 * C2);

  // MAD state
  jet.state = AccretionState::MAD;
  jet.magnetic_flux = 50.0;

  // Weaker jets than M87
  jet.lorentz_factor = 10.0;  // Γ ~ 5-15
  jet.opening_angle = 15.0 * (PI / 180.0);  // ~15 degrees

  // Jet base closer to horizon (smaller mass)
  jet.base_distance = 0.01 * 9.461e17;  // ~0.01 ly

  return jet;
}

// ============================================================================
// Blandford-Znajek Mechanism
// ============================================================================

/**
 * @brief Compute horizon angular velocity.
 *
 * Ω_H = a / (2 M r_+)
 *
 * where r_+ is the outer horizon radius.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Angular velocity [rad/s]
 */
inline double horizon_angular_velocity(double mass, double a) {
  double r_plus = kerr_outer_horizon(mass, a);
  double M_geo = G * mass / C2;

  // Ω_H in geometric units
  double omega_geom = a / (2.0 * M_geo * r_plus);

  // Convert to physical units [rad/s]
  return omega_geom * C / M_geo;
}

/**
 * @brief Estimate magnetic field at horizon for BZ mechanism.
 *
 * B_H ~ sqrt(8π ρ v²) where ρ is gas density near horizon.
 *
 * For MAD state, magnetic pressure ~ gas pressure.
 *
 * @param jet Jet parameters
 * @return Magnetic field at horizon [Gauss]
 */
inline double horizon_magnetic_field(const JetParams &jet) {
  double r_plus = kerr_outer_horizon(jet.mass, jet.a);

  // Gas density near horizon (rough estimate)
  // ρ ~ Ṁ / (4π r² v) where v ~ c
  double rho = jet.mdot / (FOUR_PI * r_plus * r_plus * C);

  // For MAD: P_mag ~ P_gas ~ ρ c²
  double P_mag = rho * C2;

  // B = sqrt(8π P_mag)
  double B = std::sqrt(8.0 * PI * P_mag);

  // MAD state has stronger fields
  if (jet.state == AccretionState::MAD) {
    B *= 2.0;  // Enhancement factor
  }

  return B;
}

/**
 * @brief Compute Blandford-Znajek power.
 *
 * P_BZ ~ (B_H² r_+² c / 4π) Ω_H² f(a*)
 *
 * where f(a*) is a spin-dependent factor.
 *
 * Normalized form:
 * P_BZ / (Ṁ c²) = η_BZ ~ 0.01 to 0.4
 *
 * @param jet Jet parameters
 * @return Jet power [erg/s]
 */
inline double blandford_znajek_power(const JetParams &jet) {
  double r_plus = kerr_outer_horizon(jet.mass, jet.a);
  double M_geo = G * jet.mass / C2;
  double a_star = jet.a / M_geo;

  // Horizon angular velocity
  double Omega_H = horizon_angular_velocity(jet.mass, jet.a);

  // Magnetic field at horizon
  double B_H = horizon_magnetic_field(jet);

  // BZ power formula
  // P_BZ ~ (B_H² r_+² c / 4π) Ω_H² for a* ~ 1
  double power_prefactor = (B_H * B_H * r_plus * r_plus * C) / FOUR_PI;
  double omega_factor = Omega_H * Omega_H;

  // Spin-dependent enhancement: f(a*) ~ a*² for near-extremal
  double spin_factor = a_star * a_star;

  double P_BZ = power_prefactor * omega_factor * spin_factor;

  // For MAD state, efficiency can be higher
  if (jet.state == AccretionState::MAD) {
    P_BZ *= 2.0;  // MAD enhancement
  }

  return P_BZ;
}

/**
 * @brief Compute jet efficiency η = P_jet / (Ṁ c²).
 *
 * @param jet Jet parameters
 * @return Efficiency (0 to ~0.4)
 */
inline double jet_efficiency(const JetParams &jet) {
  double P_jet = blandford_znajek_power(jet);
  double P_accretion = jet.mdot * C2;

  double eta = P_jet / P_accretion;

  // Clamp to physical range
  return std::clamp(eta, 0.0, 0.4);
}

// ============================================================================
// Jet Geometry
// ============================================================================

/**
 * @brief Compute jet opening angle (state-dependent).
 *
 * MAD jets are more collimated due to strong magnetic fields.
 *
 * @param jet Jet parameters
 * @return Half-opening angle [rad]
 */
inline double jet_opening_angle(const JetParams &jet) {
  // Base opening angle
  double theta = jet.opening_angle;

  // MAD jets are more collimated
  if (jet.state == AccretionState::MAD) {
    theta *= 0.7;  // 30% narrower
  } else if (jet.state == AccretionState::SANE) {
    theta *= 1.3;  // 30% wider
  }

  return theta;
}

/**
 * @brief Check if a point is inside the jet cone.
 *
 * @param r Radius from black hole [cm]
 * @param theta Polar angle from jet axis [rad]
 * @param jet Jet parameters
 * @return true if inside jet
 */
inline bool is_inside_jet(double r, double theta, const JetParams &jet) {
  // Jet only exists above base distance
  if (r < jet.base_distance) {
    return false;
  }

  // Conical jet
  double half_angle = jet_opening_angle(jet);

  return (theta < half_angle) || (theta > (PI - half_angle));
}

/**
 * @brief Compute jet velocity at distance r.
 *
 * Jets accelerate from sub-relativistic at base to highly
 * relativistic at large distances.
 *
 * @param r Distance from black hole [cm]
 * @param jet Jet parameters
 * @return Lorentz factor Γ(r)
 */
inline double jet_lorentz_factor_at_radius(double r, const JetParams &jet) {
  // Acceleration scale: ~10 times horizon radius
  double r_plus = kerr_outer_horizon(jet.mass, jet.a);
  double r_accel = 10.0 * r_plus;

  // At base: Γ ~ 2 (mildly relativistic)
  // At large r: Γ → Γ_∞ (terminal Lorentz factor)
  double Gamma_base = 2.0;
  double Gamma_inf = jet.lorentz_factor;

  // Smooth acceleration profile
  double x = (r - jet.base_distance) / r_accel;
  double Gamma = Gamma_base + (Gamma_inf - Gamma_base) * std::tanh(x);

  return Gamma;
}

/**
 * @brief Compute jet velocity β = v/c.
 *
 * β = sqrt(1 - 1/Γ²)
 *
 * @param Gamma Lorentz factor
 * @return Velocity in units of c
 */
inline double lorentz_to_beta(double Gamma) {
  if (Gamma <= 1.0) return 0.0;
  return std::sqrt(1.0 - 1.0 / (Gamma * Gamma));
}

/**
 * @brief Compute Doppler beaming factor.
 *
 * δ = 1 / (Γ(1 - β cos θ_obs))
 *
 * @param Gamma Lorentz factor
 * @param theta_obs Viewing angle [rad]
 * @return Doppler factor
 */
inline double jet_doppler_factor(double Gamma, double theta_obs) {
  double beta = lorentz_to_beta(Gamma);
  double cos_theta = std::cos(theta_obs);

  return 1.0 / (Gamma * (1.0 - beta * cos_theta));
}

// ============================================================================
// Jet Emission
// ============================================================================

/**
 * @brief Compute synchrotron emissivity in jet.
 *
 * j_ν ∝ n_e B^(p+1)/2 ν^(-(p-1)/2)
 *
 * where n_e is electron density, B is magnetic field, p is power-law index.
 *
 * @param r Radius [cm]
 * @param theta Polar angle [rad]
 * @param nu Frequency [Hz]
 * @param jet Jet parameters
 * @return Emissivity [erg/(s cm³ Hz sr)]
 */
inline double jet_synchrotron_emissivity(double r, double theta, double nu, const JetParams &jet) {
  if (!is_inside_jet(r, theta, jet)) {
    return 0.0;
  }

  // Magnetic field in jet (decreases with distance)
  double r_plus = kerr_outer_horizon(jet.mass, jet.a);
  double B_base = horizon_magnetic_field(jet);
  double B = B_base * (r_plus / r);  // B ∝ 1/r

  // Electron density (decreases as jet expands)
  double n_e_base = jet.mdot / (FOUR_PI * r_plus * r_plus * C * 9.109e-28);  // Rough estimate
  double n_e = n_e_base * (r_plus * r_plus) / (r * r);  // n ∝ 1/r²

  // Power-law index
  double p = 2.5;  // Typical non-thermal
  double alpha = (p - 1.0) / 2.0;

  // Synchrotron emissivity (simplified)
  double j_nu = n_e * std::pow(B, (p + 1.0) / 2.0) * std::pow(nu, -alpha);

  // Normalization constant (order of magnitude)
  j_nu *= 1.0e-20;

  return j_nu;
}

/**
 * @brief Compute observed flux from jet including Doppler boosting.
 *
 * F_obs = F_emit * δ^(3+α)
 *
 * @param r Radius [cm]
 * @param theta Polar angle [rad]
 * @param theta_obs Viewing angle [rad]
 * @param nu Frequency [Hz]
 * @param jet Jet parameters
 * @return Observed flux
 */
inline double jet_observed_flux(double r, double theta, double theta_obs,
                                double nu, const JetParams &jet) {
  // Intrinsic emissivity
  double F_emit = jet_synchrotron_emissivity(r, theta, nu, jet);

  // Lorentz factor at this radius
  double Gamma = jet_lorentz_factor_at_radius(r, jet);

  // Doppler factor
  double delta = jet_doppler_factor(Gamma, theta_obs);

  // Spectral index
  double alpha = 0.7;

  // Doppler boosting: F_obs = F_emit * δ^(3+α)
  double boost = std::pow(delta, 3.0 + alpha);

  return F_emit * boost;
}

// ============================================================================
// Jet Structure Visualization
// ============================================================================

/**
 * @brief Jet structure point for visualization.
 */
struct JetStructurePoint {
  double r;              ///< Distance from BH [cm]
  double theta;          ///< Polar angle [rad]
  double lorentz_factor; ///< Local Γ
  double beta;           ///< Local β = v/c
  double emissivity;     ///< Synchrotron emissivity
  double B_field;        ///< Magnetic field [Gauss]
};

/**
 * @brief Generate jet structure profile along axis.
 *
 * @param jet Jet parameters
 * @param n_points Number of points
 * @return Vector of structure points
 */
inline std::vector<JetStructurePoint> jet_structure_profile(const JetParams &jet, int n_points = 100) {
  std::vector<JetStructurePoint> profile;
  profile.reserve(static_cast<std::size_t>(n_points));

  double r_plus = kerr_outer_horizon(jet.mass, jet.a);
  double r_min = jet.base_distance;
  double r_max = r_min * 1000.0;  // Extend to 1000× base distance

  double log_r_min = std::log(r_min);
  double log_r_max = std::log(r_max);
  double d_log_r = (log_r_max - log_r_min) / (n_points - 1);

  for (int i = 0; i < n_points; ++i) {
    JetStructurePoint pt;
    pt.r = std::exp(log_r_min + i * d_log_r);
    pt.theta = 0.0;  // Along axis

    pt.lorentz_factor = jet_lorentz_factor_at_radius(pt.r, jet);
    pt.beta = lorentz_to_beta(pt.lorentz_factor);

    // Magnetic field
    double B_base = horizon_magnetic_field(jet);
    pt.B_field = B_base * (r_plus / pt.r);

    // Emissivity at 230 GHz
    pt.emissivity = jet_synchrotron_emissivity(pt.r, pt.theta, 230.0e9, jet);

    profile.push_back(pt);
  }

  return profile;
}

} // namespace physics

#endif // PHYSICS_JET_PHYSICS_H
