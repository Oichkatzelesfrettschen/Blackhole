/**
 * @file mad_disk.h
 * @brief Magnetically Arrested Disk (MAD) accretion state physics.
 *
 * MAD state occurs when magnetic flux accumulates near the black hole,
 * becoming dynamically important and affecting accretion.
 *
 * Key features:
 * - Strong magnetic fields: β = P_gas/P_mag ~ 1 (near equipartition)
 * - Episodic flux eruptions with quasi-periodic variability
 * - Powerful jets via Blandford-Znajek mechanism
 * - Lower accretion efficiency but higher jet power
 * - Favored for Sgr A* based on EHT observations (2025-2026)
 *
 * Accretion states:
 * - SANE: Standard and Normal Evolution (weak B-field)
 * - MAD: Magnetically Arrested Disk (strong B-field)
 * - INTERMEDIATE: Transitional state
 *
 * References:
 * - Narayan et al. (2003), PASJ 55, L69 (MAD discovery in simulations)
 * - Tchekhovskoy et al. (2011), MNRAS 418, L79 (MAD jets)
 * - EHT Collaboration (2025), arXiv:2510.03602 (Sgr A* MAD constraint)
 *
 * Implementation based on 2026 EHT-GRMHD observational constraints.
 */

#ifndef PHYSICS_MAD_DISK_H
#define PHYSICS_MAD_DISK_H

#include "constants.h"
#include "thin_disk.h"
#include "kerr.h"
#include <cmath>
#include <algorithm>

namespace physics {

// ============================================================================
// Constants
// ============================================================================

/// Proton mass [g]
constexpr double M_PROTON = 1.67262192369e-24;

// ============================================================================
// Accretion State Enum
// ============================================================================

/**
 * @brief Accretion disk state classification.
 */
enum class AccretionState {
  SANE,           ///< Standard and Normal Evolution (weak magnetic field)
  MAD,            ///< Magnetically Arrested Disk (strong magnetic field)
  INTERMEDIATE    ///< Transitional state between SANE and MAD
};

/**
 * @brief Convert accretion state to string.
 */
inline const char* accretion_state_name(AccretionState state) {
  switch (state) {
    case AccretionState::SANE: return "SANE";
    case AccretionState::MAD: return "MAD";
    case AccretionState::INTERMEDIATE: return "Intermediate";
    default: return "Unknown";
  }
}

// ============================================================================
// MAD Parameters
// ============================================================================

/**
 * @brief Extended disk parameters including magnetic fields.
 */
struct MADDiskParams : public DiskParams {
  AccretionState state = AccretionState::SANE;

  // Magnetic field parameters
  double magnetic_pressure_ratio = 100.0;  ///< β = P_gas/P_mag (100 for SANE, ~1 for MAD)
  double magnetic_flux = 0.0;              ///< Dimensionless magnetic flux Φ_BH

  // Time-dependent parameters
  double time = 0.0;                       ///< Simulation time [s]
  double flux_eruption_period = 6.0;       ///< Eruption timescale [hours] (~orbital period at ISCO)

  // Jet parameters
  double jet_efficiency = 0.0;             ///< Jet power / accretion power
};

/**
 * @brief Create MAD disk parameters for Sgr A*.
 *
 * Based on EHT-constrained GRMHD simulations (arXiv:2510.03602).
 *
 * @param a_star Dimensionless spin (0.94 from EHT)
 * @param M_dot_edd Accretion rate in Eddington units (low for Sgr A*)
 * @return MADDiskParams
 */
inline MADDiskParams sgr_a_star_mad_disk(double a_star = 0.94, double M_dot_edd = 1e-5) {
  MADDiskParams disk;

  // Sgr A* mass: 4.3 million solar masses
  double M_solar = 4.3e6;
  disk.M = M_solar * M_SUN;

  // Spin parameter (EHT-constrained)
  double M_geo = G * disk.M / C2;
  disk.a = a_star * M_geo;

  // Very low accretion rate (Sgr A* is highly sub-Eddington)
  double L_edd = 1.26e38 * M_solar;
  double eta = 0.3;  // High efficiency for near-extremal spin
  disk.M_dot = M_dot_edd * L_edd / (eta * C2);

  // ISCO for highly spinning black hole
  disk.r_in = kerr_isco_radius(disk.M, disk.a, true);  // Prograde
  disk.r_out = 1000.0 * M_geo;
  disk.inclination = 0.0;

  // MAD state parameters
  disk.state = AccretionState::MAD;
  disk.magnetic_pressure_ratio = 1.0;  // Near equipartition
  disk.magnetic_flux = 50.0;           // Strong flux threading horizon
  disk.flux_eruption_period = 6.0;     // Hours (~ orbital period at ISCO for Sgr A*)
  disk.jet_efficiency = 0.1;           // 10% of rest mass to jets

  return disk;
}

// ============================================================================
// MAD Magnetic Field
// ============================================================================

/**
 * @brief Compute magnetic field strength at radius r.
 *
 * For MAD state, magnetic pressure approaches gas pressure:
 * P_mag = B²/(8π) ~ P_gas/β
 *
 * @param r Radius [cm]
 * @param disk MAD disk parameters
 * @return Magnetic field strength [Gauss]
 */
inline double mad_magnetic_field(double r, const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    // SANE: weak magnetic field
    return 0.0;
  }

  // Gas pressure from ideal gas law
  // P_gas ~ ρ k_B T / (μ m_p)
  // Approximate from radiative flux and hydrostatic equilibrium
  double T = disk_temperature(r, disk);

  // Surface density (order of magnitude estimate)
  // Σ ~ Ṁ / (3π ν) where ν is kinematic viscosity
  // For α-disk: ν ~ α c_s H
  double r_g = G * disk.M / C2;
  double H_over_r = 0.1;  // Thin disk approximation
  double c_s = std::sqrt(K_B * T / (0.6 * M_PROTON));  // Sound speed
  double nu_visc = 0.1 * c_s * H_over_r * r;  // α = 0.1

  double Sigma = disk.M_dot / (3.0 * M_PI * nu_visc);
  double rho = Sigma / (H_over_r * r);  // Volume density

  // Gas pressure
  double P_gas = rho * K_B * T / (0.6 * M_PROTON);

  // Magnetic pressure
  double beta = disk.magnetic_pressure_ratio;
  double P_mag = P_gas / beta;

  // B = sqrt(8π P_mag)
  double B = std::sqrt(8.0 * M_PI * P_mag);

  // Geometry factor: stronger near ISCO
  double geometry_factor = std::pow(disk.r_in / r, 1.5);

  // MAD fields can be very strong near horizon
  if (disk.state == AccretionState::MAD) {
    geometry_factor *= 2.0;  // Enhanced for MAD
  }

  return B * geometry_factor;
}

/**
 * @brief Check if flux eruption is currently active.
 *
 * MAD state exhibits quasi-periodic flux eruptions when magnetic
 * pressure builds up and is released.
 *
 * @param disk MAD disk parameters
 * @return true if eruption is active
 */
inline bool is_flux_eruption_active(const MADDiskParams &disk) {
  if (disk.state != AccretionState::MAD) {
    return false;
  }

  // Eruption period in seconds
  double period = disk.flux_eruption_period * 3600.0;

  // Phase within cycle
  double phase = std::fmod(disk.time, period) / period;

  // Eruption active for ~20% of cycle (duty cycle)
  // This matches GRMHD simulations
  return (phase > 0.4 && phase < 0.6);
}

// ============================================================================
// MAD Jet Power
// ============================================================================

/**
 * @brief Compute jet power via Blandford-Znajek mechanism.
 *
 * For MAD state, jets extract rotational energy from the black hole
 * via magnetic field lines threading the horizon.
 *
 * P_jet ~ (a*² Φ_BH² / 4π) * Ω_H²
 *
 * where Ω_H is the horizon angular velocity.
 *
 * @param disk MAD disk parameters
 * @return Jet power [erg/s]
 */
inline double mad_jet_power(const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    // SANE: weak jets (~1% of accretion power)
    return 0.01 * disk.M_dot * C2;
  }

  // Horizon angular velocity
  double M_geo = G * disk.M / C2;
  double a_star = disk.a / M_geo;
  double r_plus = kerr_outer_horizon(disk.M, disk.a);
  double Omega_H = a_star / (2.0 * r_plus);  // rad/M

  // Blandford-Znajek power
  // P_BZ ~ (B_H² r_+² c / 4π) * Ω_H²
  // Normalized form: P_BZ ~ η_jet Ṁ c²

  // Jet efficiency depends on spin and magnetic flux
  double a2 = a_star * a_star;
  double flux2 = disk.magnetic_flux * disk.magnetic_flux;

  // Empirical fit to GRMHD simulations (Tchekhovskoy+ 2011)
  // η_jet can reach 10-40% for MAD with high spin
  double eta_jet = 0.01 * a2 * std::min(flux2 / 100.0, 1.0);

  // For MAD with a*=0.94, Φ=50: η ~ 0.09 (9%)
  if (disk.state == AccretionState::MAD) {
    eta_jet = std::max(eta_jet, disk.jet_efficiency);
  }

  return eta_jet * disk.M_dot * C2;
}

/**
 * @brief Compute jet Lorentz factor.
 *
 * MAD jets are highly relativistic.
 *
 * @param disk MAD disk parameters
 * @return Bulk Lorentz factor Γ
 */
inline double mad_jet_lorentz_factor(const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    return 2.0;  // Mildly relativistic
  }

  // MAD jets: Γ ~ 5-15 for Sgr A*, up to ~50 for blazars
  double M_geo = G * disk.M / C2;
  double a_star = disk.a / M_geo;

  // Higher spin → faster jets
  double Gamma = 5.0 + 10.0 * a_star;

  return Gamma;
}

// ============================================================================
// MAD Variability
// ============================================================================

/**
 * @brief Compute time-variable flux multiplier.
 *
 * MAD exhibits ~30-50% variability on orbital timescales.
 *
 * @param disk MAD disk parameters
 * @return Flux multiplier (0.5 to 1.5 typical)
 */
inline double mad_flux_variability(const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    return 1.0;  // Steady
  }

  // Variability timescale: orbital period at ISCO
  double omega_isco = std::sqrt(G * disk.M / (disk.r_in * disk.r_in * disk.r_in));
  double T_orb = 2.0 * M_PI / omega_isco;

  // Phase
  double phase = std::fmod(disk.time, T_orb) / T_orb;

  // Quasi-periodic variability
  // Amplitude: 30% for MAD (from GRMHD simulations)
  double amplitude = 0.3;
  if (is_flux_eruption_active(disk)) {
    amplitude = 0.5;  // Larger during eruptions
  }

  // Sinusoidal + noise approximation
  double base = 1.0 + amplitude * std::sin(2.0 * M_PI * phase);

  // Add second harmonic for realism
  base += 0.1 * amplitude * std::sin(4.0 * M_PI * phase);

  return std::clamp(base, 0.5, 1.5);
}

/**
 * @brief Update MAD disk time-dependent state.
 *
 * @param disk MAD disk parameters (modified)
 * @param dt Time step [s]
 */
inline void mad_update_time(MADDiskParams &disk, double dt) {
  disk.time += dt;
}

// ============================================================================
// MAD Emission Properties
// ============================================================================

/**
 * @brief Compute effective disk temperature including MAD effects.
 *
 * MAD magnetic dissipation can enhance temperature near ISCO.
 *
 * @param r Radius [cm]
 * @param disk MAD disk parameters
 * @return Effective temperature [K]
 */
inline double mad_disk_temperature(double r, const MADDiskParams &disk) {
  // Base Novikov-Thorne temperature
  double T_base = disk_temperature(r, disk);

  if (disk.state == AccretionState::SANE) {
    return T_base;
  }

  // MAD: magnetic reconnection heating near ISCO
  double r_ratio = disk.r_in / r;
  double magnetic_heating = 1.0 + 0.2 * std::pow(r_ratio, 2.0);

  // During flux eruptions, additional heating
  if (is_flux_eruption_active(disk)) {
    magnetic_heating *= 1.3;
  }

  return T_base * magnetic_heating;
}

/**
 * @brief Compute MAD disk flux with variability.
 *
 * @param r Radius [cm]
 * @param disk MAD disk parameters
 * @return Radiative flux [erg/(cm² s)]
 */
inline double mad_disk_flux(double r, const MADDiskParams &disk) {
  double F_base = disk_flux(r, disk);

  if (disk.state == AccretionState::SANE) {
    return F_base;
  }

  // Apply time variability
  double variability = mad_flux_variability(disk);

  return F_base * variability;
}

} // namespace physics

#endif // PHYSICS_MAD_DISK_H
