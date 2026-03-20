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

#include <algorithm>
#include <cmath>

#include "constants.h"
#include "kerr.h"
#include "thin_disk.h"

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
inline const char *accretionStateName(AccretionState state) {
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
  double magneticPressureRatio = 100.0; ///< β = P_gas/P_mag (100 for SANE, ~1 for MAD)
  double magneticFlux = 0.0;            ///< Dimensionless magnetic flux Φ_BH

  // Time-dependent parameters
  double time = 0.0;                       ///< Simulation time [s]
  double fluxEruptionPeriod = 6.0;         ///< Eruption timescale [hours] (~orbital period at ISCO)

  // Jet parameters
  double jetEfficiency = 0.0; ///< Jet power / accretion power
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
inline MADDiskParams sgrAStarMadDisk(double aStar = 0.94, double mDotEdd = 1e-5) {
  MADDiskParams disk;

  // Sgr A* mass: 4.3 million solar masses
  double const mSolar = 4.3e6;
  disk.mass = mSolar * M_SUN;

  // Spin parameter (EHT-constrained)
  double const mGeo = G * disk.mass / C2;
  disk.a = aStar * mGeo;

  // Very low accretion rate (Sgr A* is highly sub-Eddington)
  double const lEdd = 1.26e38 * mSolar;
  double const eta = 0.3; // High efficiency for near-extremal spin
  disk.mDot = mDotEdd * lEdd / (eta * C2);

  // ISCO for highly spinning black hole
  disk.rIn  = kerrIscoRadius(disk.mass, disk.a, true);  // Prograde
  disk.rOut = 1000.0 * mGeo;
  disk.inclination = 0.0;

  // MAD state parameters
  disk.state = AccretionState::MAD;
  disk.magneticPressureRatio = 1.0; // Near equipartition
  disk.magneticFlux = 50.0;         // Strong flux threading horizon
  disk.fluxEruptionPeriod = 6.0;    // Hours (~ orbital period at ISCO for Sgr A*)
  disk.jetEfficiency = 0.1;         // 10% of rest mass to jets

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
inline double madMagneticField(double r, const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    // SANE: weak magnetic field
    return 0.0;
  }

  // Gas pressure from ideal gas law
  // P_gas ~ ρ k_B T / (μ m_p)
  // Approximate from radiative flux and hydrostatic equilibrium
  double const t = diskTemperature(r, disk);

  // Surface density (order of magnitude estimate)
  // Sigma ~ Mdot / (3pi nu) where nu is kinematic viscosity
  // For alpha-disk: nu ~ alpha c_s H
  double const hOverR = 0.1;                               // Thin disk approximation
  double const cS = std::sqrt(K_B * t / (0.6 * M_PROTON)); // Sound speed
  double const nuVisc = 0.1 * cS * hOverR * r;             // alpha = 0.1

  double const sigma = disk.mDot / (3.0 * physics::PI * nuVisc);
  double const rho = sigma / (hOverR * r); // Volume density

  // Gas pressure
  double const pGas = rho * K_B * t / (0.6 * M_PROTON);

  // Magnetic pressure
  double const beta = disk.magneticPressureRatio;
  double const pMag = pGas / beta;

  // B = sqrt(8π P_mag)
  double const b = std::sqrt(8.0 * physics::PI * pMag);

  // Geometry factor: stronger near ISCO
  double geometryFactor = std::pow(disk.rIn / r, 1.5);

  // MAD fields can be very strong near horizon
  if (disk.state == AccretionState::MAD) {
    geometryFactor *= 2.0; // Enhanced for MAD
  }

  return b * geometryFactor;
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
inline bool isFluxEruptionActive(const MADDiskParams &disk) {
  if (disk.state != AccretionState::MAD) {
    return false;
  }

  // Eruption period in seconds
  double const period = disk.fluxEruptionPeriod * 3600.0;

  // Phase within cycle
  double const phase = std::fmod(disk.time, period) / period;

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
inline double madJetPower(const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    // SANE: weak jets (~1% of accretion power)
    return 0.01 * disk.mDot * C2;
  }

  // Horizon angular velocity
  double const mGeo = G * disk.mass / C2;
  double const aStar = disk.a / mGeo;
  // Blandford-Znajek power
  // P_BZ ~ (B_H² r_+² c / 4π) * Ω_H²
  // Normalized form: P_BZ ~ η_jet Ṁ c²

  // Jet efficiency depends on spin and magnetic flux
  double const a2 = aStar * aStar;
  double const flux2 = disk.magneticFlux * disk.magneticFlux;

  // Empirical fit to GRMHD simulations (Tchekhovskoy+ 2011)
  // η_jet can reach 10-40% for MAD with high spin
  double etaJet = 0.01 * a2 * std::min(flux2 / 100.0, 1.0);

  // For MAD with a*=0.94, Φ=50: η ~ 0.09 (9%)
  if (disk.state == AccretionState::MAD) {
    etaJet = std::max(etaJet, disk.jetEfficiency);
  }

  return etaJet * disk.mDot * C2;
}

/**
 * @brief Compute jet Lorentz factor.
 *
 * MAD jets are highly relativistic.
 *
 * @param disk MAD disk parameters
 * @return Bulk Lorentz factor Γ
 */
inline double madJetLorentzFactor(const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    return 2.0;  // Mildly relativistic
  }

  // MAD jets: Γ ~ 5-15 for Sgr A*, up to ~50 for blazars
  double const mGeo = G * disk.mass / C2;
  double const aStar = disk.a / mGeo;

  // Higher spin -> faster jets
  double const gamma = 5.0 + (10.0 * aStar);

  return gamma;
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
inline double madFluxVariability(const MADDiskParams &disk) {
  if (disk.state == AccretionState::SANE) {
    return 1.0;  // Steady
  }

  // Variability timescale: orbital period at ISCO
  double const omegaIsco = std::sqrt(G * disk.mass / (disk.rIn * disk.rIn * disk.rIn));
  double const tOrb = 2.0 * physics::PI / omegaIsco;

  // Phase
  double const phase = std::fmod(disk.time, tOrb) / tOrb;

  // Quasi-periodic variability
  // Amplitude: 30% for MAD (from GRMHD simulations)
  double amplitude = 0.3;
  if (isFluxEruptionActive(disk)) {
    amplitude = 0.5;  // Larger during eruptions
  }

  // Sinusoidal + noise approximation
  double base = 1.0 + (amplitude * std::sin(2.0 * physics::PI * phase));

  // Add second harmonic for realism
  base += 0.1 * amplitude * std::sin(4.0 * physics::PI * phase);

  return std::clamp(base, 0.5, 1.5);
}

/**
 * @brief Update MAD disk time-dependent state.
 *
 * @param disk MAD disk parameters (modified)
 * @param dt Time step [s]
 */
inline void madUpdateTime(MADDiskParams &disk, double dt) {
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
inline double madDiskTemperature(double r, const MADDiskParams &disk) {
  // Base Novikov-Thorne temperature
  double const tBase = diskTemperature(r, disk);

  if (disk.state == AccretionState::SANE) {
    return tBase;
  }

  // MAD: magnetic reconnection heating near ISCO
  double const rRatio = disk.rIn / r;
  double magneticHeating = 1.0 + (0.2 * std::pow(rRatio, 2.0));

  // During flux eruptions, additional heating
  if (isFluxEruptionActive(disk)) {
    magneticHeating *= 1.3;
  }

  return tBase * magneticHeating;
}

/**
 * @brief Compute MAD disk flux with variability.
 *
 * @param r Radius [cm]
 * @param disk MAD disk parameters
 * @return Radiative flux [erg/(cm² s)]
 */
inline double madDiskFlux(double r, const MADDiskParams &disk) {
  double const fBase = diskFlux(r, disk);

  if (disk.state == AccretionState::SANE) {
    return fBase;
  }

  // Apply time variability
  double const variability = madFluxVariability(disk);

  return fBase * variability;
}

} // namespace physics

#endif // PHYSICS_MAD_DISK_H
