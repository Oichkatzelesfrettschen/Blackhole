/**
 * @file multifreq_lut.h
 * @brief Multi-frequency lookup tables for EHT observations.
 *
 * Extends LUT system to support frequency-dependent emission for:
 * - 230 GHz (1.3 mm) - Standard EHT frequency
 * - 345 GHz (0.87 mm) - Next-generation EHT (Jan 2026)
 *
 * The 345 GHz observations provide 50% higher angular resolution
 * and probe different optical depths in the accretion flow.
 *
 * Key physics:
 * - Synchrotron emission: F_ν ∝ ν^(-0.7 to -1.0) in optically thin regime
 * - Self-absorption: τ_ν ∝ ν^(-2.1) → optically thick at low frequencies
 * - Peak frequency shifts with temperature and magnetic field
 *
 * References:
 * - EHT Collaboration (2026), 345 GHz first observations
 * - Rybicki & Lightman, "Radiative Processes in Astrophysics"
 * - Narayan & Yi (1995), ApJ 452, 710 (ADAF synchrotron)
 *
 * Cleanroom implementation based on standard synchrotron formulas.
 */

#ifndef PHYSICS_MULTIFREQ_LUT_H
#define PHYSICS_MULTIFREQ_LUT_H

#include "constants.h"
#include "lut.h"
#include "thin_disk.h"
#include "mad_disk.h"
#include <cmath>
#include <vector>
#include <array>

namespace physics {

// ============================================================================
// Frequency Definitions
// ============================================================================

/// EHT standard observing frequency [Hz]
constexpr double FREQ_230_GHZ = 230.0e9;

/// Next-generation EHT frequency [Hz]
constexpr double FREQ_345_GHZ = 345.0e9;

/// Wavelength for 230 GHz [cm]
constexpr double LAMBDA_230_GHZ = C / FREQ_230_GHZ;

/// Wavelength for 345 GHz [cm]
constexpr double LAMBDA_345_GHZ = C / FREQ_345_GHZ;

// ============================================================================
// Multi-Frequency LUT Structure
// ============================================================================

/**
 * @brief Observing frequency for synthetic observations.
 */
enum class ObservingFrequency {
  FREQ_230GHZ,   ///< 230 GHz (1.3 mm) - Standard EHT
  FREQ_345GHZ,   ///< 345 GHz (0.87 mm) - Next-gen EHT (50% better resolution)
  DUAL_FREQ      ///< Dual-frequency observation (both 230 and 345 GHz)
};

/**
 * @brief Convert frequency enum to string.
 */
inline const char* frequency_name(ObservingFrequency freq) {
  switch (freq) {
    case ObservingFrequency::FREQ_230GHZ: return "230 GHz (1.3 mm)";
    case ObservingFrequency::FREQ_345GHZ: return "345 GHz (0.87 mm)";
    case ObservingFrequency::DUAL_FREQ: return "Dual (230 + 345 GHz)";
    default: return "Unknown";
  }
}

/**
 * @brief Get frequency value in Hz.
 */
inline double frequency_hz(ObservingFrequency freq) {
  switch (freq) {
    case ObservingFrequency::FREQ_230GHZ: return FREQ_230_GHZ;
    case ObservingFrequency::FREQ_345GHZ: return FREQ_345_GHZ;
    case ObservingFrequency::DUAL_FREQ: return FREQ_230_GHZ;  // Primary
    default: return FREQ_230_GHZ;
  }
}

/**
 * @brief Multi-frequency LUT with 230 and 345 GHz data.
 */
struct MultiFreqLut {
  Lut1D lut_230ghz;  ///< Emissivity at 230 GHz
  Lut1D lut_345ghz;  ///< Emissivity at 345 GHz
  float r_min = 0.0f;
  float r_max = 0.0f;
};

// ============================================================================
// Synchrotron Emission
// ============================================================================

/**
 * @brief Compute synchrotron spectral index.
 *
 * For power-law electron distribution N(γ) ∝ γ^(-p):
 * α = (p - 1) / 2
 *
 * Typical values:
 * - Thermal: α ≈ 0.1 (flat spectrum)
 * - Non-thermal: α ≈ 0.7 (steep spectrum)
 *
 * @param p Electron power-law index
 * @return Spectral index α (F_ν ∝ ν^(-α))
 */
inline double synchrotron_spectral_index(double p = 2.5) {
  return (p - 1.0) / 2.0;
}

/**
 * @brief Frequency-dependent emission scaling.
 *
 * In optically thin regime:
 * F_ν ∝ ν^(-α)
 *
 * where α is the spectral index.
 *
 * @param nu Frequency [Hz]
 * @param nu_ref Reference frequency [Hz] (typically 230 GHz)
 * @param alpha Spectral index
 * @return Flux ratio F_ν / F_ν_ref
 */
inline double frequency_scaling(double nu, double nu_ref = FREQ_230_GHZ, double alpha = 0.7) {
  return std::pow(nu / nu_ref, -alpha);
}

/**
 * @brief Self-absorption optical depth.
 *
 * τ_ν ∝ ν^(-2.1) in thermal synchrotron
 *
 * @param nu Frequency [Hz]
 * @param nu_ref Reference frequency [Hz]
 * @param tau_ref Optical depth at reference frequency
 * @return Optical depth τ_ν
 */
inline double self_absorption_optical_depth(double nu, double nu_ref = FREQ_230_GHZ,
                                             double tau_ref = 1.0) {
  return tau_ref * std::pow(nu / nu_ref, -2.1);
}

/**
 * @brief Optically thick/thin transition.
 *
 * I_ν = I_0 (1 - exp(-τ_ν))
 *
 * @param intensity_thin Optically thin intensity
 * @param tau Optical depth
 * @return Observed intensity
 */
inline double radiative_transfer_simple(double intensity_thin, double tau) {
  if (tau < 0.01) {
    return intensity_thin * tau;  // Optically thin limit
  }
  return intensity_thin * (1.0 - std::exp(-tau));  // General case
}

// ============================================================================
// Disk Emission at Multiple Frequencies
// ============================================================================

/**
 * @brief Compute disk flux at specified frequency.
 *
 * Accounts for:
 * - Frequency-dependent synchrotron emission
 * - Self-absorption at low frequencies
 * - Temperature-dependent peak frequency
 *
 * @param r Radius [cm]
 * @param disk Disk parameters
 * @param nu Observing frequency [Hz]
 * @param alpha Spectral index (default 0.7 for non-thermal)
 * @return Flux at frequency ν [erg/(cm² s Hz)]
 */
inline double disk_flux_at_frequency(double r, const DiskParams &disk, double nu,
                                      double alpha = 0.7) {
  // Base flux (assumed at reference frequency)
  double F_base = disk_flux(r, disk);

  // Temperature at this radius
  double T = disk_temperature(r, disk);

  // Peak synchrotron frequency (rough estimate)
  // ν_peak ~ 3 eV T / h ~ 7e11 Hz * (T / 10^7 K)
  double nu_peak = 7.0e11 * (T / 1.0e7);

  // Spectral shape
  double freq_ratio = nu / nu_peak;

  // Optically thick below peak, optically thin above
  double tau = (freq_ratio < 1.0) ? 10.0 * std::pow(freq_ratio, -2.1) : 0.1;

  // Intensity scaling
  double intensity_thin = F_base * std::pow(freq_ratio, -alpha);
  double intensity = radiative_transfer_simple(intensity_thin, tau);

  return intensity;
}

/**
 * @brief Compute MAD disk flux at specified frequency.
 *
 * Includes magnetic field enhancement for MAD state.
 *
 * @param r Radius [cm]
 * @param disk MAD disk parameters
 * @param nu Observing frequency [Hz]
 * @return Flux at frequency ν [erg/(cm² s Hz)]
 */
inline double mad_disk_flux_at_frequency(double r, const MADDiskParams &disk, double nu) {
  // Base flux with MAD variability
  double F_base = mad_disk_flux(r, disk);

  // Magnetic field affects synchrotron emission
  double B = mad_magnetic_field(r, disk);

  // Synchrotron power ∝ B² for fixed electron energy
  // Enhance emission in MAD state
  double mag_enhancement = 1.0;
  if (disk.state == AccretionState::MAD) {
    // Stronger B-field → brighter synchrotron
    mag_enhancement = 1.0 + 0.5 * (B / 1.0e4);  // Normalize to 10^4 Gauss
  }

  // Spectral index: MAD may have more non-thermal electrons
  double alpha = (disk.state == AccretionState::MAD) ? 0.8 : 0.6;

  // Temperature
  double T = mad_disk_temperature(r, disk);
  double nu_peak = 7.0e11 * (T / 1.0e7);

  // Frequency scaling
  double freq_ratio = nu / nu_peak;
  double tau = (freq_ratio < 1.0) ? 10.0 * std::pow(freq_ratio, -2.1) : 0.1;

  double intensity_thin = F_base * mag_enhancement * std::pow(freq_ratio, -alpha);
  double intensity = radiative_transfer_simple(intensity_thin, tau);

  return intensity;
}

// ============================================================================
// Multi-Frequency LUT Generation
// ============================================================================

/**
 * @brief Generate multi-frequency emissivity LUT.
 *
 * Creates LUTs for both 230 GHz and 345 GHz.
 *
 * @param size Number of radial points
 * @param mass_solar Black hole mass in solar masses
 * @param a_star Dimensionless spin
 * @param mdot_edd Accretion rate in Eddington units
 * @param prograde True for prograde orbit
 * @return MultiFreqLut with both frequencies
 */
inline MultiFreqLut generate_multifreq_emissivity_lut(int size, double mass_solar, double a_star,
                                                      double mdot_edd, bool prograde = true) {
  MultiFreqLut lut;
  if (size <= 1) {
    return lut;
  }

  const double mass = mass_solar * M_SUN;
  const double r_s = schwarzschild_radius(mass);
  const double r_g = G * mass / C2;
  const double a = a_star * r_g;
  const double r_in = kerr_isco_radius(mass, a, prograde);
  const double r_out = r_in * 4.0;

  DiskParams disk = kerr_disk(mass_solar, a_star, mdot_edd, prograde);
  disk.r_in = r_in;
  disk.r_out = r_out;

  lut.r_min = static_cast<float>(r_in / r_s);
  lut.r_max = static_cast<float>(r_out / r_s);

  // Generate radial grid
  std::vector<double> radii(static_cast<std::size_t>(size));
  const double log_r_in = std::log(r_in);
  const double log_r_out = std::log(r_out);
  const double d_log_r = (log_r_out - log_r_in) / (size - 1);

  for (int i = 0; i < size; ++i) {
    radii[static_cast<std::size_t>(i)] = std::exp(log_r_in + i * d_log_r);
  }

  // Generate 230 GHz LUT
  lut.lut_230ghz.r_min = lut.r_min;
  lut.lut_230ghz.r_max = lut.r_max;
  lut.lut_230ghz.values.resize(static_cast<std::size_t>(size));

  double max_flux_230 = 0.0;
  for (int i = 0; i < size; ++i) {
    double flux = disk_flux_at_frequency(radii[static_cast<std::size_t>(i)], disk, FREQ_230_GHZ);
    lut.lut_230ghz.values[static_cast<std::size_t>(i)] = static_cast<float>(flux);
    max_flux_230 = std::max(max_flux_230, flux);
  }

  // Normalize
  if (max_flux_230 > 0.0) {
    for (auto &v : lut.lut_230ghz.values) {
      v = static_cast<float>(static_cast<double>(v) / max_flux_230);
    }
  }

  // Generate 345 GHz LUT
  lut.lut_345ghz.r_min = lut.r_min;
  lut.lut_345ghz.r_max = lut.r_max;
  lut.lut_345ghz.values.resize(static_cast<std::size_t>(size));

  double max_flux_345 = 0.0;
  for (int i = 0; i < size; ++i) {
    double flux = disk_flux_at_frequency(radii[static_cast<std::size_t>(i)], disk, FREQ_345_GHZ);
    lut.lut_345ghz.values[static_cast<std::size_t>(i)] = static_cast<float>(flux);
    max_flux_345 = std::max(max_flux_345, flux);
  }

  // Normalize
  if (max_flux_345 > 0.0) {
    for (auto &v : lut.lut_345ghz.values) {
      v = static_cast<float>(static_cast<double>(v) / max_flux_345);
    }
  }

  return lut;
}

// ============================================================================
// Resolution Effects
// ============================================================================

/**
 * @brief Compute angular resolution for EHT.
 *
 * θ_res = λ / D_baseline
 *
 * where D_baseline is the Earth diameter (~10^4 km for EHT).
 *
 * @param frequency Observing frequency
 * @return Angular resolution [microarcseconds]
 */
inline double eht_angular_resolution(ObservingFrequency frequency) {
  double lambda = C / frequency_hz(frequency);  // Wavelength [cm]
  double baseline = 1.0e9;  // Earth diameter ~10^4 km = 10^9 cm

  double theta_rad = lambda / baseline;  // Radians
  double theta_mas = theta_rad * (180.0 / PI) * 3600.0 * 1000.0;  // Milliarcseconds

  return theta_mas * 1000.0;  // Microarcseconds
}

/**
 * @brief Get resolution improvement factor for 345 GHz vs 230 GHz.
 *
 * @return Resolution ratio (345/230 = 1.5, i.e., 50% better)
 */
inline double resolution_improvement_345ghz() {
  return FREQ_345_GHZ / FREQ_230_GHZ;  // = 1.5
}

} // namespace physics

#endif // PHYSICS_MULTIFREQ_LUT_H
