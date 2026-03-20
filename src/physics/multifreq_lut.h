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

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <vector>

#include "constants.h"
#include "kerr.h"
#include "lut.h"
#include "mad_disk.h"
#include "schwarzschild.h"
#include "thin_disk.h"

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
  Freq230Ghz, ///< 230 GHz (1.3 mm) - Standard EHT
  Freq345Ghz, ///< 345 GHz (0.87 mm) - Next-gen EHT (50% better resolution)
  DualFreq    ///< Dual-frequency observation (both 230 and 345 GHz)
};

/**
 * @brief Convert frequency enum to string.
 */
inline const char *frequencyName(ObservingFrequency freq) {
  switch (freq) {
  case ObservingFrequency::Freq230Ghz:
    return "230 GHz (1.3 mm)";
  case ObservingFrequency::Freq345Ghz:
    return "345 GHz (0.87 mm)";
  case ObservingFrequency::DualFreq:
    return "Dual (230 + 345 GHz)";
  default:
    return "Unknown";
  }
}

/**
 * @brief Get frequency value in Hz.
 */
inline double frequencyHz(ObservingFrequency freq) {
  switch (freq) {
  case ObservingFrequency::Freq230Ghz:
    return FREQ_230_GHZ;
  case ObservingFrequency::Freq345Ghz:
    return FREQ_345_GHZ;
  case ObservingFrequency::DualFreq:
  default:
    return FREQ_230_GHZ; // Primary (also default)
  }
}

/**
 * @brief Multi-frequency LUT with 230 and 345 GHz data.
 */
struct MultiFreqLut {
  Lut1D lut230ghz; ///< Emissivity at 230 GHz
  Lut1D lut345ghz; ///< Emissivity at 345 GHz
  float rMin = 0.0f;
  float rMax = 0.0f;
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
inline double synchrotronSpectralIndex(double p = 2.5) {
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
inline double frequencyScaling(double nu, double nuRef = FREQ_230_GHZ, double alpha = 0.7) {
  return std::pow(nu / nuRef, -alpha);
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
inline double selfAbsorptionOpticalDepth(double nu, double nuRef = FREQ_230_GHZ,
                                         double tauRef = 1.0) {
  return tauRef * std::pow(nu / nuRef, -2.1);
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
inline double radiativeTransferSimple(double intensityThin, double tau) {
  if (tau < 0.01) {
    return intensityThin * tau; // Optically thin limit
  }
  return intensityThin * (1.0 - std::exp(-tau)); // General case
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
inline double diskFluxAtFrequency(double r, const DiskParams &disk, double nu, double alpha = 0.7) {
  // Base flux (assumed at reference frequency)
  double const fBase = diskFlux(r, disk);

  // Temperature at this radius
  double const t = diskTemperature(r, disk);

  // Peak synchrotron frequency (rough estimate)
  // ν_peak ~ 3 eV T / h ~ 7e11 Hz * (T / 10^7 K)
  double const nuPeak = 7.0e11 * (t / 1.0e7);

  // Spectral shape
  double const freqRatio = nu / nuPeak;

  // Optically thick below peak, optically thin above
  double const tau = (freqRatio < 1.0) ? 10.0 * std::pow(freqRatio, -2.1) : 0.1;

  // Intensity scaling
  double const intensityThin = fBase * std::pow(freqRatio, -alpha);
  double const intensity = radiativeTransferSimple(intensityThin, tau);

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
inline double madDiskFluxAtFrequency(double r, const MADDiskParams &disk, double nu) {
  // Base flux with MAD variability
  double const fBase = madDiskFlux(r, disk);

  // Magnetic field affects synchrotron emission
  double const b = madMagneticField(r, disk);

  // Synchrotron power ∝ B² for fixed electron energy
  // Enhance emission in MAD state
  double magEnhancement = 1.0;
  if (disk.state == AccretionState::MAD) {
    // Stronger B-field → brighter synchrotron
    magEnhancement = 1.0 + (0.5 * (b / 1.0e4)); // Normalize to 10^4 Gauss
  }

  // Spectral index: MAD may have more non-thermal electrons
  double const alpha = (disk.state == AccretionState::MAD) ? 0.8 : 0.6;

  // Temperature
  double const t = madDiskTemperature(r, disk);
  double const nuPeak = 7.0e11 * (t / 1.0e7);

  // Frequency scaling
  double const freqRatio = nu / nuPeak;
  double const tau = (freqRatio < 1.0) ? 10.0 * std::pow(freqRatio, -2.1) : 0.1;

  double const intensityThin = fBase * magEnhancement * std::pow(freqRatio, -alpha);
  double const intensity = radiativeTransferSimple(intensityThin, tau);

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
inline MultiFreqLut generateMultifreqEmissivityLut(int size, double massSolar, double aStar,
                                                   double mdotEdd, bool prograde = true) {
  MultiFreqLut lut;
  if (size <= 1) {
    return lut;
  }

  const double mass = massSolar * M_SUN;
  const double rS = schwarzschildRadius(mass);
  const double rG = G * mass / C2;
  const double a = aStar * rG;
  const double rIn = kerrIscoRadius(mass, a, prograde);
  const double rOut = rIn * 4.0;

  DiskParams disk = kerrDisk(massSolar, aStar, mdotEdd, prograde);
  disk.rIn = rIn;
  disk.rOut = rOut;

  lut.rMin = static_cast<float>(rIn / rS);
  lut.rMax = static_cast<float>(rOut / rS);

  // Generate radial grid
  std::vector<double> radii(static_cast<std::size_t>(size));
  const double logRIn = std::log(rIn);
  const double logROut = std::log(rOut);
  const double dLogR = (logROut - logRIn) / (size - 1);

  for (int i = 0; i < size; ++i) {
    radii.at(static_cast<std::size_t>(i)) = std::exp(logRIn + (i * dLogR));
  }

  // Generate 230 GHz LUT
  lut.lut230ghz.rMin = lut.rMin;
  lut.lut230ghz.rMax = lut.rMax;
  lut.lut230ghz.values.resize(static_cast<std::size_t>(size));

  double maxFlux230 = 0.0;
  for (int i = 0; i < size; ++i) {
    double const flux = diskFluxAtFrequency(radii.at(static_cast<std::size_t>(i)), disk, FREQ_230_GHZ);
    lut.lut230ghz.values.at(static_cast<std::size_t>(i)) = static_cast<float>(flux);
    maxFlux230 = std::max(maxFlux230, flux);
  }

  // Normalize
  if (maxFlux230 > 0.0) {
    for (auto &v : lut.lut230ghz.values) {
      v = static_cast<float>(static_cast<double>(v) / maxFlux230);
    }
  }

  // Generate 345 GHz LUT
  lut.lut345ghz.rMin = lut.rMin;
  lut.lut345ghz.rMax = lut.rMax;
  lut.lut345ghz.values.resize(static_cast<std::size_t>(size));

  double maxFlux345 = 0.0;
  for (int i = 0; i < size; ++i) {
    double const flux = diskFluxAtFrequency(radii.at(static_cast<std::size_t>(i)), disk, FREQ_345_GHZ);
    lut.lut345ghz.values.at(static_cast<std::size_t>(i)) = static_cast<float>(flux);
    maxFlux345 = std::max(maxFlux345, flux);
  }

  // Normalize
  if (maxFlux345 > 0.0) {
    for (auto &v : lut.lut345ghz.values) {
      v = static_cast<float>(static_cast<double>(v) / maxFlux345);
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
inline double ehtAngularResolution(ObservingFrequency frequency) {
  double const lambda = C / frequencyHz(frequency); // Wavelength [cm]
  double const baseline = 1.0e9;                    // Earth diameter ~10^4 km = 10^9 cm

  double const thetaRad = lambda / baseline;                         // Radians
  double const thetaMas = thetaRad * (180.0 / PI) * 3600.0 * 1000.0; // Milliarcseconds

  return thetaMas * 1000.0; // Microarcseconds
}

/**
 * @brief Get resolution improvement factor for 345 GHz vs 230 GHz.
 *
 * @return Resolution ratio (345/230 = 1.5, i.e., 50% better)
 */
inline double resolutionImprovement345ghz() {
  return FREQ_345_GHZ / FREQ_230_GHZ;  // = 1.5
}

} // namespace physics

#endif // PHYSICS_MULTIFREQ_LUT_H
