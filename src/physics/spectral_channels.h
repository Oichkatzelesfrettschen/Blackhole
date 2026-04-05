/**
 * @file spectral_channels.h
 * @brief Multi-wavelength observational bands for black hole astronomy
 *
 * Defines spectral channels for radio (EHT), optical, and X-ray observations.
 * Includes band definitions, wavelength conversions, and RGB color mappings.
 *
 * References:
 * - Event Horizon Telescope: 230 GHz (1.3 mm) observations
 * - Chandra X-ray Observatory: 0.5-10 keV band
 * - Standard optical filters: Johnson UBVRI system
 *
 * Cleanroom implementation based on standard observational parameters.
 */

#ifndef PHYSICS_SPECTRAL_CHANNELS_H
#define PHYSICS_SPECTRAL_CHANNELS_H

#include <algorithm>
#include <cmath>
#include <numbers>

namespace physics {

// ============================================================================
// Fundamental Constants (SI units)
// ============================================================================

/// Speed of light [m/s]
inline constexpr double C_SI = 2.99792458e8;

/// Planck constant [J*s]
inline constexpr double PLANCK_SI = 6.62607015e-34;

/// Boltzmann constant [J/K]
inline constexpr double BOLTZMANN_SI = 1.380649e-23;

// ============================================================================
// Spectral Bands: Frequency Definitions
// ============================================================================

/**
 * @brief Radio band (EHT 230 GHz)
 * @details Event Horizon Telescope observations of M87* and Sgr A*
 */
inline constexpr struct {
  double centerHz = 2.3e11;  // 230 GHz
  double bandwidthHz = 4e9;  // 4 GHz
  double wavelengthMm = 1.3; // 1.3 mm
  const char *name = "Radio (EHT 230 GHz)";
} RADIO_BAND;

/**
 * @brief Sub-millimeter band (ALMA)
 * @details Atacama Large Millimeter Array observations
 */
inline constexpr struct {
  double centerHz = 1e11;    // 100 GHz
  double bandwidthHz = 8e9;  // 8 GHz bandwidth
  double wavelengthMm = 3.0; // 3 mm
  const char *name = "Sub-mm (ALMA 100 GHz)";
} SUBMM_BAND;

/**
 * @brief Optical band (visual light)
 * @details Visual observation in Johnson V band (540 nm)
 */
inline constexpr struct {
  double centerNm = 540.0;           // 540 nm (green)
  double centerHz = C_SI / 540.0e-9; // ~5.6e14 Hz
  double bandwidthNm = 80.0;         // 80 nm (FWHM)
  const char *name = "Optical (V-band 540 nm)";
} OPTICAL_BAND;

/**
 * @brief X-ray band (Chandra)
 * @details X-ray observations in typical Chandra energy range
 */
inline constexpr struct {
  double energyKevMin = 0.5;    // 0.5 keV
  double energyKevMax = 10.0;   // 10 keV
  double energyKevCenter = 3.0; // Central energy (3 keV)
  double centerHz = (energyKevCenter * 1e3 * 1.602176634e-19) / PLANCK_SI;
  const char *name = "X-ray (Chandra 0.5-10 keV)";
} XRAY_BAND;

// ============================================================================
// Unit Conversions
// ============================================================================

/**
 * @brief Convert frequency [Hz] to wavelength [m]
 *
 * lambda = c / nu
 *
 * @param frequency [Hz]
 * @return Wavelength [m]
 */
[[nodiscard]] inline double frequencyToWavelength(double frequency) {
  if (frequency < 1e6) {
    return 1e10; // Avoid division by very small numbers
  }
  return C_SI / frequency;
}

/**
 * @brief Convert wavelength [m] to frequency [Hz]
 *
 * nu = c / lambda
 *
 * @param wavelength [m]
 * @return Frequency [Hz]
 */
[[nodiscard]] inline double wavelengthToFrequency(double wavelength) {
  if (wavelength < 1e-20) {
    return 1e30;
  }
  return C_SI / wavelength;
}

/**
 * @brief Convert energy [keV] to frequency [Hz]
 *
 * nu = E / h
 *
 * @param energyKev [keV]
 * @return Frequency [Hz]
 */
[[nodiscard]] inline double energyToFrequency(double energyKev) {
  const double energyJoules = energyKev * 1e3 * 1.602176634e-19;
  return energyJoules / PLANCK_SI;
}

/**
 * @brief Convert frequency [Hz] to energy [keV]
 *
 * E = h*nu [keV]
 *
 * @param frequency [Hz]
 * @return Energy [keV]
 */
[[nodiscard]] inline double frequencyToEnergy(double frequency) {
  const double energyJoules = PLANCK_SI * frequency;
  return energyJoules / (1e3 * 1.602176634e-19);
}

// ============================================================================
// Photometric Color Functions
// ============================================================================

/**
 * @brief Convert photon flux to visual RGB
 *
 * Maps photon flux across different wavelengths to visual color space.
 * Uses standard color response functions for human vision.
 *
 * @param fluxRadio Flux in radio band [erg/s/cm^2/Hz]
 * @param fluxOptical Flux in optical band [erg/s/cm^2/Hz]
 * @param fluxXray Flux in X-ray band [erg/s/cm^2/Hz]
 * @return RGB color vector [0, 1] for each channel
 */
struct RGBColor {
  double r{}, g{}, b{};

  // Clamp to [0, 1]
  void normalize() {
    r = std::clamp(r, 0.0, 1.0);
    g = std::clamp(g, 0.0, 1.0);
    b = std::clamp(b, 0.0, 1.0);
  }
};

[[nodiscard]] inline RGBColor fluxToRgb(double fluxRadio, double fluxOptical, double fluxXray) {
  // Normalize fluxes to [0, 1] range
  const double fMax = std::max({fluxRadio, fluxOptical, fluxXray, 1e-30});

  double fR = fluxRadio / fMax;   // Red channel (radio)
  double fG = fluxOptical / fMax; // Green channel (optical)
  double fB = fluxXray / fMax;    // Blue channel (X-ray)

  // Apply logarithmic scaling for better dynamic range
  const double scale = 0.4; // Compression factor
  const double logDenom = std::log(1.0 + scale);
  fR = (fR > 0.0) ? std::log(1.0 + (scale * fR)) / logDenom : 0.0;
  fG = (fG > 0.0) ? std::log(1.0 + (scale * fG)) / logDenom : 0.0;
  fB = (fB > 0.0) ? std::log(1.0 + (scale * fB)) / logDenom : 0.0;

  RGBColor rgb = {.r = fR, .g = fG, .b = fB};
  rgb.normalize();
  return rgb;
}

// ============================================================================
// Band Filter Functions
// ============================================================================

/**
 * @brief Gaussian filter response for observational band
 *
 * Simulates typical observational filter response around band center.
 *
 * @param frequency [Hz]
 * @param centerFrequency [Hz]
 * @param bandwidth [Hz]
 * @return Filter response [0, 1]
 */
[[nodiscard]] inline double gaussianFilter(double frequency, double centerFrequency,
                                           double bandwidth) {
  if (bandwidth < 1e6) {
    return 0.0;
  }

  // FWHM to sigma conversion: sigma = FWHM / (2 * sqrt(2 * ln 2))
  const double sigmaVal = bandwidth / (2.0 * std::sqrt(2.0 * std::numbers::ln2));
  const double x = (frequency - centerFrequency) / sigmaVal;

  return std::exp((-0.5 * x) * x);
}

/**
 * @brief Rectangular filter (top-hat) response
 *
 * Simpler filter with sharp edges at band limits.
 *
 * @param frequency [Hz]
 * @param center [Hz]
 * @param bandwidth [Hz]
 * @return Filter response [0, 1]
 */
[[nodiscard]] inline double rectangularFilter(double frequency, double center, double bandwidth) {
  const double lower = center - (bandwidth / 2.0);
  const double upper = center + (bandwidth / 2.0);

  if ((frequency >= lower) && (frequency <= upper)) {
    return 1.0;
  }
  return 0.0;
}

// ============================================================================
// Multi-Band Imaging
// ============================================================================

/**
 * @brief Sample spectrum at standard observational bands
 *
 * Given a spectrum F(nu), integrates through each observational band filter
 * to obtain integrated flux in each band.
 *
 * @param frequencies Array of frequency samples [Hz]
 * @param fluxes Array of flux samples [erg/s/cm^2/Hz]
 * @param nSamples Number of samples
 * @return MultibandsFlux with fluxes in radio, optical, X-ray bands
 */
struct MultibandsFlux {
  double radioFlux{};
  double opticalFlux{};
  double xrayFlux{};
};

[[nodiscard]] inline MultibandsFlux sampleSpectrumBands(const double *frequencies,
                                                        const double *fluxes, int nSamples) {
  double fRadio = 0.0;
  double fOptical = 0.0;
  double fXray = 0.0;

  // Integrate spectrum through each band filter
  for (int i = 0; i < nSamples - 1; ++i) {
    const double freqMid = 0.5 * (frequencies[i] + frequencies[i + 1]);
    const double fluxMid = 0.5 * (fluxes[i] + fluxes[i + 1]);
    const double dFreq = frequencies[i + 1] - frequencies[i];

    // Radio band (230 GHz)
    const double radioResponse =
        gaussianFilter(freqMid, RADIO_BAND.centerHz, RADIO_BAND.bandwidthHz);
    fRadio += radioResponse * fluxMid * dFreq;

    // Optical band (540 nm ~ 5.6e14 Hz)
    const double opticalResponse = gaussianFilter(
        freqMid, OPTICAL_BAND.centerHz, (OPTICAL_BAND.bandwidthNm / 1e9) * OPTICAL_BAND.centerHz);
    fOptical += opticalResponse * fluxMid * dFreq;

    // X-ray band (0.5-10 keV)
    const double xrayCenter = XRAY_BAND.centerHz;
    const double xrayBandwidth =
        (energyToFrequency(XRAY_BAND.energyKevMax) - energyToFrequency(XRAY_BAND.energyKevMin));
    const double xrayResponse = gaussianFilter(freqMid, xrayCenter, xrayBandwidth);
    fXray += xrayResponse * fluxMid * dFreq;
  }

  return {.radioFlux = fRadio, .opticalFlux = fOptical, .xrayFlux = fXray};
}

// ============================================================================
// Standard Magnitude System
// ============================================================================

/**
 * @brief Convert flux to apparent magnitude (Vega system)
 *
 * m = m_0 - 2.5 * log10(F / F_0)
 *
 * @param flux [erg/s/cm^2]
 * @param referenceFlux [erg/s/cm^2] (typically Vega flux)
 * @return Apparent magnitude
 */
[[nodiscard]] inline double fluxToMagnitude(double flux, double referenceFlux) {
  if ((flux <= 0.0) || (referenceFlux <= 0.0)) {
    return 99.0;
  }
  return -2.5 * std::log10(flux / referenceFlux);
}

/**
 * @brief Convert apparent magnitude to flux (Vega system)
 *
 * F = F_0 * 10^(-m / 2.5)
 *
 * @param magnitude [mag]
 * @param referenceFlux [erg/s/cm^2]
 * @return Flux [erg/s/cm^2]
 */
[[nodiscard]] inline double magnitudeToFlux(double magnitude, double referenceFlux) {
  return referenceFlux * std::pow(10.0, -magnitude / 2.5);
}

} // namespace physics

#endif // PHYSICS_SPECTRAL_CHANNELS_H
