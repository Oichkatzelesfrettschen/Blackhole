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

#include <cmath>
#include <array>

namespace physics {

// ============================================================================
// Fundamental Constants (SI units)
// ============================================================================

/// Speed of light [m/s]
inline constexpr double C = 2.99792458e8;

/// Planck constant [J*s]
inline constexpr double PLANCK = 6.62607015e-34;

/// Boltzmann constant [J/K]
inline constexpr double BOLTZMANN = 1.380649e-23;

// ============================================================================
// Spectral Bands: Frequency Definitions
// ============================================================================

/**
 * @brief Radio band (EHT 230 GHz)
 * @details Event Horizon Telescope observations of M87* and Sgr A*
 */
inline constexpr struct {
    double center_hz = 2.3e11;           // 230 GHz
    double bandwidth_hz = 4e9;           // 4 GHz
    double wavelength_mm = 1.3;          // 1.3 mm
    const char* name = "Radio (EHT 230 GHz)";
} RADIO_BAND;

/**
 * @brief Sub-millimeter band (ALMA)
 * @details Atacama Large Millimeter Array observations
 */
inline constexpr struct {
    double center_hz = 1e11;             // 100 GHz
    double bandwidth_hz = 8e9;           // 8 GHz bandwidth
    double wavelength_mm = 3.0;          // 3 mm
    const char* name = "Sub-mm (ALMA 100 GHz)";
} SUBMM_BAND;

/**
 * @brief Optical band (visual light)
 * @details Visual observation in Johnson V band (540 nm)
 */
inline constexpr struct {
    double center_nm = 540.0;            // 540 nm (green)
    double center_hz = C / (540.0e-9);   // ~5.6e14 Hz
    double bandwidth_nm = 80.0;          // 80 nm (FWHM)
    const char* name = "Optical (V-band 540 nm)";
} OPTICAL_BAND;

/**
 * @brief X-ray band (Chandra)
 * @details X-ray observations in typical Chandra energy range
 */
inline constexpr struct {
    double energy_kev_min = 0.5;         // 0.5 keV
    double energy_kev_max = 10.0;        // 10 keV
    double energy_kev_center = 3.0;      // Central energy (3 keV)
    double center_hz = (energy_kev_center * 1e3 * 1.602176634e-19) / PLANCK;
    const char* name = "X-ray (Chandra 0.5-10 keV)";
} XRAY_BAND;

// ============================================================================
// Unit Conversions
// ============================================================================

/**
 * @brief Convert frequency [Hz] to wavelength [m]
 *
 * λ = c / ν
 *
 * @param frequency [Hz]
 * @return Wavelength [m]
 */
inline double frequency_to_wavelength(double frequency) {
    if (frequency < 1e6) return 1e10;  // Avoid division by very small numbers
    return C / frequency;
}

/**
 * @brief Convert wavelength [m] to frequency [Hz]
 *
 * ν = c / λ
 *
 * @param wavelength [m]
 * @return Frequency [Hz]
 */
inline double wavelength_to_frequency(double wavelength) {
    if (wavelength < 1e-20) return 1e30;
    return C / wavelength;
}

/**
 * @brief Convert energy [keV] to frequency [Hz]
 *
 * ν = E / h
 *
 * @param energy_kev [keV]
 * @return Frequency [Hz]
 */
inline double energy_to_frequency(double energy_kev) {
    double energy_joules = energy_kev * 1e3 * 1.602176634e-19;
    return energy_joules / PLANCK;
}

/**
 * @brief Convert frequency [Hz] to energy [keV]
 *
 * E = h*ν [keV]
 *
 * @param frequency [Hz]
 * @return Energy [keV]
 */
inline double frequency_to_energy(double frequency) {
    double energy_joules = PLANCK * frequency;
    return energy_joules / (1e3 * 1.602176634e-19);
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
 * @param flux_radio Flux in radio band [erg/s/cm^2/Hz]
 * @param flux_optical Flux in optical band [erg/s/cm^2/Hz]
 * @param flux_xray Flux in X-ray band [erg/s/cm^2/Hz]
 * @return RGB color vector [0, 1] for each channel
 */
struct RGBColor {
    double r, g, b;

    // Clamp to [0, 1]
    void normalize() {
        r = (r < 0.0) ? 0.0 : (r > 1.0) ? 1.0 : r;
        g = (g < 0.0) ? 0.0 : (g > 1.0) ? 1.0 : g;
        b = (b < 0.0) ? 0.0 : (b > 1.0) ? 1.0 : b;
    }
};

inline RGBColor flux_to_rgb(double flux_radio, double flux_optical, double flux_xray) {
    // Normalize fluxes to [0, 1] range
    double f_max = std::max({flux_radio, flux_optical, flux_xray, 1e-30});

    double f_r = flux_radio / f_max;      // Red channel (radio)
    double f_g = flux_optical / f_max;    // Green channel (optical)
    double f_b = flux_xray / f_max;       // Blue channel (X-ray)

    // Apply logarithmic scaling for better dynamic range
    double scale = 0.4;  // Compression factor
    f_r = (f_r > 0.0) ? std::log(1.0 + scale * f_r) / std::log(1.0 + scale) : 0.0;
    f_g = (f_g > 0.0) ? std::log(1.0 + scale * f_g) / std::log(1.0 + scale) : 0.0;
    f_b = (f_b > 0.0) ? std::log(1.0 + scale * f_b) / std::log(1.0 + scale) : 0.0;

    RGBColor rgb = {f_r, f_g, f_b};
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
 * @param center_frequency [Hz]
 * @param bandwidth [Hz]
 * @return Filter response [0, 1]
 */
inline double gaussian_filter(double frequency, double center_frequency, double bandwidth) {
    if (bandwidth < 1e6) return 0.0;

    double sigma = bandwidth / (2.0 * std::sqrt(2.0 * std::log(2.0)));  // FWHM to sigma
    double x = (frequency - center_frequency) / sigma;

    return std::exp(-0.5 * x * x);
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
inline double rectangular_filter(double frequency, double center, double bandwidth) {
    double lower = center - bandwidth / 2.0;
    double upper = center + bandwidth / 2.0;

    if (frequency >= lower && frequency <= upper) {
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
 * Given a spectrum F(ν), integrates through each observational band filter
 * to obtain integrated flux in each band.
 *
 * @param spectrum Flux density function F(ν) [erg/s/cm^2/Hz]
 * @param frequencies Array of frequency samples [Hz]
 * @param fluxes Array of flux samples [erg/s/cm^2/Hz]
 * @param n_samples Number of samples
 * @return RGBColor with fluxes in radio, optical, X-ray bands
 */
struct MultibandsFlux {
    double radio_flux;
    double optical_flux;
    double xray_flux;
};

inline MultibandsFlux sample_spectrum_bands(const double* frequencies,
                                            const double* fluxes,
                                            int n_samples) {
    double f_radio = 0.0;
    double f_optical = 0.0;
    double f_xray = 0.0;

    // Integrate spectrum through each band filter
    for (int i = 0; i < n_samples - 1; i++) {
        double freq_mid = 0.5 * (frequencies[i] + frequencies[i + 1]);
        double flux_mid = 0.5 * (fluxes[i] + fluxes[i + 1]);
        double dfreq = frequencies[i + 1] - frequencies[i];

        // Radio band (230 GHz)
        double radio_response = gaussian_filter(freq_mid, RADIO_BAND.center_hz,
                                                RADIO_BAND.bandwidth_hz);
        f_radio += radio_response * flux_mid * dfreq;

        // Optical band (540 nm ~ 5.6e14 Hz)
        double optical_response = gaussian_filter(freq_mid, OPTICAL_BAND.center_hz,
                                                  OPTICAL_BAND.bandwidth_nm / 1e9 *
                                                      OPTICAL_BAND.center_hz);
        f_optical += optical_response * flux_mid * dfreq;

        // X-ray band (0.5-10 keV)
        double xray_center = XRAY_BAND.center_hz;
        double xray_bandwidth = (energy_to_frequency(XRAY_BAND.energy_kev_max) -
                                 energy_to_frequency(XRAY_BAND.energy_kev_min));
        double xray_response = gaussian_filter(freq_mid, xray_center, xray_bandwidth);
        f_xray += xray_response * flux_mid * dfreq;
    }

    return {f_radio, f_optical, f_xray};
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
 * @param reference_flux [erg/s/cm^2] (typically Vega flux)
 * @return Apparent magnitude
 */
inline double flux_to_magnitude(double flux, double reference_flux) {
    if (flux <= 0.0 || reference_flux <= 0.0) return 99.0;

    return -2.5 * std::log10(flux / reference_flux);
}

/**
 * @brief Convert apparent magnitude to flux (Vega system)
 *
 * F = F_0 * 10^(-m / 2.5)
 *
 * @param magnitude [mag]
 * @param reference_flux [erg/s/cm^2]
 * @return Flux [erg/s/cm^2]
 */
inline double magnitude_to_flux(double magnitude, double reference_flux) {
    return reference_flux * std::pow(10.0, -magnitude / 2.5);
}

} // namespace physics

#endif // PHYSICS_SPECTRAL_CHANNELS_H
