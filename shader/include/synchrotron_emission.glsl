/**
 * @file synchrotron_emission.glsl
 * @brief GPU implementation of synchrotron radiation physics
 *
 * Port of src/physics/synchrotron.h to GLSL 4.60
 * Enables synchrotron emission calculations in GPU ray marching
 *
 * References:
 * - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 6
 * - Longair (2011) "High Energy Astrophysics" Ch. 8
 *
 * Performance: Target <1ms per ray for full radiative transfer
 */

#ifndef SYNCHROTRON_EMISSION_GLSL
#define SYNCHROTRON_EMISSION_GLSL

// ============================================================================
// Constants (CGS units)
// ============================================================================

const float ELECTRON_MASS = 9.1093837015e-28;      // [g]
const float ELECTRON_CHARGE = 4.80320425e-10;     // [esu]
const float CLASSICAL_ELECTRON_R = 2.8179403262e-13; // [cm]
const float SIGMA_THOMSON = 6.6524587321e-25;    // [cm^2]
const float ALPHA_FINE = 7.2973525693e-3;         // 1/137

// Synchrotron constant
const float SYNCHROTRON_CONST = 3.0 * ELECTRON_CHARGE /
  (4.0 * 3.14159265359 * ELECTRON_MASS * ELECTRON_MASS * ELECTRON_MASS);

#include "synchrotron_lut_domain.h"
uniform sampler2D synchFLut;
uniform sampler2D synchGLut;
uniform float synchLutAvailable; ///< 1 when both CPU-built tables are bound.

// LUT domain constants, single-sourced with the C++ and CUDA consumers.
const float SYNCH_G_LUT_X_MIN = SYNCH_G_LUT_DOMAIN_X_MIN;
const float SYNCH_G_LUT_X_MAX = SYNCH_G_LUT_DOMAIN_X_MAX;

/**
 * Samples a log-spaced table over [X_MIN, X_MAX] at texel centers. Beyond the
 * ends it continues with the leading asymptote scaled to the end entry,
 * x^(1/3) below and sqrt(x) e^-x above (shared by F and G), so the value is
 * continuous across both joins.
 */
float synchLutSample(sampler2D lut, float x) {
  float entries = float(SYNCH_G_LUT_DOMAIN_ENTRIES);
  float logRatio = log(SYNCH_G_LUT_X_MAX / SYNCH_G_LUT_X_MIN);
  float xc = clamp(x, SYNCH_G_LUT_X_MIN, SYNCH_G_LUT_X_MAX);
  float u = log(xc / SYNCH_G_LUT_X_MIN) / logRatio;
  float value = texture(lut, vec2((u * (entries - 1.0) + 0.5) / entries, 0.5)).r;
  if (x < SYNCH_G_LUT_X_MIN) {
    return value * pow(x / SYNCH_G_LUT_X_MIN, 1.0 / 3.0);
  }
  if (x > SYNCH_G_LUT_X_MAX) {
    return value * sqrt(x / SYNCH_G_LUT_X_MAX) * exp(SYNCH_G_LUT_X_MAX - x);
  }
  return value;
}

// ============================================================================
// Synchrotron Function F(x) - Single Electron Spectrum
// ============================================================================

/**
 * Synchrotron function F(x) = x * integral_x^inf K_5/3(xi) dxi
 *
 * Samples the CPU-generated log-spaced F(x) table.
 *
 * @param x Dimensionless frequency (nu / nu_c)
 * @return Synchrotron function value
 */
float synchrotron_F(float x) {
  if (x <= 0.0) return 0.0;
  if (synchLutAvailable > 0.5) {
    return synchLutSample(synchFLut, x);
  }
  // Without a bound table: Aharonian, Kelner & Prosekin (2010,
  // arXiv:1006.1045) Eq. D6, continuous and within 0.4% of F for all x.
  float x23 = pow(x, 2.0 / 3.0);
  float x43 = x23 * x23;
  return 2.15 * pow(x, 1.0 / 3.0) * pow(1.0 + 3.06 * x, 1.0 / 6.0) *
         (1.0 + 0.884 * x23 + 0.471 * x43) / (1.0 + 1.64 * x23 + 0.974 * x43) * exp(-x);
}

// ============================================================================
// Synchrotron Function G(x) - Polarization (LUT-based)
// ============================================================================

// 1D LUT generated from CPU Bessel K_{2/3} evaluation.
// Upload with synchrotron_G_generate_lut() from synchrotron.h.
//
// Stored as GL_TEXTURE_2D (width=LUT size, height=1) so the same texture
// object can be registered for CUDA-GL interop via cudaGraphicsGLRegisterImage,
// which does not support GL_TEXTURE_1D.
// Uses GL_LINEAR filtering for free hardware interpolation.
// Without bound tables (synchLutAvailable = 0) F and G use published fits.

/**
 * G(x) = x * K_2/3(x) for polarized emission.
 *
 * Uses a precomputed LUT (log-spaced) when available; asymptotic
 * approximations otherwise.
 *
 * @param x Dimensionless frequency
 * @return G(x) function value
 */
float synchrotron_G(float x) {
  if (x <= 0.0) return 0.0;
  if (synchLutAvailable > 0.5) {
    return synchLutSample(synchGLut, x);
  }
  // Without a bound table: Fouka & Ouichaoui (2013, arXiv:1301.6908) Eq. 6
  // with Table 3, K_{2/3} = A1 exp(H1) + A2 (1 - exp(H2)), within 0.035% of
  // G = x K_{2/3} for all x.
  float x12 = sqrt(x);
  float x13 = pow(x, 1.0 / 3.0);
  float x14 = sqrt(x12);
  float h1 = -1.0010216415582440 * x + 0.88350305221249859 * x12 -
             3.6240174463901829 * x13 + 0.57393980442916881 * x14;
  float h2 = -0.2493940736333195 * x + 0.9122693061687756 * x12 +
             1.2051408667145216 * x13 - 5.5227048291651126 * x14;
  float smallX = 1.0747641207672394 * pow(x, -2.0 / 3.0); // 2^(-1/3) Gamma(2/3)
  float largeX = sqrt(3.14159265359 / (2.0 * x)) * exp(-x);
  return x * (smallX * exp(h1) + largeX * (1.0 - exp(h2)));
}

// ============================================================================
// Critical Frequency Computation
// ============================================================================

/**
 * Synchrotron critical frequency.
 *
 * nu_c = (3/4pi) * (eB / m_e c) * gamma^2 * sin(alpha)
 *
 * For perpendicular field (alpha = 90 degrees):
 * nu_c = (3/4pi) * (eB / m_e c) * gamma^2
 *
 * @param gamma Electron Lorentz factor
 * @param B Magnetic field [Gauss]
 * @return Critical frequency [Hz]
 */
float critical_frequency(float gamma, float B) {
  float B_abs = abs(B);
  if (B_abs < 1e-30) return 1e30;  // Effectively infinite

  return (3.0 / (4.0 * 3.14159265359)) *
    (ELECTRON_CHARGE * B_abs / (ELECTRON_MASS * 2.99792458e10)) *
    gamma * gamma;
}

// ============================================================================
// Power-Law Electron Distribution Spectrum
// ============================================================================

/**
 * Synchrotron spectrum from power-law electron distribution.
 *
 * For electron distribution N(gamma) propto gamma^(-p)
 * between gamma_min and gamma_max:
 *
 * F_nu propto nu^(-(p-1)/2) in optically thin regime
 *
 * @param nu Frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param gamma_min Minimum Lorentz factor
 * @param gamma_max Maximum Lorentz factor
 * @param p Power-law index (typically 2-3 for jets)
 * @return Relative spectral power
 */
float power_law_spectrum(float nu, float B, float gamma_min,
                         float gamma_max, float p) {

  if (nu <= 0.0) return 0.0;

  float nu_min = critical_frequency(gamma_min, B);
  float nu_max = critical_frequency(gamma_max, B);

  // Spectral index: alpha = -(p-1)/2
  float alpha = -(p - 1.0) / 2.0;

  // Self-absorption regime (optically thick)
  if (nu < nu_min) {
    return pow(nu / nu_min, 2.5);
  }
  // Power-law regime (optically thin)
  else if (nu < nu_max) {
    return pow(nu / nu_min, alpha);
  }
  // Exponential cutoff above gamma_max
  else {
    return pow(nu_max / nu_min, alpha) *
           exp(-(nu - nu_max) / nu_max);
  }
}

// ============================================================================
// Self-Absorption Coefficient
// ============================================================================

/**
 * Synchrotron self-absorption coefficient.
 *
 * alpha_nu propto nu^(-(p+4)/2) for power-law electrons
 *
 * Below self-absorption frequency, source becomes optically thick.
 *
 * @param nu Frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param n_e Electron density [cm^-3]
 * @param gamma_min Minimum Lorentz factor
 * @param p Electron power-law index
 * @return Absorption coefficient [cm^-1]
 */
float absorption_coefficient(float nu, float B, float n_e,
                             float gamma_min, float p) {

  // Gyrofrequency
  float nu_B = (ELECTRON_CHARGE * abs(B)) /
    (6.28318530718 * ELECTRON_MASS * 2.99792458e10);

  // Absorption prefactor
  float prefactor = 0.02 * ELECTRON_CHARGE * n_e /
    (ELECTRON_MASS * 2.99792458e10);

  // Frequency dependence
  float exponent = -(p + 4.0) / 2.0;

  return prefactor * pow(nu_B, (p + 2.0) / 2.0) *
         pow(nu, exponent);
}

// ============================================================================
// Polarization Degree
// ============================================================================

/**
 * Linear polarization degree from synchrotron emission.
 *
 * Pol = G(x) / F(x)
 *
 * For power-law electrons with index p:
 * Pol_max = (p + 1) / (p + 7/3)
 *
 * @param x Dimensionless frequency (nu / nu_c)
 * @return Polarization degree [0, 1]
 */
float polarization_degree(float x) {
  float F = synchrotron_F(x);
  if (F < 1e-30) return 0.0;

  float G = synchrotron_G(x);
  return G / F;
}

// ============================================================================
// Emissivity (Specific Intensity)
// ============================================================================

/**
 * Synchrotron specific intensity from power-law electrons.
 *
 * Integrates synchrotron function over electron distribution.
 *
 * I_nu [erg / s / cm^3 / Hz / sr]
 *
 * @param nu Frequency [Hz]
 * @param B Magnetic field [Gauss]
 * @param gamma_min Minimum Lorentz factor
 * @param gamma_max Maximum Lorentz factor
 * @param p Power-law index
 * @param n_e Total electron density [cm^-3]
 * @return Specific intensity (relative units)
 */
float synchrotron_intensity(float nu, float B, float gamma_min,
                           float gamma_max, float p, float n_e) {

  // Power-law spectrum
  float spectrum = power_law_spectrum(nu, B, gamma_min, gamma_max, p);

  // Scale by electron density
  return spectrum * n_e;
}

#endif // SYNCHROTRON_EMISSION_GLSL
