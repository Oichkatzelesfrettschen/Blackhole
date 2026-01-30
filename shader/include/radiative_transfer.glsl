/**
 * @file radiative_transfer.glsl
 * @brief GPU implementation of radiative transfer for synchrotron emission
 *
 * Port of radiative transfer physics to GLSL 4.60
 * Integrates synchrotron emission with optical depth absorption
 *
 * References:
 * - Rybicki & Lightman (1979) "Radiative Processes in Astrophysics" Ch. 1-2
 * - Longair (2011) "High Energy Astrophysics" Ch. 1
 * - Frank, King, Raine (2002) "Accretion Power in Astrophysics" Ch. 2
 *
 * Performance: Target <1ms per ray for full radiative transfer
 */

#ifndef RADIATIVE_TRANSFER_GLSL
#define RADIATIVE_TRANSFER_GLSL

// ============================================================================
// Radiative Transfer Constants
// ============================================================================

/// Speed of light [cm/s]
const float C = 2.99792458e10;

/// Planck constant [erg * s]
const float PLANCK = 6.62607015e-27;

// ============================================================================
// Optical Depth Integration
// ============================================================================

/**
 * @brief Compute optical depth integral along a ray segment.
 *
 * tau = integral_0^L alpha(nu) * ds
 * where alpha(nu) is the absorption coefficient and L is path length.
 *
 * For discrete ray segments:
 * tau = sum(alpha_i * ds_i)
 *
 * @param alpha_nu Array of absorption coefficients at sample points
 * @param ds_array Array of path segment lengths [cm]
 * @param n_steps Number of integration steps
 * @return Cumulative optical depth (dimensionless)
 */
float optical_depth_integrate(float alpha_nu[], float ds_array[], int n_steps) {
  float tau = 0.0;

  // Trapezoidal rule integration
  for (int i = 0; i < n_steps - 1; i++) {
    float alpha_avg = 0.5 * (alpha_nu[i] + alpha_nu[i + 1]);
    tau += alpha_avg * ds_array[i];
  }

  return tau;
}

/**
 * @brief Compute transmission factor from optical depth.
 *
 * T_nu(tau) = exp(-tau)
 *
 * Represents fraction of radiation that escapes without absorption.
 *
 * @param tau Optical depth (dimensionless)
 * @return Transmission factor [0, 1]
 */
float transmission_factor(float tau) {
  // Clamp large tau to prevent numerical issues
  if (tau > 100.0) return 0.0;
  return exp(-tau);
}

/**
 * @brief Compute source function from emission and absorption.
 *
 * S_nu = j_nu / alpha_nu
 * where j_nu is emissivity and alpha_nu is absorption coefficient.
 *
 * When alpha_nu -> 0 (optically thin), use limit:
 * S_nu -> j_nu / alpha_nu (but limit to physical bounds)
 *
 * @param j_nu Emissivity [erg / s / cm^3 / Hz / sr]
 * @param alpha_nu Absorption coefficient [cm^-1]
 * @return Source function [erg / s / cm / Hz / sr]
 */
float source_function(float j_nu, float alpha_nu) {
  if (alpha_nu < 1e-30) {
    // Optically thin limit: direct emission
    return j_nu;
  }
  return j_nu / alpha_nu;
}

// ============================================================================
// Emission-Weighted Ray Marching
// ============================================================================

/**
 * @brief Accumulate intensity along a ray with absorption.
 *
 * Radiative transfer equation:
 * dI_nu/ds = j_nu - alpha_nu * I_nu
 *
 * Solution (discrete):
 * I_nu^(i+1) = I_nu^(i) * exp(-tau_i) + S_nu^(i) * (1 - exp(-tau_i))
 *
 * where S_nu is the source function and tau_i is optical depth of segment i.
 *
 * @param I_nu_current Current intensity [erg / s / cm^2 / Hz / sr]
 * @param j_nu Emissivity at position [erg / s / cm^3 / Hz / sr]
 * @param alpha_nu Absorption coefficient [cm^-1]
 * @param ds Path segment length [cm]
 * @return Updated intensity after propagation
 */
float intensity_step(float I_nu_current, float j_nu, float alpha_nu, float ds) {
  // Optical depth for this segment
  float tau_segment = alpha_nu * ds;

  // Clamp tau for numerical stability
  if (tau_segment > 100.0) tau_segment = 100.0;

  // Transmission and absorption factor
  float T = exp(-tau_segment);

  // Source function (emission/absorption ratio)
  float S = source_function(j_nu, alpha_nu);

  // Radiative transfer step
  // I = I_old * T + S * (1 - T)
  float I_nu_new = I_nu_current * T + S * (1.0 - T);

  return I_nu_new;
}

/**
 * @brief Accumulate emission along a ray path (optically thin approximation).
 *
 * For optically thin emission (tau << 1):
 * I_nu = integral j_nu(s) * ds
 *
 * This is the simplest case and fastest to compute.
 *
 * @param j_nu_array Emissivity array at sample points
 * @param ds_array Path segment lengths
 * @param n_steps Number of steps
 * @return Total accumulated intensity
 */
float intensity_optically_thin(float j_nu_array[], float ds_array[], int n_steps) {
  float I_nu = 0.0;

  for (int i = 0; i < n_steps - 1; i++) {
    // Trapezoidal integration
    float j_avg = 0.5 * (j_nu_array[i] + j_nu_array[i + 1]);
    I_nu += j_avg * ds_array[i];
  }

  return I_nu;
}

/**
 * @brief Full radiative transfer with absorption (optically thick).
 *
 * Implements step-by-step integration of radiative transfer equation
 * with proper handling of both optically thin and thick regimes.
 *
 * @param j_nu_array Emissivity at sample points
 * @param alpha_nu_array Absorption coefficient at sample points
 * @param ds_array Path segment lengths
 * @param n_steps Number of integration steps
 * @return Final intensity after full ray march
 */
float intensity_full_radiative_transfer(float j_nu_array[],
                                        float alpha_nu_array[],
                                        float ds_array[],
                                        int n_steps) {
  float I_nu = 0.0;

  // Ray march from source toward observer
  for (int i = 0; i < n_steps - 1; i++) {
    // Current segment properties
    float j_nu = j_nu_array[i];
    float alpha_nu = alpha_nu_array[i];
    float ds = ds_array[i];

    // Update intensity with this segment
    I_nu = intensity_step(I_nu, j_nu, alpha_nu, ds);
  }

  return I_nu;
}

// ============================================================================
// Multi-Frequency Spectral Integration
// ============================================================================

/**
 * @brief Integrate spectral energy over frequency range.
 *
 * For broadband observations spanning frequency range nu_min to nu_max:
 * F_total = integral_nu_min^nu_max F_nu(nu) dnu
 *
 * Implemented as weighted sum over frequency bins.
 *
 * @param F_nu_array Flux density at frequency samples [erg / s / cm^2 / Hz]
 * @param nu_array Frequency values at sample points [Hz]
 * @param n_freqs Number of frequency samples
 * @return Integrated flux [erg / s / cm^2]
 */
float integrate_spectrum(float F_nu_array[], float nu_array[], int n_freqs) {
  float F_total = 0.0;

  if (n_freqs < 2) return 0.0;

  // Trapezoidal integration in log-space (better for power laws)
  for (int i = 0; i < n_freqs - 1; i++) {
    float dnu_log = log(nu_array[i + 1] / nu_array[i]);
    float nu_avg = 0.5 * (nu_array[i] + nu_array[i + 1]);
    float F_avg = 0.5 * (F_nu_array[i] + F_nu_array[i + 1]);

    F_total += F_avg * nu_avg * dnu_log;
  }

  return F_total;
}

/**
 * @brief Convert synchrotron spectrum to RGB color.
 *
 * Maps synchrotron flux distribution to visual RGB:
 * - Low frequency (radio): Red
 * - Medium frequency (optical): Green
 * - High frequency (X-ray): Blue
 *
 * @param F_nu_array Flux density samples across spectrum
 * @param nu_array Frequency samples
 * @param n_freqs Number of samples
 * @return RGB color vector [0, 1]
 */
vec3 spectrum_to_rgb(float F_nu_array[], float nu_array[], int n_freqs) {
  vec3 rgb = vec3(0.0);

  // Define frequency band centers
  float nu_radio = 1e9;    // 1 GHz (radio)
  float nu_optical = 5e14; // 500 nm optical
  float nu_xray = 1e18;    // 100 nm soft X-ray

  // Interpolate flux at band centers
  // (This is simplified - would use actual interpolation in practice)
  float F_red = 0.0;    // Radio band
  float F_green = 0.0;  // Optical band
  float F_blue = 0.0;   // X-ray band

  // Sum contributions by spectral region
  for (int i = 0; i < n_freqs - 1; i++) {
    float nu_mid = 0.5 * (nu_array[i] + nu_array[i + 1]);
    float F_mid = 0.5 * (F_nu_array[i] + F_nu_array[i + 1]);

    // Assign to color channels based on frequency
    if (nu_mid < 1e13) {
      F_red += F_mid;   // Radio/sub-mm
    } else if (nu_mid < 1e15) {
      F_green += F_mid; // Optical
    } else {
      F_blue += F_mid;  // UV/X-ray
    }
  }

  // Normalize and apply color mapping
  float F_total = F_red + F_green + F_blue;
  if (F_total > 0.0) {
    rgb = vec3(F_red / F_total, F_green / F_total, F_blue / F_total);
  }

  // Apply logarithmic tone mapping for display
  rgb = log(1.0 + rgb) / log(2.0);

  return clamp(rgb, 0.0, 1.0);
}

// ============================================================================
// Convergence Testing Utilities
// ============================================================================

/**
 * @brief Compute optical depth convergence ratio.
 *
 * For convergence testing, compare results with n steps vs 2n steps.
 * Convergence ratio = error / (error_ref)
 *
 * Good convergence: ratio << 1
 * Poor convergence: ratio ~ 1 (need more steps)
 *
 * @param tau_n Optical depth with n steps
 * @param tau_2n Optical depth with 2n steps
 * @return Convergence ratio (0 = perfect, 1 = no improvement)
 */
float convergence_ratio(float tau_n, float tau_2n) {
  float error_n = abs(tau_n - tau_2n);
  float error_ref = abs(tau_2n) + 1e-10;  // Avoid division by zero
  return error_n / error_ref;
}

#endif // RADIATIVE_TRANSFER_GLSL
