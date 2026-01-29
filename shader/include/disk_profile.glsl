/**
 * @file disk_profile.glsl
 * @brief Novikov-Thorne disk profile sampling for GPU rendering
 *
 * WHY: Physics-based accretion disk temperature and flux profiles
 * WHAT: LUT sampling of Novikov-Thorne thin disk model
 * HOW: 2D texture lookup with bilinear interpolation
 *
 * Usage:
 *   uniform sampler2D novikov_thorne_lut;
 *   vec2 temp_flux = sampleNovikovThorne(r, a_star);
 *   float temperature = temp_flux.r;
 *   float flux = temp_flux.g;
 */

#ifndef DISK_PROFILE_GLSL
#define DISK_PROFILE_GLSL

// Novikov-Thorne LUT parameters (must match generate_nt_lut.py)
const float NT_LUT_R_MIN = 1.0;
const float NT_LUT_R_MAX = 50.0;
const float NT_LUT_A_MIN = -0.998;
const float NT_LUT_A_MAX = 0.998;

/**
 * @brief Compute ISCO radius for Kerr black hole (BPT 1972)
 *
 * Matches src/physics/novikov_thorne.h::isco_radius()
 *
 * @param a_star Dimensionless spin parameter (-1 < a* < 1)
 * @return ISCO radius in units of M
 */
float isco_radius(float a_star) {
    a_star = clamp(a_star, -0.9999, 0.9999);

    float z1 = 1.0 + pow(1.0 - a_star * a_star, 1.0 / 3.0) *
                     (pow(1.0 + a_star, 1.0 / 3.0) + pow(1.0 - a_star, 1.0 / 3.0));
    float z2 = sqrt(3.0 * a_star * a_star + z1 * z1);

    // Prograde orbit ISCO
    return 3.0 + z2 - sign(a_star) * sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2));
}

/**
 * @brief Convert radius to normalized LUT coordinate
 *
 * Uses logarithmic spacing to match generate_nt_lut.py
 *
 * @param r Radius in units of M
 * @return Normalized coordinate u ∈ [0, 1]
 */
float radiusToLUTCoord(float r) {
    // Logarithmic mapping: r ∈ [R_MIN, R_MAX] → u ∈ [0, 1]
    float log_r = log(r);
    float log_r_min = log(NT_LUT_R_MIN);
    float log_r_max = log(NT_LUT_R_MAX);

    return (log_r - log_r_min) / (log_r_max - log_r_min);
}

/**
 * @brief Convert spin parameter to normalized LUT coordinate
 *
 * @param a_star Dimensionless spin parameter
 * @return Normalized coordinate v ∈ [0, 1]
 */
float spinToLUTCoord(float a_star) {
    // Linear mapping: a ∈ [A_MIN, A_MAX] → v ∈ [0, 1]
    return (a_star - NT_LUT_A_MIN) / (NT_LUT_A_MAX - NT_LUT_A_MIN);
}

/**
 * @brief Sample Novikov-Thorne disk profile from LUT
 *
 * Returns normalized temperature and flux values from precomputed LUT.
 * Values are 0 inside ISCO (no stable disk).
 *
 * @param lut Novikov-Thorne LUT texture (2D, RG32F)
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @return vec2(temperature, flux), both normalized to [0, 1]
 */
vec2 sampleNovikovThorne(sampler2D lut, float r, float a_star) {
    // Clamp to valid LUT range
    if (r < NT_LUT_R_MIN || r > NT_LUT_R_MAX) {
        return vec2(0.0);
    }

    a_star = clamp(a_star, NT_LUT_A_MIN, NT_LUT_A_MAX);

    // Convert to LUT coordinates
    float u = radiusToLUTCoord(r);
    float v = spinToLUTCoord(a_star);

    // Bilinear interpolation
    vec2 temp_flux = texture(lut, vec2(u, v)).rg;

    return temp_flux;
}

/**
 * @brief Sample disk temperature only
 *
 * Convenience wrapper for temperature sampling.
 *
 * @param lut Novikov-Thorne LUT texture
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @return Normalized temperature [0, 1]
 */
float sampleDiskTemperature(sampler2D lut, float r, float a_star) {
    return sampleNovikovThorne(lut, r, a_star).r;
}

/**
 * @brief Sample disk flux only
 *
 * Convenience wrapper for flux sampling.
 *
 * @param lut Novikov-Thorne LUT texture
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @return Normalized flux [0, 1]
 */
float sampleDiskFlux(sampler2D lut, float r, float a_star) {
    return sampleNovikovThorne(lut, r, a_star).g;
}

/**
 * @brief Compute disk emissivity color from temperature
 *
 * Maps normalized temperature to blackbody color (simplified Planck spectrum).
 * Uses Wien's displacement law approximation.
 *
 * @param T_normalized Normalized temperature [0, 1]
 * @param T_max Maximum temperature (from LUT metadata, e.g., 1e7 K)
 * @return RGB color (linear, not gamma-corrected)
 */
vec3 temperatureToColor(float T_normalized, float T_max) {
    // Absolute temperature
    float T_kelvin = T_normalized * T_max;

    // Wien's displacement: λ_peak = 2.898e6 / T (nm)
    float lambda_peak = 2.898e6 / max(T_kelvin, 1.0);

    // Map wavelength to RGB (simplified)
    // Visible: 380-750 nm
    // Blue-white: T > 10000 K (λ < 290 nm, UV)
    // White: T ~ 6000 K (λ ~ 500 nm, green-yellow)
    // Red-orange: T ~ 3000 K (λ ~ 1000 nm, IR)

    vec3 color;

    if (lambda_peak < 380.0) {
        // UV: bright blue-white
        color = vec3(0.6, 0.7, 1.0);
    } else if (lambda_peak < 440.0) {
        // Violet-blue
        float t = (440.0 - lambda_peak) / (440.0 - 380.0);
        color = mix(vec3(0.5, 0.0, 1.0), vec3(0.6, 0.7, 1.0), t);
    } else if (lambda_peak < 490.0) {
        // Blue
        float t = (490.0 - lambda_peak) / (490.0 - 440.0);
        color = mix(vec3(0.0, 0.0, 1.0), vec3(0.5, 0.0, 1.0), t);
    } else if (lambda_peak < 510.0) {
        // Cyan
        float t = (510.0 - lambda_peak) / (510.0 - 490.0);
        color = mix(vec3(0.0, 1.0, 1.0), vec3(0.0, 0.0, 1.0), t);
    } else if (lambda_peak < 580.0) {
        // Green-yellow
        float t = (580.0 - lambda_peak) / (580.0 - 510.0);
        color = mix(vec3(1.0, 1.0, 0.0), vec3(0.0, 1.0, 1.0), t);
    } else if (lambda_peak < 645.0) {
        // Yellow-orange
        float t = (645.0 - lambda_peak) / (645.0 - 580.0);
        color = mix(vec3(1.0, 0.5, 0.0), vec3(1.0, 1.0, 0.0), t);
    } else if (lambda_peak < 750.0) {
        // Orange-red
        float t = (750.0 - lambda_peak) / (750.0 - 645.0);
        color = mix(vec3(1.0, 0.0, 0.0), vec3(1.0, 0.5, 0.0), t);
    } else {
        // IR: deep red
        color = vec3(0.8, 0.0, 0.0);
    }

    // Apply intensity falloff for low temperatures
    float intensity = smoothstep(0.0, 0.2, T_normalized);
    color *= intensity;

    return color;
}

/**
 * @brief Compute disk color with Novikov-Thorne profile
 *
 * Combines temperature-to-color mapping with flux intensity.
 *
 * @param lut Novikov-Thorne LUT texture
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @param T_max Maximum temperature from LUT metadata (Kelvin)
 * @param flux_scale Flux intensity multiplier
 * @return RGB color (linear)
 */
vec3 novikovThorneDiskColor(sampler2D lut, float r, float a_star,
                             float T_max, float flux_scale) {
    vec2 temp_flux = sampleNovikovThorne(lut, r, a_star);

    float T_norm = temp_flux.r;
    float F_norm = temp_flux.g;

    // Temperature color
    vec3 color = temperatureToColor(T_norm, T_max);

    // Apply flux intensity
    color *= F_norm * flux_scale;

    return color;
}

/**
 * @brief Check if radius is inside ISCO (no stable disk)
 *
 * @param r Radius in units of M
 * @param a_star Dimensionless spin parameter
 * @return true if r < r_ISCO
 */
bool isInsideISCO(float r, float a_star) {
    return r < isco_radius(a_star);
}

/**
 * @brief Compute radial falloff factor for disk edge
 *
 * Smooth falloff at outer disk edge for visual continuity.
 *
 * @param r Radius in units of M
 * @param r_outer Outer disk radius
 * @param falloff_width Falloff width in M
 * @return Falloff factor [0, 1]
 */
float diskEdgeFalloff(float r, float r_outer, float falloff_width) {
    return 1.0 - smoothstep(r_outer - falloff_width, r_outer, r);
}

#endif // DISK_PROFILE_GLSL
