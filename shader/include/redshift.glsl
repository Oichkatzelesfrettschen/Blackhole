/**
 * redshift.glsl
 * Gravitational and Doppler redshift functions for color correction.
 *
 * Implements physically accurate wavelength shifting for black hole rendering.
 */

#ifndef REDSHIFT_GLSL
#define REDSHIFT_GLSL

// ============================================================================
// Wavelength Constants (nanometers)
// ============================================================================

const float WAVELENGTH_RED = 700.0;
const float WAVELENGTH_GREEN = 546.0;
const float WAVELENGTH_BLUE = 436.0;

const float WAVELENGTH_MIN = 380.0;  // Violet
const float WAVELENGTH_MAX = 780.0;  // Red

// ============================================================================
// Redshift Calculations
// ============================================================================

/**
 * Apply redshift to a wavelength.
 * λ_observed = λ_emitted * (1 + z)
 */
float applyRedshift(float wavelength, float z) {
    return wavelength * (1.0 + z);
}

/**
 * Apply blueshift (negative redshift).
 * λ_observed = λ_emitted / (1 + |z|)
 */
float applyBlueshift(float wavelength, float z) {
    return wavelength / (1.0 + abs(z));
}

/**
 * Combined gravitational + Doppler redshift.
 *
 * z_total = (1 + z_grav)(1 + z_doppler) - 1
 *
 * @param r Radial position
 * @param r_s Schwarzschild radius
 * @param v_los Line-of-sight velocity (positive = receding)
 */
float totalRedshift(float r, float r_s, float v_los) {
    // Gravitational redshift: z_g = 1/√(1 - r_s/r) - 1
    // This is exact for static observers in Schwarzschild spacetime
    float f = max(1.0 - r_s / r, 0.001);
    float z_grav = 1.0 / sqrt(f) - 1.0;

    // Relativistic longitudinal Doppler effect (exact formula):
    // z_d = √((1+β)/(1-β)) - 1  where β = v/c
    // For receding source (v > 0): redshift
    // For approaching source (v < 0): blueshift
    float v_clamped = clamp(v_los, -0.99, 0.99);
    float z_doppler = sqrt((1.0 + v_clamped) / (1.0 - v_clamped)) - 1.0;

    // Combined relativistic formula: (1+z_total) = (1+z_grav)(1+z_doppler)
    // This multiplicative form is exact for the composition of redshifts
    return (1.0 + z_grav) * (1.0 + z_doppler) - 1.0;
}

// ============================================================================
// Wavelength to Color Conversion
// ============================================================================

/**
 * Convert wavelength to RGB color using CIE color matching approximation.
 *
 * Based on Dan Bruton's approximate algorithm.
 */
vec3 wavelengthToRGB(float wavelength) {
    float r = 0.0, g = 0.0, b = 0.0;

    if (wavelength >= 380.0 && wavelength < 440.0) {
        r = -(wavelength - 440.0) / (440.0 - 380.0);
        g = 0.0;
        b = 1.0;
    } else if (wavelength >= 440.0 && wavelength < 490.0) {
        r = 0.0;
        g = (wavelength - 440.0) / (490.0 - 440.0);
        b = 1.0;
    } else if (wavelength >= 490.0 && wavelength < 510.0) {
        r = 0.0;
        g = 1.0;
        b = -(wavelength - 510.0) / (510.0 - 490.0);
    } else if (wavelength >= 510.0 && wavelength < 580.0) {
        r = (wavelength - 510.0) / (580.0 - 510.0);
        g = 1.0;
        b = 0.0;
    } else if (wavelength >= 580.0 && wavelength < 645.0) {
        r = 1.0;
        g = -(wavelength - 645.0) / (645.0 - 580.0);
        b = 0.0;
    } else if (wavelength >= 645.0 && wavelength <= 780.0) {
        r = 1.0;
        g = 0.0;
        b = 0.0;
    }

    // Intensity falloff at edges of visible spectrum
    float factor = 1.0;
    if (wavelength >= 380.0 && wavelength < 420.0) {
        factor = 0.3 + 0.7 * (wavelength - 380.0) / (420.0 - 380.0);
    } else if (wavelength >= 700.0 && wavelength <= 780.0) {
        factor = 0.3 + 0.7 * (780.0 - wavelength) / (780.0 - 700.0);
    }

    // Handle out-of-range wavelengths
    if (wavelength < 380.0) {
        // UV - show as faint violet
        r = 0.5;
        g = 0.0;
        b = 1.0;
        factor = max(0.0, 1.0 - (380.0 - wavelength) / 100.0);
    } else if (wavelength > 780.0) {
        // IR - show as faint red
        r = 1.0;
        g = 0.0;
        b = 0.0;
        factor = max(0.0, 1.0 - (wavelength - 780.0) / 200.0);
    }

    return vec3(r, g, b) * factor;
}

// ============================================================================
// Color Shift Functions
// ============================================================================

/**
 * Apply gravitational redshift to RGB color.
 *
 * Converts color to approximate wavelength, applies redshift,
 * then converts back to RGB.
 */
vec3 applyGravitationalRedshift(vec3 color, float z) {
    // Estimate dominant wavelength from RGB
    // Simple weighted average approximation
    float luminance = dot(color, vec3(0.299, 0.587, 0.114));
    if (luminance < 0.01) {
        return color; // Black stays black
    }

    // Estimate wavelength from color balance
    float r_weight = color.r / (color.r + color.g + color.b + 0.001);
    float b_weight = color.b / (color.r + color.g + color.b + 0.001);

    // Approximate wavelength: more red = longer, more blue = shorter
    float est_wavelength = 550.0 + 150.0 * (r_weight - b_weight);
    est_wavelength = clamp(est_wavelength, 400.0, 700.0);

    // Apply redshift
    float shifted_wavelength = applyRedshift(est_wavelength, z);

    // Convert back to RGB
    vec3 shifted_color = wavelengthToRGB(shifted_wavelength);

    // Preserve original intensity
    float orig_intensity = length(color);
    float new_intensity = length(shifted_color);
    if (new_intensity > 0.01) {
        shifted_color *= orig_intensity / new_intensity;
    }

    return shifted_color;
}

/**
 * Simple intensity-based redshift (faster, less accurate).
 *
 * Physically, specific intensity transforms as I_ν/ν³ = const (Liouville).
 * This gives different power laws depending on what's measured:
 *
 * - Monochromatic specific intensity: I_obs = I_emit * (1+z)^(-3)
 * - Bolometric flux (all frequencies): F_obs = F_emit * (1+z)^(-4)
 * - Surface brightness: Σ_obs = Σ_emit * (1+z)^(-4)
 *
 * For visualization, we use (1+z)^(-3) as a compromise that captures
 * the dominant dimming effect without full spectral integration.
 */
vec3 applySimpleRedshift(vec3 color, float z) {
    float one_plus_z = 1.0 + z;
    // Using power of 3 for specific intensity transformation
    float dimming = 1.0 / (one_plus_z * one_plus_z * one_plus_z);
    return color * dimming;
}

/**
 * Apply Doppler shift for moving source.
 *
 * @param color Source color
 * @param v_los Line-of-sight velocity (-1 to 1, where 1 = c)
 */
vec3 applyDopplerShift(vec3 color, float v_los) {
    // Relativistic Doppler: z = √((1+v)/(1-v)) - 1
    float v_clamped = clamp(v_los, -0.99, 0.99);
    float z = sqrt((1.0 + v_clamped) / (1.0 - v_clamped)) - 1.0;
    return applyGravitationalRedshift(color, z);
}

// ============================================================================
// Beaming Effect
// ============================================================================

/**
 * Relativistic beaming (Doppler boosting) intensity modification.
 *
 * The Doppler factor δ = 1/(γ(1 - β·n̂)) relates observed to emitted quantities.
 * Different observables transform with different powers of δ:
 *
 * - Frequency: ν_obs = δ * ν_emit
 * - Specific intensity at fixed ν: I_ν,obs = δ³ * I_ν,emit  (Liouville)
 * - Bolometric intensity: I_obs = δ⁴ * I_emit (includes ν factor)
 * - Flux from moving blob: F_obs = δ⁴ * F_emit (thermal sources)
 * - Jet continuous emission: F_obs = δ^(2+α) where α is spectral index
 *
 * For accretion disk emission (thermal, quasi-isotropic), use δ⁴.
 * For optically thin synchrotron jets, use δ^(3+α) ≈ δ³ for flat spectrum.
 *
 * @param v_los Line-of-sight velocity (positive = receding, β = v/c)
 * @param is_thermal true for thermal sources (δ⁴), false for jets (δ³)
 */
float relativisticBeaming(float v_los, bool is_thermal) {
    float v_clamped = clamp(v_los, -0.99, 0.99);
    float gamma = 1.0 / sqrt(1.0 - v_clamped * v_clamped);
    float delta = 1.0 / (gamma * (1.0 - v_clamped));

    if (is_thermal) {
        // δ⁴ for thermal emission (accretion disk, stars)
        float d2 = delta * delta;
        return d2 * d2;
    } else {
        // δ³ for optically thin continuous emission (jets, α≈0)
        return delta * delta * delta;
    }
}

// Convenience wrapper using thermal (δ⁴) by default for disk emission
float relativisticBeaming(float v_los) {
    return relativisticBeaming(v_los, true);
}

#endif // REDSHIFT_GLSL
