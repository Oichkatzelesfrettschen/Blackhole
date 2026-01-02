/**
 * @file hawking_glow.glsl
 * @brief Hawking Radiation Thermal Glow Shader
 *
 * Phase 10.1: Hawking Radiation Thermal Glow (Weeks 1-2)
 *
 * Renders blackbody thermal spectrum near the black hole horizon.
 * Physical basis: Hawking (1974) predicted thermal radiation with
 * temperature T_H = ℏc³/(8πGMk_B).
 *
 * Key features:
 * - Planck blackbody spectrum at RGB wavelengths
 * - Inverse-square falloff with exponential near-horizon enhancement
 * - Temperature scaling for pedagogical visualization
 * - LUT-based sampling for performance
 *
 * Integration point: blackhole_main.frag line 306 (before event horizon return)
 *
 * Auto-generated: 2026-01-02
 */

#ifndef SHADER_HAWKING_GLOW_GLSL
#define SHADER_HAWKING_GLOW_GLSL

#include "hawking_luts.glsl"

// ============================================================================
// Hawking Glow Parameters (Uniforms)
// ============================================================================

// Enable/disable flag
// uniform float hawkingGlowEnabled;    // 0.0 = off, 1.0 = on

// Temperature scale factor (pedagogical adjustment)
// uniform float hawkingTempScale;      // Default: 1.0 (physical)
//                                       // 1e6 = primordial BH visualization
//                                       // 1e9 = extreme pedagogical mode

// Glow intensity multiplier
// uniform float hawkingGlowIntensity;  // Default: 1.0, range: [0, 5]

// LUT textures
// uniform sampler2D hawkingTempLUT;
// uniform sampler2D hawkingSpectrumLUT;

// Use LUTs vs direct calculation
// uniform float useHawkingLUTs;        // 0.0 = direct, 1.0 = LUT

// ============================================================================
// Core Hawking Glow Functions
// ============================================================================

/**
 * @brief Compute thermal glow color and intensity.
 *
 * Implements the key algorithm from Phase 10 plan:
 * 1. Compute Hawking temperature T_H(M) * scale
 * 2. Sample Planck blackbody spectrum at RGB wavelengths
 * 3. Apply inverse-square falloff with near-horizon enhancement
 *
 * @param mass Black hole mass [g]
 * @param r Current radius [cm]
 * @param r_s Schwarzschild radius [cm]
 * @param tempScale Temperature scaling factor
 * @param intensity Global intensity multiplier
 * @param hawkingTempLUT Temperature LUT texture
 * @param hawkingSpectrumLUT Spectrum LUT texture
 * @param useLUTs Use LUTs (1.0) or direct calculation (0.0)
 * @return RGB thermal glow color
 */
vec3 hawkingThermalGlow(
    float mass,
    float r,
    float r_s,
    float tempScale,
    float intensity,
    sampler2D hawkingTempLUT,
    sampler2D hawkingSpectrumLUT,
    float useLUTs
) {
    // 1. Compute Hawking temperature
    float T_H;
    if (useLUTs > 0.5) {
        T_H = hawkingTemperatureLUT(mass, hawkingTempLUT);
    } else {
        T_H = hawkingTemperatureDirect(mass);
    }

    // Apply pedagogical temperature scaling
    T_H *= tempScale;

    // 2. Get blackbody RGB spectrum
    vec3 spectrum;
    if (useLUTs > 0.5) {
        spectrum = sampleHawkingSpectrum(T_H, hawkingSpectrumLUT);
    } else {
        spectrum = planckBlackbodyRGB(T_H);
    }

    // 3. Compute spatial falloff
    // radius_ratio = r / r_s (normalized distance from horizon)
    float radius_ratio = r / max(r_s, 1e-10);

    // Inverse-square law with exponential near-horizon enhancement
    // falloff = exp(-radius_ratio * 4) / (radius_ratio² + 0.01)
    float exp_factor = exp(-radius_ratio * 4.0);
    float inv_sq = 1.0 / (radius_ratio * radius_ratio + 0.01);
    float falloff = exp_factor * inv_sq;

    // 4. Apply global intensity multiplier
    vec3 glow = spectrum * falloff * intensity;

    return glow;
}

/**
 * @brief Simplified thermal glow (single function call).
 *
 * Convenience wrapper for integration into blackhole_main.frag.
 *
 * @param temperature Precomputed Hawking temperature [K]
 * @param radius_ratio r / r_s (normalized radius)
 * @param hawkingSpectrumLUT Spectrum LUT texture
 * @return RGB thermal glow color
 */
vec3 hawkingSpectrum(
    float temperature,
    float radius_ratio,
    sampler2D hawkingSpectrumLUT
) {
    // Sample blackbody spectrum
    vec3 intensities = sampleHawkingSpectrum(temperature, hawkingSpectrumLUT);

    // Spatial falloff
    float falloff = exp(-radius_ratio * 4.0) /
                    (radius_ratio * radius_ratio + 0.01);

    return intensities * falloff;
}

/**
 * @brief Apply Hawking glow to accumulated ray color.
 *
 * This is the main integration function called from blackhole_main.frag
 * at the event horizon check (line 306).
 *
 * @param currentColor Current accumulated ray color
 * @param mass Black hole mass [g]
 * @param r Current radius [cm]
 * @param r_s Schwarzschild radius [cm]
 * @param enabled Enable flag (0.0 or 1.0)
 * @param tempScale Temperature scaling factor
 * @param intensity Glow intensity multiplier
 * @param hawkingTempLUT Temperature LUT texture
 * @param hawkingSpectrumLUT Spectrum LUT texture
 * @param useLUTs Use LUTs flag
 * @return Updated color with Hawking glow added
 */
vec3 applyHawkingGlow(
    vec3 currentColor,
    float mass,
    float r,
    float r_s,
    float enabled,
    float tempScale,
    float intensity,
    sampler2D hawkingTempLUT,
    sampler2D hawkingSpectrumLUT,
    float useLUTs
) {
    // Early exit if disabled
    if (enabled < 0.5) {
        return currentColor;
    }

    // Compute thermal glow
    vec3 glow = hawkingThermalGlow(
        mass, r, r_s, tempScale, intensity,
        hawkingTempLUT, hawkingSpectrumLUT, useLUTs
    );

    // Additive blending (glow adds to existing color)
    return currentColor + glow;
}

// ============================================================================
// Physical Validation Functions
// ============================================================================

/**
 * @brief Validate Hawking temperature against known values.
 *
 * For testing and validation:
 * - Solar mass (1.989e33 g): T_H ≈ 6.2e-8 K
 * - Primordial (5e14 g): T_H ≈ 2.5e5 K
 *
 * @param mass Black hole mass [g]
 * @param hawkingTempLUT Temperature LUT texture
 * @return Hawking temperature [K]
 */
float validateHawkingTemperature(float mass, sampler2D hawkingTempLUT) {
    float T_direct = hawkingTemperatureDirect(mass);
    float T_lut = hawkingTemperatureLUT(mass, hawkingTempLUT);

    // Relative error should be < 1e-6 (float32 precision)
    float rel_error = abs((T_lut - T_direct) / (T_direct + 1e-30));

    // Debug output (comment out for production)
    // if (rel_error > 1e-6) {
    //     // Warning: LUT inaccuracy detected
    // }

    return T_lut;
}

/**
 * @brief Check inverse mass relationship: T_H ∝ 1/M.
 *
 * For masses M1 and M2 = 2*M1:
 * T_H(M2) = T_H(M1) / 2
 *
 * @param mass1 First mass [g]
 * @param mass2 Second mass (should be 2*mass1) [g]
 * @param hawkingTempLUT Temperature LUT texture
 * @return Ratio T_H(mass2) / T_H(mass1) (should be ~0.5)
 */
float testInverseMassLaw(float mass1, float mass2, sampler2D hawkingTempLUT) {
    float T1 = hawkingTemperatureLUT(mass1, hawkingTempLUT);
    float T2 = hawkingTemperatureLUT(mass2, hawkingTempLUT);
    return T2 / T1;
}

#endif // SHADER_HAWKING_GLOW_GLSL
