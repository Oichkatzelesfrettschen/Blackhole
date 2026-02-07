#version 460 core

/**
 * @file grmhd_raytracer_composite.frag
 * @brief Phase 6.3: Composite raytracer combining GPU geodesics with GRMHD fields (Fragment Shader)
 *
 * Execution: Reads rays from texture, samples GRMHD fields (simplified),
 * computes emitted radiation and outputs composite image.
 *
 * Integration: Phase 6.1a rays + Phase 6.2b GRMHD -> image
 */

in vec2 uv;
out vec4 fragColor;

// ============================================================================
// Inputs
// ============================================================================

uniform sampler2D rayTexture; // Contains color (rgb) and depth (a)

// ============================================================================
// Constants
// ============================================================================

const float PI = 3.14159265358979;
const float C = 2.99792458e8;  // Speed of light (m/s)

// ============================================================================
// Synchrotron Emission Model
// ============================================================================

/**
 * SynchrotronFraction: ratio of synchrotron to total radiation
 * Depends on: B field strength, electron temperature, density
 */
float synchrotronFraction(float B_strength, float temp) {
    // Simplified: strong B -> high synchrotron
    return min(1.0, B_strength * B_strength / (temp + 1.0));
}

/**
 * PlasmaFrequency: electron plasma frequency
 * ωp = sqrt(n_e * e^2 / (m_e * ε0))
 */
float plasmaFrequency(float density) {
    // Simplified: f_p ~ sqrt(n_e)
    return sqrt(abs(density) + 0.1);
}

// ============================================================================
// GRMHD Sampling (placeholder)
// ============================================================================

vec4 sampleGRMHDField(vec3 coord) {
    // Placeholder: would sample 3D texture in fragment shader
    // Returns (rho, uu, B_mag, T_eff)
    return vec4(0.1, 0.05, 1.0, 1e6);
}

// ============================================================================
// Main
// ============================================================================

void main() {
    vec4 rayResult = texture(rayTexture, uv);
    float depth = rayResult.a;
    
    // Phase 1: Ray result is base color
    vec4 outputColor = vec4(rayResult.rgb, 1.0);
    
    // Phase 2: If ray hit accretion disk (depth > 0), sample GRMHD
    if (depth >= 0.0 && depth < 1e6) {
        // Reconstruct world coordinate from ray (simplified)
        // In fragment shader, would use actual ray reconstruction from UV
        vec3 worldCoord = vec3(depth, uv.y * PI, uv.x * 2.0 * PI);
        
        // Sample GRMHD field
        vec4 grmhdField = sampleGRMHDField(worldCoord);
        
        // Compute synchrotron contribution
        float synchFrac = synchrotronFraction(grmhdField.z, grmhdField.w);
        
        // Blend: ray color (doppler-beamed photon) + synchrotron (local plasma)
        vec3 rayColor = outputColor.rgb;
        vec3 syncColor = vec3(synchFrac) * (grmhdField.x + 0.5);  // Density-weighted
        
        outputColor.rgb = mix(rayColor, syncColor, 0.3);  // 30% synchrotron blend
    }
    
    // Phase 3: Output composite pixel
    fragColor = outputColor;
}
