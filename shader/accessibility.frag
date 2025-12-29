#version 330 core

// Accessibility post-processing shader
// Implements: Colorblind simulation, color inversion, photosensitivity protection
// Based on research from:
// - https://www.inf.ufrgs.br/~oliveira/pubs_files/CVD_Simulation/CVD_Simulation.html
// - WCAG 2.3.1 flash thresholds
// - https://gist.github.com/jcdickinson/580b7fb5cc145cee8740

out vec4 FragColor;

in vec2 TexCoords;

uniform sampler2D texture0;         // Input texture
uniform sampler2D previousFrame;    // Previous frame for flash detection

uniform vec2 resolution;
uniform float time;

// Colorblind mode: 0=none, 1=protanopia, 2=deuteranopia, 3=tritanopia, 4=achromatopsia
// Passed as float from C++, cast to int in shader
uniform float colorblindMode;
uniform float colorblindStrength;   // 0.0-1.0 blend factor

// Photosensitivity settings
// Passed as float from C++, cast to int in shader
uniform float photosensitivityLevel;  // 0=none, 1=low, 2=medium, 3=high, 4=maximum
uniform float maxBloomIntensity;
uniform float maxFlashFrequency;

// Other effects (passed as float 0.0 or 1.0)
uniform float invertColors;
uniform float highContrast;

// ============================================================================
// RGB to LMS color space conversion matrices
// From: Machado, Oliveira, Fernandes (2009)
// ============================================================================

// RGB to LMS (sRGB primaries, D65 illuminant)
const mat3 RGB_TO_LMS = mat3(
    0.31399022, 0.15537241, 0.01775239,
    0.63951294, 0.75789446, 0.10944209,
    0.04649755, 0.08670142, 0.87256922
);

// LMS to RGB (inverse of above)
const mat3 LMS_TO_RGB = mat3(
     5.47221206, -1.12524190,  0.02980165,
    -4.64196010,  2.29317094, -0.19318073,
     0.16963708, -0.16789520,  1.16364789
);

// ============================================================================
// Colorblind simulation matrices (applied in LMS space)
// ============================================================================

// Protanopia: L cone deficiency (red-blind)
const mat3 PROTANOPIA_SIM = mat3(
    0.0, 1.05118294, -0.05116099,
    0.0, 1.0,         0.0,
    0.0, 0.0,         1.0
);

// Deuteranopia: M cone deficiency (green-blind)
const mat3 DEUTERANOPIA_SIM = mat3(
    1.0,        0.0, 0.0,
    0.9513092,  0.0, 0.04866992,
    0.0,        0.0, 1.0
);

// Tritanopia: S cone deficiency (blue-blind)
const mat3 TRITANOPIA_SIM = mat3(
    1.0,         0.0,        0.0,
    0.0,         1.0,        0.0,
    -0.86744736, 1.86727089, 0.0
);

// ============================================================================
// Photosensitivity protection
// Per WCAG 2.3.1: No more than 3 flashes per second
// Luminance change >10% of max is considered a flash
// ============================================================================

float calculateLuminance(vec3 color) {
    // Relative luminance per WCAG
    return 0.2126 * color.r + 0.7152 * color.g + 0.0722 * color.b;
}

vec3 applyPhotosensitivityProtection(vec3 currentColor, vec3 previousColor, int level) {
    if (level == 0) return currentColor;

    float currentLum = calculateLuminance(currentColor);
    float previousLum = calculateLuminance(previousColor);
    float lumChange = abs(currentLum - previousLum);

    // WCAG threshold: 10% luminance change with darker <0.8 is a flash
    float flashThreshold = 0.1;
    bool isFlash = lumChange > flashThreshold && min(currentLum, previousLum) < 0.8;

    if (isFlash) {
        // Dampen the flash based on protection level
        float dampFactor = 1.0;
        switch (level) {
            case 1: dampFactor = 0.7; break;  // Low: 30% reduction
            case 2: dampFactor = 0.5; break;  // Medium: 50% reduction
            case 3: dampFactor = 0.3; break;  // High: 70% reduction
            case 4: dampFactor = 0.1; break;  // Maximum: 90% reduction
        }

        // Blend toward previous frame to reduce flash
        return mix(previousColor, currentColor, dampFactor);
    }

    return currentColor;
}

// ============================================================================
// Colorblind simulation/correction
// ============================================================================

vec3 applyColorblindFilter(vec3 color, int mode, float strength) {
    if (mode == 0 || strength <= 0.0) return color;

    // Convert to LMS
    vec3 lms = RGB_TO_LMS * color;

    // Apply simulation matrix
    vec3 simLms;
    switch (mode) {
        case 1: simLms = PROTANOPIA_SIM * lms; break;
        case 2: simLms = DEUTERANOPIA_SIM * lms; break;
        case 3: simLms = TRITANOPIA_SIM * lms; break;
        case 4:
            // Achromatopsia: convert to grayscale
            float gray = calculateLuminance(color);
            return mix(color, vec3(gray), strength);
        default: return color;
    }

    // Convert back to RGB
    vec3 simColor = LMS_TO_RGB * simLms;

    // Clamp to valid range
    simColor = clamp(simColor, 0.0, 1.0);

    // Blend based on strength
    return mix(color, simColor, strength);
}

// ============================================================================
// Color inversion (for high contrast needs)
// ============================================================================

vec3 applyColorInversion(vec3 color) {
    return vec3(1.0) - color;
}

// ============================================================================
// High contrast enhancement
// ============================================================================

vec3 applyHighContrast(vec3 color) {
    // Increase saturation and contrast
    float luminance = calculateLuminance(color);
    vec3 saturated = mix(vec3(luminance), color, 1.5);

    // Apply S-curve for contrast
    vec3 contrasted = saturated * saturated * (3.0 - 2.0 * saturated);

    return clamp(contrasted, 0.0, 1.0);
}

// ============================================================================
// Bloom intensity limiter for photosensitivity
// ============================================================================

vec3 limitBloomIntensity(vec3 color, float maxIntensity) {
    float luminance = calculateLuminance(color);

    if (luminance > maxIntensity) {
        // Scale down bright areas
        float scale = maxIntensity / luminance;
        return color * scale;
    }

    return color;
}

// ============================================================================
// Main
// ============================================================================

void main() {
    vec2 uv = gl_FragCoord.xy / resolution;

    vec3 color = texture(texture0, uv).rgb;
    vec3 prevColor = texture(previousFrame, uv).rgb;

    // Cast float uniforms to int for mode selection
    int cbMode = int(colorblindMode);
    int psLevel = int(photosensitivityLevel);

    // Apply photosensitivity protection first (most critical)
    if (psLevel > 0) {
        color = applyPhotosensitivityProtection(color, prevColor, psLevel);
        color = limitBloomIntensity(color, maxBloomIntensity);
    }

    // Apply colorblind filter
    if (cbMode > 0) {
        color = applyColorblindFilter(color, cbMode, colorblindStrength);
    }

    // Apply color inversion if enabled (float > 0.5 means true)
    if (invertColors > 0.5) {
        color = applyColorInversion(color);
    }

    // Apply high contrast if enabled (float > 0.5 means true)
    if (highContrast > 0.5) {
        color = applyHighContrast(color);
    }

    FragColor = vec4(color, 1.0);
}
