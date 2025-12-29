#version 330 core

// Stereoblindness Accessibility Shader
// Implements monocular depth cues for users who cannot perceive stereoscopic depth
// Based on research from: https://en.wikipedia.org/wiki/Depth_perception

out vec4 fragColor;

uniform sampler2D texture0;       // Main scene color
uniform sampler2D depthTexture;   // Depth buffer (if available)
uniform vec2 resolution;
uniform float time;

// Depth cue settings (controlled from accessibility menu)
uniform float fogEnabled;         // 0.0 or 1.0
uniform float fogDensity;         // 0.0 - 1.0
uniform vec3 fogColor;            // Usually sky color or gray
uniform float fogStart;           // Distance where fog begins
uniform float fogEnd;             // Distance where fog is complete

uniform float edgeOutlinesEnabled;  // 0.0 or 1.0
uniform float edgeThreshold;        // 0.0 - 1.0
uniform vec3 edgeColor;             // Outline color
uniform float edgeWidth;            // 1.0 - 3.0

uniform float depthDesatEnabled;    // 0.0 or 1.0
uniform float desatStrength;        // 0.0 - 1.0

uniform float chromaDepthEnabled;   // 0.0 or 1.0 - warm near, cool far
uniform float motionParallaxHint;   // 0.0 or 1.0 - subtle motion indicator

// Near/far planes for depth linearization
uniform float nearPlane;
uniform float farPlane;

// ============================================================================
// Depth utilities
// ============================================================================

// Linearize depth from depth buffer (0-1 range to linear distance)
float linearizeDepth(float depth) {
    float z = depth * 2.0 - 1.0; // Back to NDC
    return (2.0 * nearPlane * farPlane) / (farPlane + nearPlane - z * (farPlane - nearPlane));
}

// Get normalized depth (0 = near, 1 = far)
float getNormalizedDepth(vec2 uv) {
    float depth = texture(depthTexture, uv).r;
    float linearDepth = linearizeDepth(depth);
    return clamp((linearDepth - nearPlane) / (farPlane - nearPlane), 0.0, 1.0);
}

// ============================================================================
// Distance Fog (Atmospheric Perspective)
// ============================================================================

vec3 applyFog(vec3 color, float depth) {
    if (fogEnabled < 0.5) return color;

    // Exponential squared fog for more natural falloff
    float fogFactor = 1.0 - exp(-pow(depth * fogDensity * 2.0, 2.0));
    fogFactor = clamp(fogFactor, 0.0, 1.0);

    // Apply start/end range
    float rangedDepth = smoothstep(fogStart, fogEnd, depth);
    fogFactor *= rangedDepth;

    return mix(color, fogColor, fogFactor);
}

// ============================================================================
// Edge Detection (Sobel-based)
// ============================================================================

float sobelEdge(vec2 uv) {
    vec2 texelSize = 1.0 / resolution;

    // Sample neighboring depths
    float tl = getNormalizedDepth(uv + vec2(-texelSize.x, -texelSize.y));
    float t  = getNormalizedDepth(uv + vec2(0.0, -texelSize.y));
    float tr = getNormalizedDepth(uv + vec2(texelSize.x, -texelSize.y));
    float l  = getNormalizedDepth(uv + vec2(-texelSize.x, 0.0));
    float r  = getNormalizedDepth(uv + vec2(texelSize.x, 0.0));
    float bl = getNormalizedDepth(uv + vec2(-texelSize.x, texelSize.y));
    float b  = getNormalizedDepth(uv + vec2(0.0, texelSize.y));
    float br = getNormalizedDepth(uv + vec2(texelSize.x, texelSize.y));

    // Sobel operators
    float gx = -tl - 2.0*l - bl + tr + 2.0*r + br;
    float gy = -tl - 2.0*t - tr + bl + 2.0*b + br;

    return sqrt(gx*gx + gy*gy);
}

vec3 applyEdgeOutlines(vec3 color, vec2 uv, float depth) {
    if (edgeOutlinesEnabled < 0.5) return color;

    float edge = sobelEdge(uv);

    // Threshold and scale
    edge = smoothstep(edgeThreshold * 0.1, edgeThreshold * 0.2, edge);

    // Make edges more visible at distance (helps depth perception)
    edge *= 1.0 + depth * 0.5;

    return mix(color, edgeColor, edge * edgeWidth * 0.3);
}

// ============================================================================
// Depth-based Desaturation
// ============================================================================

vec3 desaturate(vec3 color, float amount) {
    float luminance = dot(color, vec3(0.299, 0.587, 0.114));
    return mix(color, vec3(luminance), amount);
}

vec3 applyDepthDesaturation(vec3 color, float depth) {
    if (depthDesatEnabled < 0.5) return color;

    // Progressive desaturation with distance
    float desat = depth * desatStrength;
    return desaturate(color, desat);
}

// ============================================================================
// Chromatic Depth (Chromostereopsis)
// ============================================================================

vec3 applyChromaDepth(vec3 color, float depth) {
    if (chromaDepthEnabled < 0.5) return color;

    // Warm colors (red) appear closer, cool colors (blue) appear farther
    // Shift hue based on depth
    float warmShift = (1.0 - depth) * 0.1;  // Near: add warmth
    float coolShift = depth * 0.15;          // Far: add coolness

    vec3 warm = vec3(1.0 + warmShift, 1.0, 1.0 - warmShift * 0.5);
    vec3 cool = vec3(1.0 - coolShift * 0.3, 1.0, 1.0 + coolShift);

    vec3 tint = mix(warm, cool, depth);
    return color * tint;
}

// ============================================================================
// Motion Parallax Hint (subtle visual indicator)
// ============================================================================

vec3 applyMotionParallaxHint(vec3 color, float depth, vec2 uv) {
    if (motionParallaxHint < 0.5) return color;

    // Subtle animated pattern that moves faster for near objects
    float parallaxSpeed = 1.0 - depth;
    float pattern = sin((uv.x + time * parallaxSpeed * 0.1) * 50.0) * 0.02;

    // Only visible at edges of screen
    float edgeFade = 1.0 - smoothstep(0.0, 0.2, min(uv.x, 1.0 - uv.x));
    pattern *= edgeFade;

    return color + vec3(pattern);
}

// ============================================================================
// Main
// ============================================================================

void main() {
    vec2 uv = gl_FragCoord.xy / resolution;

    vec3 color = texture(texture0, uv).rgb;
    float depth = getNormalizedDepth(uv);

    // Apply depth cues in order of visual importance

    // 1. Edge outlines - enhances occlusion depth cue
    color = applyEdgeOutlines(color, uv, depth);

    // 2. Depth-based desaturation - atmospheric perspective
    color = applyDepthDesaturation(color, depth);

    // 3. Distance fog - strong atmospheric depth cue
    color = applyFog(color, depth);

    // 4. Chromatic depth - subtle but effective
    color = applyChromaDepth(color, depth);

    // 5. Motion parallax hint - very subtle
    color = applyMotionParallaxHint(color, depth, uv);

    fragColor = vec4(color, 1.0);
}
