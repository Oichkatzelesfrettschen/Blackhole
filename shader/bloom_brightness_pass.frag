/**
 * @file bloom_brightness_pass.frag
 * @brief Bloom pre-pass: extracts pixels above a luminance threshold.
 *
 * Samples the scene color and zeroes out any pixel whose luminance is below
 * brightPassThreshold (1.0), leaving only the brightest highlights for the
 * subsequent blur passes.
 * Key uniforms: texture0 (scene color), resolution.
 * Inputs: gl_FragCoord.
 * Outputs: fragColor (bright regions only, black elsewhere).
 */
#version 460 core

out vec4 fragColor;

uniform sampler2D texture0;
uniform vec2 resolution; // viewport resolution in pixels

// Exposed as a uniform so it can be tuned without shader recompile.
// Default 0.4: disk (0.3-0.9 linear) and photon ring (~1.06) both contribute.
// Old hardcoded value of 1.0 killed all disk emission.
uniform float brightPassThreshold = 0.4;
// Soft-knee half-width: smoothstep spans [threshold-knee, threshold+knee].
// Eliminates the hard cutoff edge that sign() produced.
uniform float brightPassKnee = 0.15;
const vec3 luminanceVector = vec3(0.2125, 0.7154, 0.0721);

void main() {
  vec2 texCoord = gl_FragCoord.xy / resolution.xy;

  vec4 c = texture(texture0, texCoord);

  float lum = dot(luminanceVector, c.xyz);
  // Smooth knee: 0 below (threshold-knee), 1 above (threshold+knee)
  float weight = smoothstep(brightPassThreshold - brightPassKnee,
                             brightPassThreshold + brightPassKnee,
                             lum);
  c.xyz *= weight;
  c.a = 1.0;

  fragColor = c;
}