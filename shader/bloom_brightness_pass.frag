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

const float brightPassThreshold = 1.0;
const vec3 luminanceVector = vec3(0.2125, 0.7154, 0.0721);

void main() {
  vec2 texCoord = gl_FragCoord.xy / resolution.xy;

  vec4 c = texture(texture0, texCoord);

  float luminance = dot(luminanceVector, c.xyz);
  luminance = max(0.0, luminance - brightPassThreshold);
  c.xyz *= sign(luminance);
  c.a = 1.0;

  fragColor = c;
}