/**
 * @file passthrough.frag
 * @brief Simple full-screen texture blit fragment shader.
 *
 * Samples texture0 at the fragment's normalized screen coordinate and outputs
 * the result directly, with no post-processing.
 * Key uniforms: texture0 (source texture), resolution.
 * Inputs: gl_FragCoord.
 * Outputs: fragColor (unmodified texel from texture0).
 */
#version 460 core

out vec4 fragColor;

uniform vec2 resolution;
uniform sampler2D texture0;

void main() {
  vec2 uv = gl_FragCoord.xy / resolution;
  fragColor = texture(texture0, uv);
}