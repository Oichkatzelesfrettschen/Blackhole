/**
 * @file bloom_composite.frag
 * @brief Bloom final composite: blends the tonemapped scene with the bloom buffer.
 *
 * Adds the blurred bloom texture to the base scene image, weighted by
 * bloomStrength, and scales the scene contribution by the tone factor.
 * Key uniforms: texture0 (scene), texture1 (bloom), tone, bloomStrength, resolution.
 * Inputs: uv (interpolated texture coordinates).
 * Outputs: fragColor (composited HDR image).
 */
#version 460 core

layout(location = 0) in vec2 uv;

out vec4 fragColor;

uniform float tone = 1.0;
uniform float bloomStrength = 0.1;

uniform sampler2D texture0;
uniform sampler2D texture1;

uniform vec2 resolution; // viewport resolution in pixels

void main() {
  fragColor =
      texture(texture0, uv) * tone + texture(texture1, uv) * bloomStrength;
}
