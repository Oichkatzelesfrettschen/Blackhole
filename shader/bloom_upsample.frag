/**
 * @file bloom_upsample.frag
 * @brief Bloom upsample pass: 2x box-filter upsample with additive accumulation.
 *
 * Performs a 4-tap box filter on texture0 and adds the result to texture1
 * (the previous pyramid level), building the upsampled bloom chain.
 * Key uniforms: texture0 (current level), texture1 (accumulation buffer), resolution.
 * Inputs: uv (interpolated texture coordinates).
 * Outputs: fragColor (upsampled level added to previous accumulation).
 */
#version 460 core

layout(location = 0) in vec2 uv;

out vec4 fragColor;

uniform vec2 resolution;
uniform sampler2D texture0;
uniform sampler2D texture1;

void main() {
  vec2 inputTexelSize = 1.0 / resolution * 0.5;
  vec4 o = inputTexelSize.xyxy * vec4(-1.0, -1.0, 1.0, 1.0); // Offset
  fragColor =
      0.25 * (texture(texture0, uv + o.xy) + texture(texture0, uv + o.zy) +
              texture(texture0, uv + o.xw) + texture(texture0, uv + o.zw));

  fragColor += texture(texture1, uv);
  fragColor.a = 1.0;
}
