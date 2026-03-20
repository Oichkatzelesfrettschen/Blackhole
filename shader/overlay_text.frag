/**
 * @file overlay_text.frag
 * @brief Simple color-passthrough fragment shader for HUD text rendering.
 *
 * Passes the per-vertex color directly to the framebuffer with no texture
 * sampling or additional processing.
 * Inputs: vColor (vec4, location 0).
 * Outputs: fragColor (vColor unchanged).
 */
#version 460 core

layout(location = 0) in vec4 vColor;
out vec4 fragColor;

void main() {
  fragColor = vColor;
}
