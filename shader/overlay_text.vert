/**
 * @file overlay_text.vert
 * @brief Vertex shader for screen-space HUD text rendering.
 *
 * Converts pixel-space positions to normalized device coordinates using the
 * screen size uniform, and forwards the per-vertex color to the fragment stage.
 * Key uniforms: uScreenSize (viewport dimensions in pixels).
 * Inputs: inPos (vec2, pixel coords, location 0), inColor (vec4, location 1).
 * Outputs: gl_Position (NDC), vColor (vec4).
 */
#version 460 core

layout(location = 0) in vec2 inPos;
layout(location = 1) in vec4 inColor;

uniform vec2 uScreenSize;

layout(location = 0) out vec4 vColor;

void main() {
  vec2 ndc;
  ndc.x = (inPos.x / uScreenSize.x) * 2.0 - 1.0;
  ndc.y = 1.0 - (inPos.y / uScreenSize.y) * 2.0;
  gl_Position = vec4(ndc, 0.0, 1.0);
  vColor = inColor;
}
