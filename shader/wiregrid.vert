/**
 * @file wiregrid.vert
 * @brief Vertex shader for the spacetime wireframe grid.
 *
 * Transforms grid vertices into clip space using a view-projection matrix
 * and forwards the world-space position to the fragment stage for distance
 * and curvature-based effects.
 * Key uniforms: viewProj (mat4, location 0).
 * Inputs: position (vec3, location 0).
 * Outputs: gl_Position (clip space), worldPos (vec3, world space).
 */
#version 460 core

layout(location = 0) in vec3 position;

layout(location = 0) uniform mat4 viewProj;

out vec3 worldPos;

void main() {
  worldPos = position;
  gl_Position = viewProj * vec4(position, 1.0);
}