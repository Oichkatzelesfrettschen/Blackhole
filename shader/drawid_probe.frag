/**
 * @file drawid_probe.frag
 * @brief Debug fragment shader that colors geometry by gl_DrawID.
 *
 * Assigns a distinct semi-transparent color per draw call (blue for draw 0,
 * orange for draw 1+) to help diagnose multi-draw-indirect batching.
 * Inputs: drawId (flat int from vertex shader).
 * Outputs: fragColor (color coded by draw call index, alpha = 0.35).
 */
#version 460 core

layout(location = 0) flat in int drawId;
out vec4 fragColor;

void main() {
  vec3 color = (drawId == 0) ? vec3(0.1, 0.65, 1.0) : vec3(1.0, 0.4, 0.1);
  fragColor = vec4(color, 0.35);
}
