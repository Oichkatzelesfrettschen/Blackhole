/**
 * @file drawid_probe.vert
 * @brief Debug vertex shader that positions two side-by-side draw call quads.
 *
 * Separates draw 0 and draw 1 into left/right halves of the viewport using
 * gl_DrawID, and forwards the draw ID to the fragment stage for color coding.
 * Inputs: position (vec3, location 0).
 * Outputs: gl_Position, drawId (flat int).
 */
#version 460 core

layout(location = 0) in vec3 position;

layout(location = 0) flat out int drawId;

void main() {
  int id = int(gl_DrawID);
  float scale = 0.5;
  float offset = (id == 0) ? -0.5 : 0.5;
  vec3 pos = position;
  pos.x = pos.x * scale + offset;
  drawId = id;
  gl_Position = vec4(pos, 1.0);
}
