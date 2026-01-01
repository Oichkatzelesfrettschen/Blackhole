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
