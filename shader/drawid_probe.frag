#version 460 core

layout(location = 0) flat in int drawId;
out vec4 fragColor;

void main() {
  vec3 color = (drawId == 0) ? vec3(0.1, 0.65, 1.0) : vec3(1.0, 0.4, 0.1);
  fragColor = vec4(color, 0.35);
}
