#version 460 core

layout(location = 0) in vec3 position;

layout(location = 0) uniform mat4 viewProj;

out vec3 worldPos;

void main() {
  worldPos = position;
  gl_Position = viewProj * vec4(position, 1.0);
}