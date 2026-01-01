#version 460 core

layout(location = 0) in vec4 vColor;
out vec4 fragColor;

void main() {
  fragColor = vColor;
}
