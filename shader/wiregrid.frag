#version 460 core

out vec4 fragColor;

layout(location = 4) uniform vec4 color;

void main() {
  fragColor = color;
}
