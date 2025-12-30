#version 460 core

layout(location = 0) in vec2 inPos;
layout(location = 1) in vec4 inColor;

uniform vec2 uScreenSize;

out vec4 vColor;

void main() {
  vec2 ndc;
  ndc.x = (inPos.x / uScreenSize.x) * 2.0 - 1.0;
  ndc.y = 1.0 - (inPos.y / uScreenSize.y) * 2.0;
  gl_Position = vec4(ndc, 0.0, 1.0);
  vColor = inColor;
}
