#version 460 core

layout(location = 0) in vec3 position;

struct DrawInstance {
  vec4 offsetScale;
  vec4 tint;
  vec4 flags;
};

layout(std430, binding = 3) readonly buffer DrawInstances {
  DrawInstance instances[];
};

layout(location = 0) out vec2 uv;
layout(location = 1) flat out uint drawId;
layout(location = 2) flat out uint instanceId;

void main() {
  uint inst = uint(gl_BaseInstance);
  DrawInstance data = instances[inst];
  vec2 scaled = position.xy * data.offsetScale.zw + data.offsetScale.xy;
  uv = position.xy * 0.5 + 0.5;
  drawId = uint(gl_DrawID);
  instanceId = inst;
  gl_Position = vec4(scaled, position.z, 1.0);
}
