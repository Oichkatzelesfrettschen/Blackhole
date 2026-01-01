#version 460 core

layout(binding = 0) uniform sampler2D texture0;

struct DrawInstance {
  vec4 offsetScale;
  vec4 tint;
  vec4 flags;
};

layout(std430, binding = 3) readonly buffer DrawInstances {
  DrawInstance instances[];
};

layout(location = 0) in vec2 uv;
layout(location = 1) flat in uint drawId;
layout(location = 2) flat in uint instanceId;

out vec4 fragColor;

void main() {
  DrawInstance data = instances[instanceId];
  float enabled = step(0.5, data.flags.x);
  vec4 base = texture(texture0, uv);
  vec3 tint = mix(data.tint.rgb * 0.9, data.tint.rgb, drawId == 0 ? 1.0 : 0.8);
  fragColor = vec4(base.rgb * tint, base.a * data.tint.a * enabled);
}
