#version 460 core

in vec2 uv;
out vec4 fragColor;

uniform sampler3D grmhdTexture;
uniform sampler2D colorMap;
uniform float sliceAxis;
uniform float sliceCoord;
uniform float sliceChannel;
uniform float sliceMin;
uniform float sliceMax;
uniform float useColorMap;

float selectChannel(vec4 sampleValue, int channel) {
  if (channel == 0) {
    return sampleValue.r;
  }
  if (channel == 1) {
    return sampleValue.g;
  }
  if (channel == 2) {
    return sampleValue.b;
  }
  return sampleValue.a;
}

void main() {
  float axis = sliceAxis;
  float coord = clamp(sliceCoord, 0.0, 1.0);
  vec3 sampleCoord;
  if (axis < 0.5) {
    sampleCoord = vec3(coord, uv.x, uv.y);
  } else if (axis < 1.5) {
    sampleCoord = vec3(uv.x, coord, uv.y);
  } else {
    sampleCoord = vec3(uv.x, uv.y, coord);
  }

  vec4 sampleValue = texture(grmhdTexture, sampleCoord);
  int channel = int(clamp(sliceChannel, 0.0, 3.0) + 0.5);
  float value = selectChannel(sampleValue, channel);

  float denom = max(sliceMax - sliceMin, 1e-6);
  float u = clamp((value - sliceMin) / denom, 0.0, 1.0);
  vec3 color = useColorMap > 0.5 ? texture(colorMap, vec2(u, 0.5)).rgb : vec3(u);
  fragColor = vec4(color, 1.0);
}
