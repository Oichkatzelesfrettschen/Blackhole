#version 460
#extension GL_GOOGLE_include_directive : require
#include "grmhd_dense_emission.glsl"

layout(location = 0) out vec4 fragColor;

void main() {
  fragColor = vec4(grmhdDensityWeight(vec4(gl_FragCoord.xy, 0.0, 0.0)));
}
