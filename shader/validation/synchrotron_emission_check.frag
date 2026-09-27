#version 460
#extension GL_GOOGLE_include_directive : require
// Compiles shader/include/synchrotron_emission.glsl for validate-shaders; no
// render pass loads this file.
#include "synchrotron_emission.glsl"

layout(location = 0) out vec4 fragColor;

void main() {
  float x = gl_FragCoord.x * 0.01;
  fragColor = vec4(synchrotron_F(x), synchrotron_G(x), polarization_degree(x), 1.0);
}
