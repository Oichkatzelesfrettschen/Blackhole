#version 460 core
// Synchrotron emissivity LUT (placeholder). Real LUTs will be generated offline and uploaded.
layout(binding=0) uniform sampler2D uSynchLUT; // x: log10(n_e), y: log10(B), rgba: j_nu at bands

vec4 sampleSynchLUT(float logNe, float logB){
  vec2 uv = vec2(clamp((logNe+6.0)/12.0,0.0,1.0), clamp((logB+3.0)/6.0,0.0,1.0));
  return texture(uSynchLUT, uv);
}
