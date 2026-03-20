/**
 * @file synchrotron_lut.glsl
 * @brief Synchrotron emissivity LUT sampling helper (placeholder).
 *
 * Provides sampleSynchLUT() which maps log10(n_e) and log10(B) to a 4-band
 * synchrotron emissivity RGBA value.  Real LUT data is generated offline
 * and uploaded by the CPU at runtime.
 * Key uniforms: uSynchLUT (sampler2D, binding 0; axes: log n_e, log B).
 * Inputs: logNe (log10 electron number density), logB (log10 magnetic field strength).
 * Outputs: vec4 emissivity at four spectral bands.
 */
#version 460 core
// Synchrotron emissivity LUT (placeholder). Real LUTs will be generated offline and uploaded.
layout(binding=0) uniform sampler2D uSynchLUT; // x: log10(n_e), y: log10(B), rgba: j_nu at bands

vec4 sampleSynchLUT(float logNe, float logB){
  vec2 uv = vec2(clamp((logNe+6.0)/12.0,0.0,1.0), clamp((logB+3.0)/6.0,0.0,1.0));
  return texture(uSynchLUT, uv);
}
