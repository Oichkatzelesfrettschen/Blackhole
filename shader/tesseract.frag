#version 460 core
/**
 * @file tesseract.frag
 * @brief Emissive shading for the speculative tesseract scene ribbons.
 *
 * Render-only content (Thorne, The Science of Interstellar ch. 29-31); not
 * physics. Tesseract edges glow a cool blue, world-tube strands a dim amber
 * brightened by the lit-moment Gaussian exp(-(t - litMoment)^2 / (2 w^2)),
 * and the gravity-message
 * pulse adds a travelling Gaussian at library time pulseTime on strand
 * pulseStrand. The profile across each ribbon falls off smoothly so bloom
 * reads the ribbons as light rather than as flat bars. Output is linear HDR
 * radiance, summed additively into the scene target; alpha is 1.
 */

layout(location = 0) in float vLibraryTime;
layout(location = 1) noperspective in float vAcross; // Screen-space, as tesseract.vert writes it.
layout(location = 2) in float vFade;
layout(location = 3) flat in int vKind;
layout(location = 4) flat in int vStrand;

uniform float litMoment;
uniform float litWidth;
uniform float pulseTime;
uniform float pulseWidth;
uniform int pulseEnabled;
uniform int pulseStrand;
uniform float edgeIntensity;
uniform float strandIntensity;
uniform float sliceIntensity;

layout(location = 0) out vec4 fragColor;

const int KIND_EDGE = 0;
const int KIND_WORLD_TUBE = 1;

const vec3 EDGE_COLOR = vec3(0.35, 0.55, 1.0);
const vec3 STRAND_COLOR = vec3(0.9, 0.62, 0.28);
const vec3 SLICE_COLOR = vec3(1.0, 0.82, 0.55);
const vec3 PULSE_COLOR = vec3(0.65, 0.92, 1.0);

// Mirrors litMomentEmission in src/render/tesseract/tesseract_geometry.cpp
// (EMISSION_MIN_WIDTH = 1e-4); tests/tesseract_geometry_test.cpp checks it.
const float EMISSION_MIN_WIDTH = 1e-4;

float gaussian(float x, float center, float width) {
  float u = (x - center) / max(width, EMISSION_MIN_WIDTH);
  return exp(-0.5 * u * u);
}

void main() {
  float across = 1.0 - abs(vAcross);
  float profile = across * across * (3.0 - 2.0 * across);

  vec3 radiance;
  if (vKind == KIND_EDGE) {
    radiance = EDGE_COLOR * edgeIntensity;
  } else if (vKind == KIND_WORLD_TUBE) {
    float lit = gaussian(vLibraryTime, litMoment, litWidth);
    radiance = STRAND_COLOR * strandIntensity * (0.2 + 3.0 * lit);
    if (pulseEnabled != 0 && vStrand == pulseStrand) {
      radiance += PULSE_COLOR * 6.0 * gaussian(vLibraryTime, pulseTime, pulseWidth);
    }
  } else {
    radiance = SLICE_COLOR * sliceIntensity;
  }

  fragColor = vec4(radiance * profile * vFade, 1.0);
}
