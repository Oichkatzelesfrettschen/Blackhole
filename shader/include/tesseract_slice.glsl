#ifndef TESSERACT_SLICE_GLSL
#define TESSERACT_SLICE_GLSL

/**
 * @file tesseract_slice.glsl
 * @brief Slice frame, 4D depth cue, and fog of the tesseract scene, shared by
 *        shader/tesseract.frag (lattice march) and shader/tesseract_panes.frag
 *        (emanation panes), so both passes evaluate one field.
 */

uniform mat4 rotation4;   // SO(4) matrix of v -> qL v conj(qR), column-major.
uniform float sceneScale; // Slice-frame tilt gain: blend toward rotation4.
uniform float cellSize;   // Lattice cell period ("Corridor density").

// exp(-kappa |p4.w|): 4D depth cue.
const float W_DIM_KAPPA = 0.06;
// Slice hyperplane offset along w, in cells.
const float SLICE_W_CELLS = 0.25;
// Lattice offset in cells: places the default eye (world x = y = 0, depth
// drift along z) in the open middle of a cell, slightly off the corridor axis.
const vec3 LATTICE_OFFSET_CELLS = vec3(0.53, 0.47, 0.5);

// Fog: transmittance exp(-(t / fogDistance)^FOG_EXPONENT). The exponent above 1
// keeps the first cells clear and closes the corridor steeply beyond
// fogDistance, so the vanishing point reads as depth, not as uniform haze.
// fogDistance is FOG_CELLS cells at the default fogDensity (0.35) and scales
// inversely with the slider.
const float FOG_EXPONENT = 1.8;
const float FOG_CELLS = 3.5;
const float FOG_REFERENCE_DENSITY = 0.35;

// Slice frame, set once per fragment by buildSliceFrame().
vec4 gF0;
vec4 gF1;
vec4 gF2;

// Orthonormal 4x3 slice frame: the columns of rotation4 blended toward the
// identity (blend = 0.10 sceneScale, 0.13 at the default 1.3, capped at 0.6 so
// the blend never cancels), then Gram-Schmidt orthonormalized.
void buildSliceFrame() {
  float blend = clamp(0.10 * sceneScale, 0.0, 0.6);
  vec4 a0 = mix(vec4(1.0, 0.0, 0.0, 0.0), rotation4[0], blend);
  vec4 a1 = mix(vec4(0.0, 1.0, 0.0, 0.0), rotation4[1], blend);
  vec4 a2 = mix(vec4(0.0, 0.0, 1.0, 0.0), rotation4[2], blend);
  gF0 = normalize(a0);
  gF1 = normalize(a1 - (gF0 * dot(a1, gF0)));
  gF2 = normalize(a2 - (gF0 * dot(a2, gF0)) - (gF1 * dot(a2, gF1)));
}

vec4 slicePoint(vec3 p) {
  vec3 q = p + (LATTICE_OFFSET_CELLS * cellSize);
  return (gF0 * q.x) + (gF1 * q.y) + (gF2 * q.z) + vec4(0.0, 0.0, 0.0, SLICE_W_CELLS * cellSize);
}

// Distance at which fog transmittance is exp(-1), from the Fog slider value.
float fogDistanceFor(float fogDensity) {
  return FOG_CELLS * cellSize * FOG_REFERENCE_DENSITY / max(fogDensity, 1e-3);
}

// World-frame 4D depth cue.
float wDim(float w) {
  return exp(-W_DIM_KAPPA * abs(w));
}

float fogTransmittance(float t, float fogDistance) {
  return exp(-pow(t / fogDistance, FOG_EXPONENT));
}

#endif // TESSERACT_SLICE_GLSL
