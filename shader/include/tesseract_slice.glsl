#ifndef TESSERACT_SLICE_GLSL
#define TESSERACT_SLICE_GLSL

/**
 * @file tesseract_slice.glsl
 * @brief Slice frame, 4D depth cue, and fog of the tesseract scene, shared by
 *        shader/tesseract.frag (lattice march) and shader/tesseract_panes.frag
 *        (emanation panes), so both passes evaluate one field.
 *
 * The CPU builds the frame and the eye's 4D point in double
 * (tesseract_renderer.h tesseractSliceFrame): sliceAxes are the three
 * orthonormal columns F of the slice, and eyeSlice is the eye's point with its
 * x, y, z wrapped onto one lattice period. The shaders march in eye-relative
 * coordinates r, so p4 = eyeSlice + F r stays within a few cells of the
 * origin however long the eye has drifted.
 */

uniform vec4 sliceAxes[3];        // Columns of the orthonormal 4x3 slice frame F.
uniform vec4 eyeSlice;            // 4D point of the eye, x, y, z wrapped onto the lattice period.
uniform float cellSize;           // Lattice cell period ("Corridor density").
uniform float latticePeriodCells; // Cells after which the strand and pane hashes repeat.

// exp(-kappa |p4.w|): 4D depth cue.
const float W_DIM_KAPPA = 0.06;

// Fog: transmittance exp(-(t / fogDistance)^FOG_EXPONENT). The exponent above 1
// keeps the first cells clear and closes the corridor steeply beyond
// fogDistance, so the vanishing point reads as depth, not as uniform haze.
// fogDistance is FOG_CELLS cells at the default fogDensity (0.35) and scales
// inversely with the slider.
const float FOG_EXPONENT = 1.8;
const float FOG_CELLS = 3.5;
const float FOG_REFERENCE_DENSITY = 0.35;

// 4D displacement of the eye-relative world offset @p r.
vec4 sliceOffset(vec3 r) {
  return (sliceAxes[0] * r.x) + (sliceAxes[1] * r.y) + (sliceAxes[2] * r.z);
}

// 4D point of the eye-relative world offset @p r.
vec4 slicePoint(vec3 r) {
  return eyeSlice + sliceOffset(r);
}

// Lattice cell index @p n reduced onto [-P/2, P/2) of the hash period P, so
// every hash keyed by it repeats with the wrapped eyeSlice and the cells
// around the origin keep their own indices.
vec2 latticeCellId(vec2 n) {
  return n - (latticePeriodCells * floor((n + (0.5 * latticePeriodCells)) / latticePeriodCells));
}

// Distance at which fog transmittance is exp(-1), from the Fog slider value.
float fogDistanceFor(float fogDensity) {
  return FOG_CELLS * cellSize * FOG_REFERENCE_DENSITY / max(fogDensity, 1e-3);
}

// World-frame 4D depth cue, the distance of the sampled point from the w = 0
// hyperplane. The drift runs inside that hyperplane, so eyeSlice.w stays
// within the camera offset of it.
float wDim(float w) {
  return exp(-W_DIM_KAPPA * abs(w));
}

float fogTransmittance(float t, float fogDistance) {
  return exp(-pow(t / fogDistance, FOG_EXPONENT));
}

#endif // TESSERACT_SLICE_GLSL
