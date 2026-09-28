#ifndef GRMHD_DENSE_EMISSION_GLSL
#define GRMHD_DENSE_EMISSION_GLSL

// The packed volume stores normalized mass density and internal energy in R and G.
float grmhdDensityWeight(vec4 grmhdSample) {
  return max(grmhdSample.r, 0.0) * max(grmhdSample.g, 0.0);
}

#endif
