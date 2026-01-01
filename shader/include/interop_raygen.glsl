#ifndef INTEROP_RAYGEN_GLSL
#define INTEROP_RAYGEN_GLSL

vec2 bhPixelUv(vec2 pixelCoord, vec2 resolution) {
  vec2 uv = pixelCoord / resolution - vec2(0.5);
  uv.x *= resolution.x / max(resolution.y, 1.0);
  return uv;
}

vec3 bhRayDirFromUv(vec2 uv, float fovScale, mat3 cameraBasis) {
  vec3 dir = normalize(vec3(-uv.x * fovScale, uv.y * fovScale, 1.0));
  return cameraBasis * dir;
}

vec3 bhRayDir(vec2 pixelCoord, vec2 resolution, float fovScale, mat3 cameraBasis) {
  return bhRayDirFromUv(bhPixelUv(pixelCoord, resolution), fovScale, cameraBasis);
}

#endif // INTEROP_RAYGEN_GLSL
