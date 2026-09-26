#ifndef INTEROP_RAYGEN_GLSL
#define INTEROP_RAYGEN_GLSL

// Screen offset of a pixel from the image center in units of the vertical
// half-height: uv.y runs from -1 at the bottom edge to +1 at the top and uv.x
// spans +-aspect. With fovScale = tan(fov / 2) the image then subtends the
// vertical field of view fov, the glm::perspective projection of the same
// camera and the CUDA d_ray_dir.
vec2 bhPixelUv(vec2 pixelCoord, vec2 resolution) {
  vec2 uv = 2.0 * pixelCoord / resolution - vec2(1.0);
  uv.x *= resolution.x / max(resolution.y, 1.0);
  return uv;
}

// cameraBasis columns are (right, up, forward) from buildCameraBasis, so the
// pixel's screen offsets map to +right and +up without sign changes.
vec3 bhRayDirFromUv(vec2 uv, float fovScale, mat3 cameraBasis) {
  vec3 dir = normalize(vec3(uv.x * fovScale, uv.y * fovScale, 1.0));
  return cameraBasis * dir;
}

vec3 bhRayDir(vec2 pixelCoord, vec2 resolution, float fovScale, mat3 cameraBasis) {
  return bhRayDirFromUv(bhPixelUv(pixelCoord, resolution), fovScale, cameraBasis);
}

#endif // INTEROP_RAYGEN_GLSL
