#version 460 core
/**
 * @file tesseract.vert
 * @brief Speculative tesseract scene: instanced camera-facing ribbons for 4D
 *        line segments, rotated in R^4 and projected to R^3 per vertex.
 *
 * Render-only content (Thorne, The Science of Interstellar ch. 29-31); not
 * physics. Each instance is one segment (segA, segB) of R^4 ordered
 * (x, y, z, w) with segMeta = (tA, tB, kind, strand) as packed by
 * buildSceneSegments in src/render/tesseract/tesseract_geometry.cpp. Six
 * vertices per instance expand the segment into a screen-space quad of
 * lineWidthPx pixels, because core-profile lines rasterize one pixel wide.
 *
 * rotation4 is the SO(4) matrix of v -> qL v conj(qR) (so4.h), uploaded
 * column-major. projectionMode 0 is perspective along w,
 * p = xyz d / (d - w); 1 is stereographic from S^3, p = xyz / (1 - w) after
 * normalizing the rotated point. Kind 2 (lit-moment room outline) takes its
 * w and library time from litMoment, mapped by t -> 2 t / T - 1 as
 * libraryToTesseract does. A segment with an endpoint behind the camera is
 * culled, since its screen-space direction is undefined there.
 */

layout(location = 0) in vec4 segA;
layout(location = 1) in vec4 segB;
layout(location = 2) in vec4 segMeta;

uniform mat4 rotation4;
uniform mat4 viewProjection;
uniform vec2 resolution;
uniform int projectionMode;
uniform float perspectiveDistance;
uniform float sceneScale;
uniform float timeSpan;
uniform float litMoment;
uniform float lineWidthPx;

layout(location = 0) out float vLibraryTime;
layout(location = 1) out float vAcross;
layout(location = 2) out float vFade;
layout(location = 3) flat out int vKind;
layout(location = 4) flat out int vStrand;

const int KIND_EDGE = 0;
const int KIND_LIT_SLICE = 2;

// Corner (along, across) of the two triangles covering one ribbon.
const vec2 CORNERS[6] = vec2[6](vec2(0.0, -1.0), vec2(1.0, -1.0), vec2(1.0, 1.0),
                                vec2(0.0, -1.0), vec2(1.0, 1.0), vec2(0.0, 1.0));

// projectPerspective and projectStereographic mirror the functions of the
// same names in src/render/tesseract/tesseract_geometry.cpp, constant for
// constant (PERSPECTIVE_MIN_DEPTH, STEREOGRAPHIC_MIN_NORM, _MIN_DENOM,
// _FADE_END); tests/tesseract_geometry_test.cpp checks the CPU copies.
const float PERSPECTIVE_MIN_DEPTH = 0.05;
const float STEREOGRAPHIC_MIN_DENOM = 0.02;
const float STEREOGRAPHIC_FADE_END = 0.2;
const float STEREOGRAPHIC_MIN_NORM = 1e-4;

vec3 projectPerspective(vec4 p, float eyeDistance) {
  float denom = max(eyeDistance - p.w, PERSPECTIVE_MIN_DEPTH);
  return p.xyz * (eyeDistance / denom);
}

// The fade falls to zero where the image diverges near the pole w = 1.
vec3 projectStereographic(vec4 p, out float fade) {
  float len = length(p);
  vec4 s = len > STEREOGRAPHIC_MIN_NORM ? p / len : vec4(0.0, 0.0, 0.0, -1.0);
  float denom = 1.0 - s.w;
  fade = smoothstep(STEREOGRAPHIC_MIN_DENOM, STEREOGRAPHIC_FADE_END, denom);
  return s.xyz / max(denom, STEREOGRAPHIC_MIN_DENOM);
}

// Rotate p in R^4, then project to R^3 and scale to world units.
vec3 project4(vec4 p, out float fade) {
  vec4 r = rotation4 * p;
  fade = 1.0;
  if (projectionMode == 1) {
    return sceneScale * projectStereographic(r, fade);
  }
  return sceneScale * projectPerspective(r, perspectiveDistance);
}

void main() {
  vec2 corner = CORNERS[gl_VertexID % 6];
  int kind = int(round(segMeta.z));
  vec4 a = segA;
  vec4 b = segB;
  float tA = segMeta.x;
  float tB = segMeta.y;
  if (kind == KIND_LIT_SLICE) {
    float w = (2.0 * litMoment / timeSpan) - 1.0;
    a.w = w;
    b.w = w;
    tA = litMoment;
    tB = litMoment;
  }

  float fadeA;
  float fadeB;
  vec4 clipA = viewProjection * vec4(project4(a, fadeA), 1.0);
  vec4 clipB = viewProjection * vec4(project4(b, fadeB), 1.0);

  vLibraryTime = mix(tA, tB, corner.x);
  vAcross = corner.y;
  vFade = mix(fadeA, fadeB, corner.x);
  vKind = kind;
  vStrand = int(round(segMeta.w));

  if (clipA.w <= 1e-3 || clipB.w <= 1e-3) {
    gl_Position = vec4(0.0, 0.0, 2.0, 1.0);
    return;
  }

  vec2 halfRes = 0.5 * resolution;
  vec2 screenA = (clipA.xy / clipA.w) * halfRes;
  vec2 screenB = (clipB.xy / clipB.w) * halfRes;
  vec2 dir = screenB - screenA;
  float len = length(dir);
  dir = len > 1e-4 ? dir / len : vec2(1.0, 0.0);
  vec2 normal = vec2(-dir.y, dir.x);

  float widthScale = kind == KIND_EDGE ? 1.0 : (kind == KIND_LIT_SLICE ? 1.4 : 0.8);
  float halfWidth = 0.5 * lineWidthPx * widthScale;
  // Extend past each endpoint by the half width so consecutive pieces overlap.
  vec2 offsetPx = normal * (corner.y * halfWidth) + dir * ((2.0 * corner.x - 1.0) * halfWidth);

  vec4 clip = mix(clipA, clipB, corner.x);
  clip.xy += (offsetPx / halfRes) * clip.w;
  gl_Position = clip;
}
