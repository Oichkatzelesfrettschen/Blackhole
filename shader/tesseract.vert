#version 460 core
/**
 * @file tesseract.vert
 * @brief Speculative tesseract scene: instanced camera-facing ribbons for 4D
 *        line segments, rotated in R^4 and projected to R^3 per vertex.
 *
 * Render-only content (Thorne, The Science of Interstellar ch. 29-31); not
 * physics. Each instance is one segment (segA, segB) of R^4 ordered
 * (x, y, z, w) with segMeta = (tA, tB, tag, strand) and the neighboring
 * polyline points segPrev and segNext, as packed by buildSceneSegments in
 * src/render/tesseract/tesseract_geometry.cpp. Six vertices per instance
 * expand the segment into a screen-space quad of lineWidthPx pixels, because
 * core-profile lines rasterize one pixel wide. Blending is additive, so the
 * quads of one polyline must tile it: a true endpoint extends by the half
 * width as a cap, and an interior joint puts both neighbors' corners on one
 * miter, (n0 + n1) * 2 halfWidth / |n0 + n1|^2 from the joint for the two
 * segment normals, computed from the same projected points in the same order
 * by both segments, so the shared edge is bit-identical and the rasterizer
 * covers each pixel once. A neighbor point behind the near plane is first
 * clipped the way its own segment clips it (nearClipStart, nearClipEnd). Turns sharper than the miter limit fall back to the
 * segment's own normal.
 *
 * rotation4 is the SO(4) matrix of v -> qL v conj(qR) (so4.h), uploaded
 * column-major. segMeta.z packs the SegmentKind in its low two bits with
 * SEGMENT_CAP_A (4) and SEGMENT_CAP_B (8), as packSegmentTag writes it.
 * projectionMode 0 is perspective along w,
 * p = xyz d / (d - w); 1 is stereographic from S^3, p = xyz / (1 - w) after
 * normalizing the rotated point. Kind 2 (lit-moment room outline) takes its
 * w and library time from litMoment, mapped by t -> 2 t / T - 1 as
 * libraryToTesseract does. A segment that crosses the near plane z = -w is
 * clipped to its visible part in clip space before the screen-space
 * expansion, which needs finite screen positions at both ends; a segment
 * wholly behind the plane is culled.
 */

layout(location = 0) in vec4 segA;
layout(location = 1) in vec4 segB;
layout(location = 2) in vec4 segMeta;
layout(location = 3) in vec4 segPrev;
layout(location = 4) in vec4 segNext;

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
const int SEGMENT_KIND_MASK = 3;
const int SEGMENT_CAP_A = 4;
const int SEGMENT_CAP_B = 8;

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
// Segment-parameter step a clipped endpoint takes past the near plane toward
// the visible end, so the rasterizer's own near clip never shaves the quad.
const float NEAR_CLIP_NUDGE = 1e-4;
// Smallest cosine of the half turn a miter serves (turns up to about 151
// degrees); sharper joints keep the segment's own normal.
const float MITER_MIN_HALF_COS = 0.25;

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

// Segment parameter where a segment whose start lies behind the near plane
// (signed distances nearStart < 0 <= nearEnd) enters it, nudged forward.
float nearClipStart(float nearStart, float nearEnd) {
  return min(nearStart / (nearStart - nearEnd) + NEAR_CLIP_NUDGE, 1.0);
}

// Segment parameter where a segment whose end lies behind the near plane
// (nearStart >= 0 > nearEnd) leaves it, nudged back.
float nearClipEnd(float nearStart, float nearEnd) {
  return max(nearStart / (nearStart - nearEnd) - NEAR_CLIP_NUDGE, 0.0);
}

// Left-hand unit normal of the screen segment from p to q.
vec2 segmentNormal(vec2 p, vec2 q) {
  precise vec2 d = q - p;
  precise float len = length(d);
  d = len > 1e-4 ? d / len : vec2(1.0, 0.0);
  return vec2(-d.y, d.x);
}

void main() {
  vec2 corner = CORNERS[gl_VertexID % 6];
  int tag = int(round(segMeta.z));
  int kind = tag & SEGMENT_KIND_MASK;
  vec4 a = segA;
  vec4 b = segB;
  vec4 prev = segPrev;
  vec4 next = segNext;
  float tA = segMeta.x;
  float tB = segMeta.y;
  if (kind == KIND_LIT_SLICE) {
    float w = (2.0 * litMoment / timeSpan) - 1.0;
    a.w = w;
    b.w = w;
    prev.w = w;
    next.w = w;
    tA = litMoment;
    tB = litMoment;
  }

  float fadeA;
  float fadeB;
  // precise keeps the compiler from contracting these differently per use,
  // so a joint point projects to the same bits in both segments.
  precise vec4 clipA = viewProjection * vec4(project4(a, fadeA), 1.0);
  precise vec4 clipB = viewProjection * vec4(project4(b, fadeB), 1.0);

  // Signed distance to the near plane z = -w, linear along the segment.
  precise float nearA = clipA.z + clipA.w;
  precise float nearB = clipB.z + clipB.w;
  vKind = kind;
  vStrand = int(round(segMeta.w));
  vAcross = corner.y;
  if (nearA <= 0.0 && nearB <= 0.0) {
    gl_Position = vec4(0.0, 0.0, 2.0, 1.0);
    vLibraryTime = tA;
    vFade = 0.0;
    return;
  }
  // Keep the part of [0, 1] in front of the plane; a clipped end is no
  // polyline endpoint and draws no cap.
  float sA = 0.0;
  float sB = 1.0;
  if (nearA < 0.0) {
    sA = nearClipStart(nearA, nearB);
    tag &= ~SEGMENT_CAP_A;
  } else if (nearB < 0.0) {
    sB = nearClipEnd(nearA, nearB);
    tag &= ~SEGMENT_CAP_B;
  }
  // Only a clipped end moves, so an unclipped joint keeps the exact clip
  // position its neighbor computes for the same point.
  bool clippedA = sA > 0.0;
  bool clippedB = sB < 1.0;
  vec4 keptA = clippedA ? mix(clipA, clipB, sA) : clipA;
  vec4 keptB = clippedB ? mix(clipA, clipB, sB) : clipB;
  bool atA = corner.x < 0.5;
  float s = atA ? sA : sB;
  vLibraryTime = mix(tA, tB, s);
  vFade = mix(fadeA, fadeB, s);
  clipA = keptA;
  clipB = keptB;
  if (clipA.w <= 1e-6 || clipB.w <= 1e-6) {
    gl_Position = vec4(0.0, 0.0, 2.0, 1.0);
    return;
  }

  vec2 halfRes = 0.5 * resolution;
  precise vec2 screenA = (clipA.xy / clipA.w) * halfRes;
  precise vec2 screenB = (clipB.xy / clipB.w) * halfRes;
  precise vec2 normal = segmentNormal(screenA, screenB);

  float widthScale = kind == KIND_EDGE ? 1.0 : (kind == KIND_LIT_SLICE ? 1.4 : 0.8);
  float halfWidth = 0.5 * lineWidthPx * widthScale;
  bool capped = atA ? (tag & SEGMENT_CAP_A) != 0 : (tag & SEGMENT_CAP_B) != 0;
  precise vec2 offsetPx = normal * (corner.y * halfWidth);
  if (capped) {
    vec2 dir = vec2(normal.y, -normal.x);
    offsetPx += dir * ((atA ? -1.0 : 1.0) * halfWidth);
  } else if (atA ? !clippedA : !clippedB) {
    // Interior joint: the neighbor's segment runs prev -> a or b -> next.
    // A neighbor point behind the near plane is clipped exactly as the
    // neighbor clips its own segment (same operands, same order), so both
    // segments miter against the same visible direction.
    float fadeN;
    precise vec4 clipN = viewProjection * vec4(project4(atA ? prev : next, fadeN), 1.0);
    precise float nearN = clipN.z + clipN.w;
    if (nearN < 0.0) {
      clipN = atA ? mix(clipN, clipA, nearClipStart(nearN, nearA))
                  : mix(clipB, clipN, nearClipEnd(nearB, nearN));
    }
    if (clipN.w > 1e-6) {
      precise vec2 screenN = (clipN.xy / clipN.w) * halfRes;
      // A repeated point (no neighbor) has no direction to miter against.
      bool hasNeighbor = distance(screenN, atA ? screenA : screenB) > 1e-4;
      precise vec2 other = atA ? segmentNormal(screenN, screenA) : segmentNormal(screenB, screenN);
      // Both segments add the earlier segment's normal first.
      precise vec2 m = atA ? other + normal : normal + other;
      precise float m2 = dot(m, m);
      if (hasNeighbor && m2 > 4.0 * MITER_MIN_HALF_COS * MITER_MIN_HALF_COS) {
        offsetPx = m * (corner.y * 2.0 * halfWidth / m2);
      }
    }
  }

  precise vec4 clip = atA ? clipA : clipB;
  clip.xy += (offsetPx / halfRes) * clip.w;
  gl_Position = clip;
}
