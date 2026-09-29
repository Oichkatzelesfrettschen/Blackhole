#version 460 core
#extension GL_GOOGLE_include_directive : enable
/**
 * @file tesseract.frag
 * @brief Speculative tesseract scene: SDF raymarch of an endless rectilinear
 *        lattice, sheared along its depth axis by an SO(4) rotation.
 *
 * Render-only content (Thorne, The Science of Interstellar ch. 29-31); not
 * physics. Runs over the fullscreen triangle of shader/simple.vert, one ray
 * per pixel from bhRayDir (shader/include/interop_raygen.glsl), the same
 * camera-ray convention the black-hole integrator uses.
 *
 * The lattice is plain domain repetition (mod-round) of a box-within-box
 * corridor cell (sdCorridorShell: an outer box minus an inner box, walled on
 * the x and y faces, open along z) holding a few strand capsules along its
 * depth axis (world z): every cell is solid geometry, not a wireframe line.
 * A cell's cross-section offset
 * is sheared by shear4(), which rotates a pure-w point (0, 0, 0, wSeed) with
 * rotation4 and projects it back to R^3 with the same perspective-along-w or
 * stereographic map tesseract_geometry.cpp's projectPerspective/
 * projectStereographic apply on the CPU: as rotation4 animates, the shear
 * slides neighboring cells against each other along the cross-section, the
 * "SO(4) spin visibly warps the corridor" effect. A depth-periodic Gaussian
 * (gaussian(), mirroring litMomentEmission) lights one static band (nowDepth)
 * and one traveling band (pulseDepth, the gravity-message pulse) on every
 * strand. Output is linear HDR radiance with alpha 1, summed into the scene
 * target so bloom and ACES tonemap treat it like the black-hole frame.
 */

#include "include/interop_raygen.glsl"

layout(location = 0) out vec4 fragColor;

uniform vec2 resolution;
uniform vec3 eye;
uniform mat3 cameraBasis; // columns (right, up, forward), buildCameraBasis order.
uniform float fovScale;   // tan(fovDeg / 2)
uniform mat4 rotation4;   // SO(4) matrix of v -> qL v conj(qR), column-major.
uniform int projectionMode;
uniform float perspectiveDistance;
uniform float sceneScale;
uniform float corridorPeriod; // World units of depth before the shear/light pattern repeats.
uniform float cellSize;       // Lattice cell period ("Corridor density").
uniform float nowDepth;       // Depth (mod corridorPeriod) of the static "now" highlight band.
uniform float nowWidth;
uniform float pulseDepth; // Depth (mod corridorPeriod) of the traveling gravity-message pulse.
uniform float pulseWidth;
uniform int pulseEnabled;
uniform float strandGlow;
uniform float fogDensity;
uniform int qualityTier; // 0 dense (real GPUs), 1 sparse (Mesa llvmpipe and other slow rasterizers).

// tesseract_geometry.cpp mirrors these constants for projectPerspective/projectStereographic.
const float PERSPECTIVE_MIN_DEPTH = 0.05;
const float STEREOGRAPHIC_MIN_DENOM = 0.02;
const float STEREOGRAPHIC_FADE_END = 0.2;
const float STEREOGRAPHIC_MIN_NORM = 1e-4;
// Mirrors EMISSION_MIN_WIDTH in src/render/tesseract/tesseract_geometry.cpp.
const float EMISSION_MIN_WIDTH = 1e-4;

const int MATERIAL_FRAME = 0;
const int MATERIAL_STRAND = 1;

const vec3 FRAME_COLOR = vec3(0.55, 0.32, 0.16);
// Mirrors STRAND_COLOR in src/render/tesseract/tesseract_geometry.h.
const vec3 STRAND_COLOR = vec3(1.0, 0.68, 0.32);
const vec3 STRAND_HIGHLIGHT = vec3(1.0, 0.92, 0.65);
const vec3 VOID_COLOR = vec3(0.01, 0.008, 0.02);
const vec3 FOG_COLOR = vec3(0.09, 0.045, 0.03);

const float SURFACE_EPS = 0.0025;
const float MAX_MARCH_DISTANCE = 70.0;
const float STRAND_WIGGLE_FREQUENCY = 1.7;

vec3 projectPerspective(vec4 p, float eyeDistance) {
  float denom = max(eyeDistance - p.w, PERSPECTIVE_MIN_DEPTH);
  return p.xyz * (eyeDistance / denom);
}

vec3 projectStereographic(vec4 p) {
  float len = length(p);
  vec4 s = len > STEREOGRAPHIC_MIN_NORM ? p / len : vec4(0.0, 0.0, 0.0, -1.0);
  float denom = max(1.0 - s.w, STEREOGRAPHIC_MIN_DENOM);
  return s.xyz / denom;
}

// Mirrors litMomentEmission in src/render/tesseract/tesseract_geometry.cpp.
float gaussian(float x, float center, float width) {
  float u = (x - center) / max(width, EMISSION_MIN_WIDTH);
  return exp(-0.5 * u * u);
}

float hash11(float n) {
  return fract(sin(n) * 43758.5453123);
}

vec2 hash21(vec2 p) {
  return fract(sin(vec2(dot(p, vec2(127.1, 311.7)), dot(p, vec2(269.5, 183.3)))) * 43758.5453123);
}

// The 3D offset a depth of @p depthWorld shears the cross-section by: a pure-w
// point rotated by the SO(4) orientation and projected back with the active
// projection mode, so the offset is zero at rotation4 = identity and grows as
// the rotation mixes w into x, y, z. Mirrors project4 in the retired
// shader/tesseract.vert, minus the per-instance xyz component (always zero
// here, since only the w seed varies).
vec3 shear4(float depthWorld) {
  float wSeed = (2.0 * fract(depthWorld / max(corridorPeriod, 1e-3))) - 1.0;
  vec4 rotated = rotation4 * vec4(0.0, 0.0, 0.0, wSeed);
  vec3 projected = projectionMode == 1 ? projectStereographic(rotated)
                                       : projectPerspective(rotated, perspectiveDistance);
  return sceneScale * projected;
}

float sdBox(vec3 p, vec3 b) {
  vec3 q = abs(p) - b;
  return length(max(q, 0.0)) + min(max(q.x, max(q.y, q.z)), 0.0);
}

// A box-within-box corridor cross-section: sdBox(outer) minus sdBox(inner)
// leaves solid walls on the x and y faces (floor, ceiling, both sides); the
// inner box's z half-extent is left huge so no wall closes off the z faces,
// and the corridor threads straight through every cell. Domain repetition
// (mapDistance) then stacks this into a grid of parallel square tunnels.
float sdCorridorShell(vec3 p, float halfCell, float wallThickness) {
  float outer = sdBox(p, vec3(halfCell));
  float inner = sdBox(p, vec3(halfCell - wallThickness, halfCell - wallThickness, 1000.0));
  return max(outer, -inner);
}

float sdCapsule(vec3 p, vec3 a, vec3 b, float r) {
  vec3 pa = p - a;
  vec3 ba = b - a;
  float h = clamp(dot(pa, ba) / dot(ba, ba), 0.0, 1.0);
  return length(pa - (ba * h)) - r;
}

// Distance from @p localP (cell-local, z along the corridor) to one strand
// fiber at cross-section @p offset, its capsule spanning the whole cell depth.
// The query point's cross-section is offset by a low-frequency sine pair
// before the capsule distance, which bends the fiber without a multi-segment
// SDF: the strand reads as gently woven rather than a straight rod.
float strandDistance(vec3 localP, vec2 offset, float radius, float wiggleAmp, float phase,
                     float halfCell) {
  vec3 q = localP;
  q.xy -= wiggleAmp * vec2(sin((localP.z * STRAND_WIGGLE_FREQUENCY) + phase),
                          cos((localP.z * STRAND_WIGGLE_FREQUENCY * 1.3) + (phase * 1.7)));
  return sdCapsule(q, vec3(offset, -halfCell), vec3(offset, halfCell), radius);
}

// Local (post-shear, cell-relative) position of world point @p p and the
// cell's own center, shared by mapDistance and materialAt so both classify
// the same cell the same way.
vec3 lockedLocalPosition(vec3 p, out vec3 cellCenter) {
  vec3 shear = shear4(p.z);
  vec3 sheared = vec3(p.x - shear.x, p.y - shear.y, p.z);
  cellCenter = cellSize * round(sheared / cellSize);
  return sheared - cellCenter;
}

float strandFieldDistance(vec3 localP, vec3 cellCenter, float halfCell) {
  int strandCount = qualityTier == 0 ? 3 : 1;
  float wiggleAmp = qualityTier == 0 ? cellSize * 0.05 : 0.0;
  float strandRadius = cellSize * 0.018;
  float innerHalf = halfCell * 0.5;
  vec2 cellSeed = cellCenter.xy * 0.7 + cellCenter.zz * 1.9;
  float strands = 1e5;
  for (int i = 0; i < strandCount; ++i) {
    vec2 h = hash21(cellSeed + (float(i) * 11.37));
    vec2 offset = mix(vec2(-innerHalf), vec2(innerHalf), h);
    float phase = h.x * 6.2831853;
    strands = min(strands, strandDistance(localP, offset, strandRadius, wiggleAmp, phase, halfCell));
  }
  return strands;
}

// Signed distance to the lattice at world position @p p: the nearer of the
// cell's corridor shell and its strand fibers. Takes no out parameters so the
// raymarch loop and the normal's finite differences call one small, self-
// contained function per sample.
float mapDistance(vec3 p) {
  vec3 cellCenter;
  vec3 localP = lockedLocalPosition(p, cellCenter);
  float halfCell = 0.5 * cellSize;
  float frame = sdCorridorShell(localP, halfCell * 0.98, cellSize * 0.06);
  float strands = strandFieldDistance(localP, cellCenter, halfCell);
  return min(frame, strands);
}

// Material of the surface at @p p: recomputes the same frame/strand split
// mapDistance already resolved, called once at the raymarch's final hit
// point rather than every step.
int materialAt(vec3 p) {
  vec3 cellCenter;
  vec3 localP = lockedLocalPosition(p, cellCenter);
  float halfCell = 0.5 * cellSize;
  float frame = sdCorridorShell(localP, halfCell * 0.98, cellSize * 0.06);
  float strands = strandFieldDistance(localP, cellCenter, halfCell);
  return strands < frame ? MATERIAL_STRAND : MATERIAL_FRAME;
}

vec3 estimateNormal(vec3 p) {
  const vec2 e = vec2(1.0, -1.0) * 0.001;
  return normalize((e.xyy * mapDistance(p + e.xyy)) + (e.yyx * mapDistance(p + e.yyx)) +
                   (e.yxy * mapDistance(p + e.yxy)) + (e.xxx * mapDistance(p + e.xxx)));
}

// Sphere-traces from @p rayOrigin along @p rayDir. Returns the travelled
// distance; @p hit reports whether a surface was found within
// MAX_MARCH_DISTANCE.
float raymarch(vec3 rayOrigin, vec3 rayDir, out bool hit) {
  int maxSteps = qualityTier == 0 ? 128 : 56;
  float travelled = 0.0;
  hit = false;
  for (int step = 0; step < maxSteps; ++step) {
    vec3 p = rayOrigin + (rayDir * travelled);
    float d = mapDistance(p);
    if (abs(d) < SURFACE_EPS) {
      hit = true;
      break;
    }
    // Step by |d|, not d: the eye can start inside a frame beam (drift and
    // rotation move it through the lattice with no collision guard), where d
    // is negative and stepping by d alone would creep forward in
    // SURFACE_EPS-sized slivers, taking hundreds of steps to reach open
    // space. Stepping by the unsigned distance still bounds a safe move (the
    // nearest surface, inside or out, is exactly |d| away) and reaches open
    // space in a few steps.
    travelled += max(abs(d), SURFACE_EPS * 0.5);
    if (travelled > MAX_MARCH_DISTANCE) {
      break;
    }
  }
  return travelled;
}

vec3 shadeHit(vec3 p, vec3 rayDir) {
  int material = materialAt(p);
  vec3 normal = estimateNormal(p);
  float lambert = clamp(dot(normal, -rayDir), 0.0, 1.0);
  float depthPattern = mod(p.z, max(corridorPeriod, 1e-3));
  float lit = gaussian(depthPattern, mod(nowDepth, max(corridorPeriod, 1e-3)), nowWidth);
  float pulse = pulseEnabled != 0
                   ? gaussian(depthPattern, mod(pulseDepth, max(corridorPeriod, 1e-3)), pulseWidth)
                   : 0.0;
  vec3 radiance;
  if (material == MATERIAL_STRAND) {
    // Anisotropic highlight along the corridor axis (the fiber tangent),
    // cheap in place of a full microfacet BRDF: brightest when the view
    // grazes the fiber rather than looking straight down its length.
    float aniso = pow(clamp(1.0 - abs(rayDir.z), 0.0, 1.0), 3.0);
    // Baseline is a lit fiber, not a light source; the now/pulse boost below
    // is what pushes a strand well past the bloom brightness-pass threshold
    // (0.4 by default), so the highlighted band reads as glowing.
    radiance = (STRAND_COLOR * (0.16 + (0.3 * lambert))) + (STRAND_HIGHLIGHT * aniso * 0.06);
    radiance *= 1.0 + (2.2 * lit) + (3.5 * pulse);
  } else {
    radiance = FRAME_COLOR * (0.015 + (0.05 * lambert));
    radiance *= 1.0 + (1.2 * lit) + (2.0 * pulse);
  }
  return radiance * strandGlow;
}

void main() {
  vec3 rayDir = bhRayDir(gl_FragCoord.xy, resolution, fovScale, cameraBasis);

  bool hit;
  float travelled = raymarch(eye, rayDir, hit);

  vec3 shaded = hit ? shadeHit(eye + (rayDir * travelled), rayDir) : vec3(0.0);
  // Aerial-perspective fog: the void grows warmer and brighter with distance,
  // hiding the lattice's far tiling seam without extra geometry.
  float fog = 1.0 - exp(-travelled * fogDensity * 0.05);
  vec3 background = mix(VOID_COLOR, FOG_COLOR, clamp(travelled / MAX_MARCH_DISTANCE, 0.0, 1.0));
  vec3 color = mix(shaded, background, clamp(fog, 0.0, 1.0));

  fragColor = vec4(color, 1.0);
}
