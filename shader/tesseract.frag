#version 460 core
#extension GL_GOOGLE_include_directive : enable
/**
 * @file tesseract.frag
 * @brief Speculative tesseract scene: SDF raymarch of an endless rectilinear
 *        lattice of thin frame beams and dense glowing strands, sheared along
 *        its depth axis by an SO(4) rotation.
 *
 * Render-only content (Thorne, The Science of Interstellar ch. 29-31); not
 * physics. Runs over the fullscreen triangle of shader/simple.vert, one ray
 * per pixel from bhRayDir (shader/include/interop_raygen.glsl), the same
 * camera-ray convention the black-hole integrator uses.
 *
 * The lattice is plain domain repetition (mod-round) of a cell holding two
 * kinds of geometry: sdBoxFrame, thin dim bronze beams along the 12 edges
 * only (most of the cell's volume is open, dark void -- cells recede in x,
 * y, and z, not a single corridor), and a nested domain-repeated grid of
 * thin amber strand capsules along the depth axis (world z), each strand
 * lit and emissive enough to feed bloom on its own; the beams never are. A
 * cell's cross-section is sheared by shear4(), which rotates a pure-w point
 * (0, 0, 0, wSeed) with rotation4 and projects it back to R^3 with the same
 * perspective-along-w or stereographic map tesseract_geometry.cpp's
 * projectPerspective/projectStereographic apply on the CPU: as rotation4
 * animates, the shear slides neighboring cells against each other, the
 * "SO(4) spin visibly warps the lattice" effect. wSeed is a smooth sine of
 * depth, not a sawtooth: a fract()-based wrap is discontinuous at every
 * period and breaks the SDF's Lipschitz bound there, which read as a
 * seam of raymarch noise. A depth-periodic Gaussian (gaussian(), mirroring
 * litMomentEmission) lights one static band (nowDepth) and one traveling
 * band (pulseDepth, the gravity-message pulse) on every strand; beams never
 * carry either. Output is linear HDR radiance with alpha 1, summed into the
 * scene target so bloom and ACES tonemap treat it like the black-hole frame.
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

const float PI = 3.14159265359;

// tesseract_geometry.cpp mirrors these constants for projectPerspective/projectStereographic.
const float PERSPECTIVE_MIN_DEPTH = 0.05;
const float STEREOGRAPHIC_MIN_DENOM = 0.02;
const float STEREOGRAPHIC_FADE_END = 0.2;
const float STEREOGRAPHIC_MIN_NORM = 1e-4;
// Mirrors EMISSION_MIN_WIDTH in src/render/tesseract/tesseract_geometry.cpp.
const float EMISSION_MIN_WIDTH = 1e-4;

const int MATERIAL_BEAM = 0;
const int MATERIAL_STRAND = 1;

// Dim, non-emissive bronze: never crosses the bloom brightness-pass threshold
// (0.4 by default), so beams read as structure, not light.
const vec3 BEAM_COLOR = vec3(0.34, 0.19, 0.09);
// Warm amber, mirrors STRAND_COLOR in src/render/tesseract/tesseract_geometry.h.
const vec3 STRAND_COLOR = vec3(1.0, 0.55, 0.18);
const vec3 STRAND_HIGHLIGHT = vec3(1.0, 0.92, 0.65);
// The void is close to black; strands and beams fade into it with distance,
// not into a flat mid-tone patch.
const vec3 VOID_COLOR = vec3(0.0005, 0.0004, 0.001);

// Surface epsilon and step scale are fractions of cellSize so they track the
// strand radius (also a cellSize fraction) at any "Corridor density" slider
// value, rather than assuming one absolute scene scale.
const float SURFACE_EPS_FRACTION = 0.0006;
const float MIN_STEP_FRACTION = 0.0012;
// Conservative step scale: the strand field is a nested domain repetition
// (see strandFieldDistance) that only ever tests the strand nearest to the
// query point's own grid cell, which can under-count how close a jittered
// strand in a neighboring grid cell really is; the shear also locally
// stretches distances by more than 1:1 where the SO(4) rotation mixes a lot
// of w into the cross-section. Stepping by less than the raw SDF value
// absorbs both without per-sample derivative bounds.
const float STEP_SCALE = 0.55;
const float MAX_MARCH_DISTANCE = 70.0;
// Footprint multiple within which an exhausted march counts as a hit.
const float GRAZE_ACCEPT_FOOTPRINTS = 4.0;
const float STRAND_WIGGLE_FREQUENCY = 1.7;
// Fraction of the raw SO(4) shear offset applied to the lattice: the full
// offset (up to about 1.5 sceneScale) bends every strand into a slack-line
// sag; a fraction keeps the lattice rectilinear at rest and still slides
// neighboring cells visibly as rotation4 animates.
const float SHEAR_GAIN = 0.35;
// Beam outer half-extent as a fraction of the cell half-size, and beam
// thickness as a fraction of the full cell size (2-4% per the film's "thin
// lattice-like structure").
const float BEAM_HALF_FRACTION = 1.0;
const float BEAM_THICKNESS_FRACTION = 0.0025;
// Strand radius as a fraction of its own grid spacing (not of cellSize
// directly): whatever density the quality tier picks, a strand stays this
// thin relative to its neighbors, so the nearest strand never looks like a
// filled tube even when the eye happens to be close to it.
const float STRAND_RADIUS_FRACTION = 0.003;
// Strands per cell edge on the dense and sparse quality tiers (N x N grid);
// "on the order of 20-60 per cell face" (dense) and enough to stay
// recognizable but cheap (sparse).
const int STRAND_GRID_DENSE = 8;
const int STRAND_GRID_SPARSE = 4;

// The lattice's depth/strand axis is world x, carried into the z slot every
// other function treats as "depth" by this swap (its own inverse, so it
// carries a direction exactly as it carries a position, with no translation
// to strip out). The default camera looks toward the world origin along a
// path close to world z (buildCameraBasis's forward for an unmoved orbit),
// so aligning the strand axis with world z would point the camera straight
// down every fiber's length: a thin fiber viewed end-on covers far more
// screen area than the same fiber viewed broadside, reading as a fat glowing
// rod instead of a thin thread. World x sits close to perpendicular to that
// default forward instead, so fibers are seen mostly broadside and the beam
// grid, which repeats in all three axes regardless of which one is "depth",
// still recedes in x, y, and z at once.
vec3 latticeSpace(vec3 p) {
  return p.zyx;
}

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

vec2 hash21(vec2 p) {
  return fract(sin(vec2(dot(p, vec2(127.1, 311.7)), dot(p, vec2(269.5, 183.3)))) * 43758.5453123);
}

// The 3D offset a depth of @p depthWorld shears the cross-section by: a
// pure-w point rotated by the SO(4) orientation and projected back with the
// active projection mode, so the offset is zero at rotation4 = identity and
// grows as the rotation mixes w into x, y, z. Mirrors project4 in the
// retired shader/tesseract.vert, minus the per-instance xyz component
// (always zero here, since only the w seed varies). wSeed is sin(), not
// 2 fract() - 1: fract() wraps with a jump discontinuity at every period,
// which put a literal cliff in the SDF at every corridorPeriod boundary in
// depth; sin() is periodic and C-infinity everywhere, so the shear (and the
// SDF built on it) has no seam to raymarch noise against.
vec3 shear4(float depthWorld) {
  float wSeed = sin(2.0 * PI * depthWorld / max(corridorPeriod, 1e-3));
  vec4 rotated = rotation4 * vec4(0.0, 0.0, 0.0, wSeed);
  vec3 projected = projectionMode == 1 ? projectStereographic(rotated)
                                       : projectPerspective(rotated, perspectiveDistance);
  return SHEAR_GAIN * sceneScale * projected;
}

// Distance to a hollow box frame: the 12 edges only, thickness @p e, half
// extents @p b. Most of the box's volume (and most of the cell) stays open,
// dark void; only a ring of beams near each edge is solid.
float sdBoxFrame(vec3 p, vec3 b, float e) {
  p = abs(p) - b;
  vec3 q = abs(p + e) - e;
  return min(min(length(max(vec3(p.x, q.y, q.z), 0.0)) + min(max(p.x, max(q.y, q.z)), 0.0),
                 length(max(vec3(q.x, p.y, q.z), 0.0)) + min(max(q.x, max(p.y, q.z)), 0.0)),
             length(max(vec3(q.x, q.y, p.z), 0.0)) + min(max(q.x, max(q.y, p.z)), 0.0));
}

// Distance from @p localP (cell-local) to one strand fiber running along the
// depth axis at cross-section @p offset. The fiber is an unbounded line in
// depth, bent by a low-frequency sine pair of the ABSOLUTE depth @p depth
// (cell z plus local z) and a per-strand phase that depends on the strand's
// cross-section cell only, so the same fiber continues without a seam through
// every cell along the depth axis instead of ending in a cut capsule cap.
float strandDistance(vec3 localP, vec2 offset, float radius, float wiggleAmp, float phase,
                     float depth) {
  vec2 bend = wiggleAmp * vec2(sin((depth * STRAND_WIGGLE_FREQUENCY) + phase),
                               cos((depth * STRAND_WIGGLE_FREQUENCY * 1.3) + (phase * 1.7)));
  return length(localP.xy - offset - bend) - radius;
}

// Local (post-shear, cell-relative) position of world point @p p and the
// cell's own center, shared by every distance/material/brightness query so
// they all classify the same cell the same way.
vec3 lockedLocalPosition(vec3 worldP, out vec3 cellCenter) {
  vec3 p = latticeSpace(worldP);
  vec3 shear = shear4(p.z);
  vec3 sheared = vec3(p.x - shear.x, p.y - shear.y, p.z);
  cellCenter = cellSize * round(sheared / cellSize);
  return sheared - cellCenter;
}

// Cross-section grid spacing of the strand field: an N x N grid per cell,
// N set by the quality tier, so "how many strands" is an O(1) domain-
// repetition parameter rather than a per-sample loop count.
float strandGridSpacing(float halfCell) {
  int n = qualityTier == 0 ? STRAND_GRID_DENSE : STRAND_GRID_SPARSE;
  return (2.0 * halfCell) / float(n);
}

vec2 strandGridIndex(vec3 localP, float spacing) {
  return round(localP.xy / spacing);
}

// Per-(cell, grid-cell) hash: x drives phase and cross-section jitter, y
// drives the per-strand brightness variance in shadeHit.
vec2 strandHash(vec3 cellCenter, vec2 gridIndex) {
  return hash21((cellCenter.xy * 3.1) + (gridIndex * 17.0));
}

// Distance to the nearest grid cell's strand fiber. localP.xy is rounded to
// its grid cell before the strand's own cross-section jitter is applied, so
// a query near a grid boundary can under-count a neighbor's jittered strand;
// STEP_SCALE in raymarch() absorbs the resulting conservative-distance error.
float strandFieldDistance(vec3 localP, vec3 cellCenter, float halfCell) {
  float spacing = strandGridSpacing(halfCell);
  vec2 gridIndex = strandGridIndex(localP, spacing);
  vec2 h = strandHash(cellCenter, gridIndex);
  vec2 jitter = (h - vec2(0.5)) * spacing * 0.6;
  vec2 offset = clamp((gridIndex * spacing) + jitter, vec2(-halfCell * 0.92), vec2(halfCell * 0.92));
  float phase = h.x * 6.2831853;
  float wiggleAmp = qualityTier == 0 ? spacing * 0.12 : 0.0;
  float radius = cellSize * STRAND_RADIUS_FRACTION;
  return strandDistance(localP, offset, radius, wiggleAmp, phase, localP.z + cellCenter.z);
}

// Signed distance to the lattice at world position @p p: the nearer of the
// cell's beam frame and its strand field. Takes no out parameters so the
// raymarch loop and the normal's finite differences call one small, self-
// contained function per sample.
float mapDistance(vec3 p) {
  vec3 cellCenter;
  vec3 localP = lockedLocalPosition(p, cellCenter);
  float halfCell = 0.5 * cellSize;
  float beam = sdBoxFrame(localP, vec3(halfCell * BEAM_HALF_FRACTION), cellSize * BEAM_THICKNESS_FRACTION);
  float strands = strandFieldDistance(localP, cellCenter, halfCell);
  return min(beam, strands);
}

// Material of the surface at @p p: recomputes the same beam/strand split
// mapDistance already resolved, called once at the raymarch's final hit
// point rather than every step.
int materialAt(vec3 p) {
  vec3 cellCenter;
  vec3 localP = lockedLocalPosition(p, cellCenter);
  float halfCell = 0.5 * cellSize;
  float beam = sdBoxFrame(localP, vec3(halfCell * BEAM_HALF_FRACTION), cellSize * BEAM_THICKNESS_FRACTION);
  float strands = strandFieldDistance(localP, cellCenter, halfCell);
  return strands < beam ? MATERIAL_STRAND : MATERIAL_BEAM;
}

// Per-strand brightness variance ("brightness varying per strand"),
// recomputed at the hit point from the same grid hash strandFieldDistance
// used, so it stays consistent without threading an out parameter through
// the raymarch loop.
float strandBrightnessAt(vec3 p) {
  vec3 cellCenter;
  vec3 localP = lockedLocalPosition(p, cellCenter);
  float halfCell = 0.5 * cellSize;
  float spacing = strandGridSpacing(halfCell);
  vec2 gridIndex = strandGridIndex(localP, spacing);
  vec2 h = strandHash(cellCenter, gridIndex);
  // Three discrete tiers (dim, mid, bright), the film's layered strand
  // bundles: a continuous ramp would read as one uniform haze of fibers.
  return h.y < 0.6 ? 0.4 : (h.y < 0.9 ? 1.0 : 2.2);
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
  int maxSteps = qualityTier == 0 ? 256 : 160;
  float surfaceEps = cellSize * SURFACE_EPS_FRACTION;
  float minStep = cellSize * MIN_STEP_FRACTION;
  // Half a pixel's footprint per unit of travel: a strand thinner than a
  // pixel still registers a hit inside its footprint instead of being
  // skipped between samples, and a grazing ray stops as soon as it is within
  // a pixel of the fiber rather than crawling until the step budget ends.
  float pixelAngle = fovScale / max(resolution.y, 1.0);
  float travelled = 0.0;
  hit = false;
  float d = 0.0;
  float eps = surfaceEps;
  for (int step = 0; step < maxSteps; ++step) {
    vec3 p = rayOrigin + (rayDir * travelled);
    d = mapDistance(p);
    eps = max(surfaceEps, travelled * pixelAngle);
    if (abs(d) < eps) {
      hit = true;
      break;
    }
    // Step by |d| * STEP_SCALE, not d: the eye can start inside a beam
    // (drift and rotation move it through the lattice with no collision
    // guard), where d is negative and stepping by d alone would creep
    // forward in surfaceEps-sized slivers, taking hundreds of steps to
    // reach open space. Stepping by the unsigned, scaled-down distance still
    // bounds a safe move and reaches open space in a few steps.
    travelled += max(abs(d) * STEP_SCALE, minStep);
    if (travelled > MAX_MARCH_DISTANCE) {
      break;
    }
  }
  // A ray that spent its whole step budget within a few footprints of a
  // surface (a fiber seen at a grazing angle) is a hit, not a miss.
  if (!hit && travelled <= MAX_MARCH_DISTANCE && abs(d) < GRAZE_ACCEPT_FOOTPRINTS * eps) {
    hit = true;
  }
  return travelled;
}

vec3 shadeHit(vec3 p, vec3 rayDir, float footprint) {
  int material = materialAt(p);
  vec3 normal = estimateNormal(p);
  float lambert = clamp(dot(normal, -rayDir), 0.0, 1.0);
  // The depth/strand axis is the tilted z, not world z (see latticeSpace);
  // latticeSpace is a pure rotation, so it carries a direction the same way
  // it carries a position, with no translation term to strip out.
  float tiltedDepth = latticeSpace(p).z;
  float tiltedRayZ = latticeSpace(rayDir).z;
  vec3 radiance;
  if (material == MATERIAL_STRAND) {
    float depthPattern = mod(tiltedDepth, max(corridorPeriod, 1e-3));
    float lit = gaussian(depthPattern, mod(nowDepth, max(corridorPeriod, 1e-3)), nowWidth);
    float pulse = pulseEnabled != 0
                     ? gaussian(depthPattern, mod(pulseDepth, max(corridorPeriod, 1e-3)), pulseWidth)
                     : 0.0;
    // Anisotropic highlight along the depth axis (the fiber tangent), cheap
    // in place of a full microfacet BRDF: brightest when the view grazes the
    // fiber rather than looking straight down its length.
    float aniso = pow(clamp(1.0 - abs(tiltedRayZ), 0.0, 1.0), 3.0);
    float brightness = strandBrightnessAt(p);
    // Every strand is already a dim emissive fiber; the now/pulse boost
    // brightens the highlighted band further without letting an ordinary
    // strand flood the frame the way a much brighter baseline would once
    // the lattice fills most of the screen with thin fibers.
    radiance = (STRAND_COLOR * (0.32 + (0.16 * lambert)) * brightness) + (STRAND_HIGHLIGHT * aniso * 0.03 * brightness);
    radiance *= 1.0 + (1.0 * lit) + (1.8 * pulse);
  } else {
    // Beams carry no now/pulse boost: the gravity message travels the
    // strands, and a beam never crosses the bloom threshold.
    radiance = BEAM_COLOR * (0.03 + (0.22 * lambert));
  }
  // A fiber thinner than one pixel's footprint covers only part of the pixel;
  // dimming by the covered fraction trades the aliased speckle a hard
  // subpixel hit produces for a soft, continuous fade with distance.
  float radius = material == MATERIAL_STRAND ? cellSize * STRAND_RADIUS_FRACTION
                                             : 2.0 * cellSize * BEAM_THICKNESS_FRACTION;
  float coverage = clamp(radius / max(footprint, 1e-6), 0.0, 1.0);
  return radiance * strandGlow * coverage;
}

void main() {
  vec3 rayDir = bhRayDir(gl_FragCoord.xy, resolution, fovScale, cameraBasis);

  bool hit;
  float travelled = raymarch(eye, rayDir, hit);

  float footprint = travelled * fovScale / max(resolution.y, 1.0);
  vec3 shaded = hit ? shadeHit(eye + (rayDir * travelled), rayDir, footprint) : vec3(0.0);
  // Exponential extinction into a near-black void: depth reads by strands
  // and beams fading out, not by a flat mid-tone patch filling empty rays.
  float extinction = exp(-travelled * fogDensity * 0.22);
  vec3 color = (shaded * extinction) + (VOID_COLOR * (1.0 - extinction));

  fragColor = vec4(color, 1.0);
}
