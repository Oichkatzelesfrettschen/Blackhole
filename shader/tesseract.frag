#version 460 core
#extension GL_GOOGLE_include_directive : enable
/**
 * @file tesseract.frag
 * @brief Speculative tesseract scene: sphere-traced 3D hyperplane slice of a
 *        periodic 4D field of thickened 2-planes, dressed with helical strands.
 *
 * Render-only content (Thorne, The Science of Interstellar ch. 29-31); not
 * physics. Design: docs/plans/tesseract-interstellar-visuals.md, after
 * R1-R4 of the hyperdimensional projection research note. Runs over the
 * fullscreen triangle of shader/simple.vert, one ray per pixel from bhRayDir
 * (shader/include/interop_raygen.glsl).
 *
 * Field. A 4D point is p4 = eyeSlice + F r for the eye-relative offset r, where
 * F is an orthonormal 4x3 slice frame built from the SO(4) orientation blended
 * toward the identity (shader/include/tesseract_slice.glsl), so the slice tilts
 * slowly about the eye against the lattice as the left-isoclinic rotation
 * animates. In the lattice
 * cell of period cellSize, three families of thickened 2-planes (a beam axis
 * plus w, omitting the two transverse axes) slice to tubes along x, y, and z:
 * a cubic lattice of thin beams receding down corridors in every direction.
 * Distances are exact 4D distances, a lower bound of the slice distance, so
 * sphere tracing never overshoots.
 *
 * Strands. Around every beam wind two helical shells of thin strands (three
 * inner, two outer, opposite twist). A strand's phase advances with arc length
 * and with p4.w, so the weave shifts as the slice moves through w. The
 * angular-sector fold is seam-free (the sector index shifts by the sector
 * count across the atan branch cut, a full turn). Each strand hashes to one of
 * three tiers of brightness and radius.
 *
 * Shading. Strands are emissive fibers: a bright core that falls off across the
 * fiber width, plus a soft halo accumulated along the march from the distance
 * to the nearest strand (analytic bloom, no extra pass), so a fiber thinner
 * than a pixel still contributes light instead of aliasing. Beams are dark
 * bronze with a rim and a narrow specular streak, kept under the 0.4 bloom
 * threshold. Radiance falls with exponential extinction along the ray and
 * with exp(-kappa |p4.w|), the distance of the sampled point from the w = 0
 * hyperplane in the world frame. Output is linear HDR radiance with alpha 1.
 */

#include "include/interop_raygen.glsl"
#include "include/tesseract_slice.glsl"

layout(location = 0) out vec4 fragColor;

uniform vec2 resolution;
uniform mat3 cameraBasis; // columns (right, up, forward), buildCameraBasis order.
uniform float fovScale;   // tan(fovDeg / 2)
uniform int projectionMode;
uniform float perspectiveDistance;
uniform float corridorPeriod; // World units of depth before the light bands repeat.
uniform float eyeDepth;       // World depth of the eye plus the lattice offset, mod corridorPeriod.
uniform float nowDepth;       // Depth (mod corridorPeriod) of the static "now" highlight band.
uniform float nowWidth;
uniform float pulseDepth; // Depth (mod corridorPeriod) of the traveling gravity-message pulse.
uniform float pulseWidth;
uniform int pulseEnabled;
uniform float strandGlow;
uniform float fogDensity;
uniform int qualityTier; // 0 dense (real GPUs), 1 sparse (Mesa llvmpipe and other slow rasterizers).
uniform int wallsEnabled; // Ammann-Beenker walls (tesseract_algebra.glsl).
uniform int kitesEnabled; // Box-kite glyphs at the lattice vertices.

#include "include/tesseract_algebra.glsl"

const float PI = 3.14159265359;
const float TAU = 6.28318530718;

// Mirrors EMISSION_MIN_WIDTH in src/render/tesseract/tesseract_geometry.cpp.
const float EMISSION_MIN_WIDTH = 1e-4;

const int MATERIAL_BEAM = 0;
const int MATERIAL_STRAND = 1;

// Dark bronze; the rim and specular terms below carry the metallic read.
const vec3 BEAM_COLOR = vec3(0.30, 0.16, 0.07);
const vec3 BEAM_RIM_COLOR = vec3(1.0, 0.62, 0.28);
// Strand core (hot amber-white) and halo (deeper amber).
const vec3 STRAND_CORE_COLOR = vec3(1.0, 0.66, 0.26);
const vec3 STRAND_HALO_COLOR = vec3(1.0, 0.50, 0.15);
const vec3 VOID_COLOR = vec3(0.0004, 0.0003, 0.0008);

// Beam ceiling: BEAM_COLOR * 0.08 + rim 0.16 + specular 0.10 stays under the
// 0.4 bloom brightness-pass threshold; only strands bloom.
const float BEAM_RIM_GAIN = 0.16;
const float BEAM_SPEC_GAIN = 0.10;

// Geometry as fractions of cellSize.
const float BEAM_RADIUS_FRACTION = 0.012;
const float SHELL_RADIUS_FRACTION[2] = float[2](0.05, 0.11);
const float SHELL_PITCH_FRACTION[2] = float[2](0.50, 0.85);
const int SHELL_STRANDS[2] = int[2](3, 1);
const float SHELL_DIRECTION[2] = float[2](1.0, -1.0);
// Strand radius per tier (dim, mid, bright) and emissive scale per tier.
const float TIER_RADIUS_FRACTION[3] = float[3](0.0045, 0.0060, 0.0085);
const float TIER_BRIGHTNESS[3] = float[3](0.08, 0.22, 1.30);
// Beyond this transverse distance from a beam axis the strand shells are
// replaced by their conservative lower bound.
const float STRAND_CULL_FRACTION = 0.26;
// Box-kite glyph: octahedron at a lattice vertex, radius from GLYPH_RADIUS_MIN
// to GLYPH_RADIUS_MAX cells by the count of local box-kites, over w within
// GLYPH_W_HALF cells of the vertex's w layer.
const float GLYPH_RADIUS_MIN = 0.024;
const float GLYPH_RADIUS_MAX = 0.045;
// The slice sits TESSERACT_SLICE_W_CELLS (0.25) off the w = 0 layer, so the
// w extent must exceed it for the glyphs of that layer to show.
const float GLYPH_W_HALF = 0.4;
const float GLYPH_SAIL_GAIN = 0.9;
const float GLYPH_FACE_GAIN = 0.14;
const vec3 STRAND_COOL_TINT = vec3(0.62, 0.78, 1.0);
// The w-phase rate of the helices (radians per cellSize of p4.w).
const float STRAND_W_TWIST = 0.6;

// Halo: analytic bloom from the nearest-strand distance along the march.
const float HALO_RADIUS_FRACTION = 0.05;
const float HALO_GAIN = 0.03;
const float SURFACE_EPS_FRACTION = 0.0004;
const float MIN_STEP_FRACTION = 0.0008;
// The fold to the nearest angular sector under-estimates strand proximity
// slightly, and the slice frame is only near-isometric: step conservatively.
const float STEP_SCALE = 0.6;
const float MAX_MARCH_CELLS = 24.0;
const float GRAZE_ACCEPT_FOOTPRINTS = 4.0;
// Tier index and 4D-cue-free brightness of the nearest strand of the last
// field evaluation.
float gTierBrightness = 1.0;
float gTierRadius = 0.006;
// Edge sign (+1 or -1) of the nearest strand's DMZ link, and the basis index
// of the nearest box-kite glyph's vertex.
float gStrandSign = 1.0;
int gKiteIndex = 0;

// Mirrors litMomentEmission in src/render/tesseract/tesseract_geometry.cpp.
float gaussian(float x, float center, float width) {
  float u = (x - center) / max(width, EMISSION_MIN_WIDTH);
  return exp(-0.5 * u * u);
}

uint pcgHash(uint v) {
  uint state = (v * 747796405u) + 2891336453u;
  uint word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
  return (word >> 22u) ^ word;
}

// Integer PCG hash of a lattice-derived coordinate pair, quantized to 1/16.
// sin()-based hashes differ between GPU drivers at large arguments, which
// would give each driver a different strand layout.
vec2 hash21(vec2 p) {
  ivec2 i = ivec2(round(p * 16.0));
  uint h = pcgHash(uint(i.x) + pcgHash(uint(i.y) + 0x9e3779b9u));
  return vec2(float(h & 0xFFFFu), float(pcgHash(h) & 0xFFFFu)) / 65535.0;
}

// One beam family along lattice axis @p axis (0 x, 1 y, 2 z): transverse 4D
// coordinates @p ct, axial coordinate @p s, and the world-frame w coordinate
// @p w. The beam segment between lattice points k and k + 1 along the axis is
// one single-bit link of the algebra; it carries strands exactly when that
// link is a DMZ (zero-divisor) edge of the strut, with the helix handedness
// and braid set by the edge sign. Updates the nearest beam distance, the nearest strand
// distance, and the nearest strand's tier and sign.
void beamFamily(vec2 ct, float s, float w, int axis, inout float dBeam, inout float dStrand) {
  vec2 n = round(ct / cellSize);
  vec2 t = ct - (n * cellSize);
  float rad = length(t);
  dBeam = min(dBeam, rad - (BEAM_RADIUS_FRACTION * cellSize));
  float outerRadius = SHELL_RADIUS_FRACTION[1] * cellSize;
  float shellBound = rad - outerRadius - (TIER_RADIUS_FRACTION[2] * cellSize);
  if (rad > STRAND_CULL_FRACTION * cellSize) {
    dStrand = min(dStrand, shellBound);
    return;
  }
  ivec2 nt = ivec2(n);
  float axial = s / cellSize;
  int k = int(floor(axial));
  float f = axial - float(k);
  int kw = int(round(w / cellSize));
  ivec4 step = ivec4(axis == 0 ? 1 : 0, axis == 1 ? 1 : 0, axis == 2 ? 1 : 0, 0);
  float ang = atan(t.y, t.x);
  // The segment holding s and its nearer neighbor; each strand is clipped to
  // its own segment, so its distance is at least the axial distance outside
  // it. Segments farther along the axis are at least max(f, 1 - f) cells away.
  dStrand = min(dStrand, max(shellBound, max(f, 1.0 - f) * cellSize));
  for (int pass = 0; pass < 2; ++pass) {
    int segment = pass == 0 ? k : (f < 0.5 ? k - 1 : k + 1);
    float outside = pass == 0 ? 0.0 : min(f, 1.0 - f) * cellSize;
    if (max(shellBound, outside) >= dStrand) {
      continue;
    }
    ivec4 lattice = axis == 0 ? ivec4(segment, nt.x, nt.y, kw)
                              : (axis == 1 ? ivec4(nt.y, segment, nt.x, kw) : ivec4(nt.x, nt.y, segment, kw));
    int i = algebraIndex(lattice);
    int bit = findLSB(i ^ algebraIndex(lattice + step));
    uvec2 m = algebraMaskAt(i);
    if (((m.r >> uint(bit)) & 1u) == 0u) {
      continue;
    }
    float edgeSign = ((m.g >> uint(bit)) & 1u) != 0u ? 1.0 : -1.0;
    // The edge sign picks the shell: a +1 link is one wide helix, a -1 link a
    // tight triple braid of the opposite hand.
    int shell = edgeSign > 0.0 ? 1 : 0;
    vec2 segmentId = latticeCellId(n) + vec2(0.0, float(segment) * 0.37);
    int count = SHELL_STRANDS[shell];
    float pitch = SHELL_PITCH_FRACTION[shell] * cellSize;
    float phi = (SHELL_DIRECTION[shell] * TAU * s / pitch) + (STRAND_W_TWIST * w / cellSize) +
                (float(shell) * 1.9);
    float sector = round((ang - phi) * float(count) / TAU);
    float centerAngle = phi + (TAU * sector / float(count));
    vec2 c = SHELL_RADIUS_FRACTION[shell] * cellSize * vec2(cos(centerAngle), sin(centerAngle));
    float index = mod(sector, float(count));
    vec2 h = hash21((segmentId * 1.7) + vec2((float(axis) * 3.1) + (float(shell) * 11.0), index * 5.3));
    int tier = h.x < 0.5 ? 0 : (h.x < 0.8 ? 1 : 2);
    float d = max(length(t - c) - (TIER_RADIUS_FRACTION[tier] * cellSize), outside);
    if (d < dStrand) {
      dStrand = d;
      gTierBrightness = TIER_BRIGHTNESS[tier];
      gTierRadius = TIER_RADIUS_FRACTION[tier] * cellSize;
      gStrandSign = edgeSign;
    }
  }
}

// Box-kite glyph distance at 4D point @p p4: an octahedron at the nearest
// lattice vertex, sized by the number of box-kites the vertex anchors (the set
// bits of its DMZ mask), limited to GLYPH_W_HALF cells in w. The six true
// vertices of each box-kite are non-local in the lattice; the glyph marks the
// anchor. Any other vertex's glyph is at least cell - max|q| - radius away.
float kiteDistance(vec4 p4) {
  vec4 v = round(p4 / cellSize);
  vec4 q = p4 - (v * cellSize);
  vec4 aq = abs(q);
  float rMax = GLYPH_RADIUS_MAX * cellSize;
  float others = cellSize - max(max(aq.x, aq.y), max(aq.z, aq.w)) - rMax;
  if (kitesEnabled == 0) {
    return 1e9;
  }
  int i = algebraIndex(ivec4(v));
  int kites = bitCount(algebraMaskAt(i).r);
  if (kites == 0) {
    return others;
  }
  gKiteIndex = i;
  float fraction = float(kites) / float(ALGEBRA_BOX_KITES_PER_VERTEX);
  float radius = mix(GLYPH_RADIUS_MIN, GLYPH_RADIUS_MAX, clamp(fraction, 0.0, 1.0)) * cellSize;
  float octa = (aq.x + aq.y + aq.z - radius) * 0.57735027;
  return min(max(octa, aq.w - (GLYPH_W_HALF * cellSize)), others);
}

// Beam, strand, and box-kite distances at eye-relative point @p p; @p p4
// returns the 4D point.
void fieldDistances(vec3 p, out float dBeam, out float dStrand, out float dKite, out vec4 p4) {
  p4 = slicePoint(p);
  dBeam = 1e9;
  dStrand = 1e9;
  gTierBrightness = TIER_BRIGHTNESS[1];
  gTierRadius = TIER_RADIUS_FRACTION[1] * cellSize;
  gStrandSign = 1.0;
  beamFamily(p4.yz, p4.x, p4.w, 0, dBeam, dStrand);
  beamFamily(p4.zx, p4.y, p4.w, 1, dBeam, dStrand);
  beamFamily(p4.xy, p4.z, p4.w, 2, dBeam, dStrand);
  dKite = kiteDistance(p4);
}

float mapDistance(vec3 p) {
  float dBeam;
  float dStrand;
  float dKite;
  vec4 p4;
  fieldDistances(p, dBeam, dStrand, dKite, p4);
  return min(min(dBeam, dStrand), dKite);
}

vec3 estimateNormal(vec3 p, float e) {
  const vec2 k = vec2(1.0, -1.0);
  return normalize((k.xyy * mapDistance(p + (k.xyy * e))) + (k.yyx * mapDistance(p + (k.yyx * e))) +
                   (k.yxy * mapDistance(p + (k.yxy * e))) + (k.xxx * mapDistance(p + (k.xxx * e))));
}

// Sphere-traces from the eye-relative @p rayOrigin along @p rayDir. Returns the travelled
// distance, whether a surface was hit, and the halo radiance gathered along
// the march.
float raymarch(vec3 rayOrigin, vec3 rayDir, float fogDistance, out bool hit, out vec3 halo) {
  int maxSteps = qualityTier == 0 ? 256 : 160;
  float maxDistance = MAX_MARCH_CELLS * cellSize;
  float surfaceEps = cellSize * SURFACE_EPS_FRACTION;
  float minStep = cellSize * MIN_STEP_FRACTION;
  float haloRadius = HALO_RADIUS_FRACTION * cellSize;
  // Half a pixel's footprint per unit of travel: a fiber thinner than a pixel
  // still registers a hit inside its footprint instead of being skipped, and
  // a grazing ray stops as soon as it is within a pixel of the fiber.
  float pixelAngle = fovScale / max(resolution.y, 1.0);
  float travelled = 0.0;
  hit = false;
  halo = vec3(0.0);
  float d = 0.0;
  float eps = surfaceEps;
  for (int step = 0; step < maxSteps; ++step) {
    vec3 p = rayOrigin + (rayDir * travelled);
    float dBeam;
    float dStrand;
    float dKite;
    vec4 p4;
    fieldDistances(p, dBeam, dStrand, dKite, p4);
    d = min(min(dBeam, dStrand), dKite);
    eps = max(surfaceEps, travelled * pixelAngle);
    if (abs(d) < eps) {
      hit = true;
      break;
    }
    // Step by |d|: the eye can start inside a beam (no collision guard), where
    // a negative d would stall the march.
    float stepLength = max(abs(d) * STEP_SCALE, minStep);
    float strandLight = exp(-max(dStrand, 0.0) / haloRadius) * gTierBrightness;
    halo += STRAND_HALO_COLOR * (HALO_GAIN * strandLight * (stepLength / cellSize) *
                                 fogTransmittance(travelled, fogDistance) * wDim(p4.w));
    travelled += stepLength;
    if (travelled > maxDistance) {
      break;
    }
  }
  // A ray that spent its whole step budget within a few footprints of a
  // surface (a fiber seen at a grazing angle) is a hit, not a miss.
  if (!hit && travelled <= maxDistance && abs(d) < GRAZE_ACCEPT_FOOTPRINTS * eps) {
    hit = true;
  }
  return travelled;
}

vec3 shadeHit(vec3 p, vec3 rayDir, float footprint) {
  float dBeam;
  float dStrand;
  float dKite;
  vec4 p4;
  fieldDistances(p, dBeam, dStrand, dKite, p4);
  bool kite = dKite < min(dBeam, dStrand);
  bool strand = !kite && dStrand < dBeam;
  float tierBrightness = gTierBrightness;
  float tierRadius = gTierRadius;
  float strandSign = gStrandSign;
  int kiteIndex = gKiteIndex;
  vec3 normal = estimateNormal(p, max(0.002 * cellSize, 0.5 * footprint));
  float facing = clamp(dot(normal, -rayDir), 0.0, 1.0);
  float cue = wDim(p4.w);
  vec3 radiance;
  float radius;
  if (kite) {
    // Emissive octahedron: the four faces with an even number of negative
    // coordinates (the sails) glow, the other four stay dim.
    vec4 q = p4 - (round(p4 / cellSize) * cellSize);
    bool sail = (q.x * q.y * q.z) > 0.0;
    radiance = algebraLevelColor(kiteIndex) * (sail ? GLYPH_SAIL_GAIN : GLYPH_FACE_GAIN);
    radius = GLYPH_RADIUS_MAX * cellSize;
  } else if (strand) {
    float depth = eyeDepth + p.z;
    float period = max(corridorPeriod, 1e-3);
    float depthPattern = mod(depth, period);
    float lit = gaussian(depthPattern, mod(nowDepth, period), nowWidth);
    float pulse = pulseEnabled != 0 ? gaussian(depthPattern, mod(pulseDepth, period), pulseWidth) : 0.0;
    // Round fiber: brightest on the axis, falling off across the width.
    float core = pow(facing, 1.5);
    // Negative-sign links run the opposite helix and take a cooler tint.
    vec3 tint = strandSign > 0.0 ? vec3(1.0) : STRAND_COOL_TINT;
    radiance = mix(STRAND_HALO_COLOR, STRAND_CORE_COLOR, core) * tint * (0.25 + (0.75 * core)) *
               tierBrightness * (1.0 + lit + (1.8 * pulse));
    radius = tierRadius;
  } else {
    float rim = pow(1.0 - facing, 4.0);
    float spec = pow(facing, 40.0);
    radiance = (BEAM_COLOR * (0.02 + (0.06 * facing))) + (BEAM_RIM_COLOR * BEAM_RIM_GAIN * rim) +
               (vec3(1.0, 0.82, 0.6) * BEAM_SPEC_GAIN * spec);
    radius = 2.0 * BEAM_RADIUS_FRACTION * cellSize;
  }
  // A fiber thinner than one pixel's footprint covers part of the pixel.
  float coverage = clamp(radius / max(footprint, 1e-6), 0.0, 1.0);
  return radiance * strandGlow * cue * coverage;
}


void main() {
  vec3 rayDir = bhRayDir(gl_FragCoord.xy, resolution, fovScale, cameraBasis);
  float fogDistance = fogDistanceFor(fogDensity);

  bool hit;
  vec3 halo;
  float travelled = raymarch(vec3(0.0), rayDir, fogDistance, hit, halo);

  float footprint = travelled * fovScale / max(resolution.y, 1.0);
  vec3 shaded = hit ? shadeHit(rayDir * travelled, rayDir, footprint) : vec3(0.0);
  float extinction = fogTransmittance(travelled, fogDistance);
  vec3 color = (shaded * extinction) + (halo * strandGlow) + (VOID_COLOR * (1.0 - extinction));
  if (wallsEnabled != 0) {
    color += quasicrystalWalls(rayDir, hit ? travelled : MAX_MARCH_CELLS * cellSize, fogDistance) * strandGlow;
  }

  fragColor = vec4(color, 1.0);
}
