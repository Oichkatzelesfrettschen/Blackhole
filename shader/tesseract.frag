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
// Fraction of beams that carry strand shells.
const float STRAND_BEAM_FRACTION = 0.45;
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

// One beam family: transverse 4D coordinates @p ct, axial coordinate @p s,
// and the world-frame w coordinate @p w. Updates the nearest beam distance,
// the nearest strand distance, and the nearest strand's tier.
void beamFamily(vec2 ct, float s, float w, float family, inout float dBeam, inout float dStrand) {
  vec2 n = round(ct / cellSize);
  vec2 t = ct - (n * cellSize);
  float rad = length(t);
  dBeam = min(dBeam, rad - (BEAM_RADIUS_FRACTION * cellSize));
  float outerRadius = SHELL_RADIUS_FRACTION[1] * cellSize;
  if (rad > STRAND_CULL_FRACTION * cellSize) {
    dStrand = min(dStrand, rad - outerRadius - (TIER_RADIUS_FRACTION[2] * cellSize));
    return;
  }
  // Only some beams carry strands: bare beams keep the frame void-dominated.
  if (hash21((latticeCellId(n) * 2.3) + vec2(family * 5.7, 1.3)).y > STRAND_BEAM_FRACTION) {
    return;
  }
  float ang = atan(t.y, t.x);
  for (int shell = 0; shell < 2; ++shell) {
    int count = SHELL_STRANDS[shell];
    float pitch = SHELL_PITCH_FRACTION[shell] * cellSize;
    float phi = (SHELL_DIRECTION[shell] * TAU * s / pitch) +
                (STRAND_W_TWIST * w / cellSize) + (float(shell) * 1.9);
    float sector = round((ang - phi) * float(count) / TAU);
    float centerAngle = phi + (TAU * sector / float(count));
    vec2 c = SHELL_RADIUS_FRACTION[shell] * cellSize * vec2(cos(centerAngle), sin(centerAngle));
    float index = mod(sector, float(count));
    vec2 h = hash21((latticeCellId(n) * 1.7) + vec2((family * 3.1) + (float(shell) * 11.0), index * 5.3));
    int tier = h.x < 0.5 ? 0 : (h.x < 0.8 ? 1 : 2);
    float d = length(t - c) - (TIER_RADIUS_FRACTION[tier] * cellSize);
    if (d < dStrand) {
      dStrand = d;
      gTierBrightness = TIER_BRIGHTNESS[tier];
      gTierRadius = TIER_RADIUS_FRACTION[tier] * cellSize;
    }
  }
}

// Beam and strand distances at eye-relative point @p p; @p p4 returns the 4D point.
void fieldDistances(vec3 p, out float dBeam, out float dStrand, out vec4 p4) {
  p4 = slicePoint(p);
  dBeam = 1e9;
  dStrand = 1e9;
  gTierBrightness = TIER_BRIGHTNESS[1];
  gTierRadius = TIER_RADIUS_FRACTION[1] * cellSize;
  beamFamily(p4.yz, p4.x, p4.w, 0.0, dBeam, dStrand);
  beamFamily(p4.zx, p4.y, p4.w, 1.0, dBeam, dStrand);
  beamFamily(p4.xy, p4.z, p4.w, 2.0, dBeam, dStrand);
}

float mapDistance(vec3 p) {
  float dBeam;
  float dStrand;
  vec4 p4;
  fieldDistances(p, dBeam, dStrand, p4);
  return min(dBeam, dStrand);
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
    vec4 p4;
    fieldDistances(p, dBeam, dStrand, p4);
    d = min(dBeam, dStrand);
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
  vec4 p4;
  fieldDistances(p, dBeam, dStrand, p4);
  bool strand = dStrand < dBeam;
  float tierBrightness = gTierBrightness;
  float tierRadius = gTierRadius;
  vec3 normal = estimateNormal(p, max(0.002 * cellSize, 0.5 * footprint));
  float facing = clamp(dot(normal, -rayDir), 0.0, 1.0);
  float cue = wDim(p4.w);
  vec3 radiance;
  float radius;
  if (strand) {
    float depth = eyeDepth + p.z;
    float period = max(corridorPeriod, 1e-3);
    float depthPattern = mod(depth, period);
    float lit = gaussian(depthPattern, mod(nowDepth, period), nowWidth);
    float pulse = pulseEnabled != 0 ? gaussian(depthPattern, mod(pulseDepth, period), pulseWidth) : 0.0;
    // Round fiber: brightest on the axis, falling off across the width.
    float core = pow(facing, 1.5);
    radiance = mix(STRAND_HALO_COLOR, STRAND_CORE_COLOR, core) * (0.25 + (0.75 * core)) *
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


// ---- Quasicrystal walls (prototype): Ammann-Beenker cut-and-project of the
// Z^4 lattice whose points name the basis units of the 4096-dimensional
// Cayley-Dickson algebra (Gray-Morton index). A tiling edge n -> n + e_j is a
// single-bit XOR of the two indices, lit warm or cool when it is a DMZ
// (zero-divisor) edge of strut QC_STRUT. docs/plans/tesseract-quasicrystal-algebra.md.
const int QC_DIM = 4096;
const int QC_HALF = 2048;
const int QC_STRUT = 17;
const int QC_PLANES = 6;
const float QC_WALL_FRACTION = 0.12;
const float QC_INSET = 0.08;
const float QC_TILES = 9.0; // Tiling units across a wall.
const float QC_S = 0.70710678;
const vec4 QC_U1 = vec4(1.0, QC_S, 0.0, -QC_S) * QC_S;
const vec4 QC_U2 = vec4(0.0, QC_S, 1.0, QC_S) * QC_S;
const vec4 QC_V1 = vec4(1.0, -QC_S, 0.0, QC_S) * QC_S;
const vec4 QC_V2 = vec4(0.0, QC_S, -1.0, QC_S) * QC_S;
const vec3 QC_WARM = vec3(1.0, 0.62, 0.22);
const vec3 QC_COOL = vec3(0.30, 0.62, 1.0);
const vec3 QC_CHORD = vec3(0.75, 0.35, 1.0);
const vec3 QC_FAINT = vec3(0.35, 0.24, 0.14);

int qcSign(int p, int q) {
  int sign = 1;
  for (int halfDim = QC_DIM >> 1; halfDim > 0; halfDim >>= 1) {
    bool pHigh = p >= halfDim;
    bool qHigh = q >= halfDim;
    if (!pHigh && qHigh) {
      int qLow = q - halfDim;
      q = p;
      p = qLow;
    } else if (pHigh && !qHigh) {
      p -= halfDim;
      if (q != 0) {
        sign = -sign;
      }
    } else if (pHigh && qHigh) {
      int qLow = q - halfDim;
      int pLow = p - halfDim;
      if (qLow == 0) {
        return -sign;
      }
      p = qLow;
      q = pLow;
    }
  }
  return sign;
}

// Signed DMZ value of assessors (a, a ^ x) and (b, b ^ x), 0 when not a DMZ.
int qcDmz(int x, int a, int b) {
  int ul = qcSign(a ^ x, b);
  int ur = qcSign(a ^ x, b ^ x);
  int ll = qcSign(a, b);
  int lr = qcSign(a, b ^ x);
  bool one = ul == lr;
  bool two = ur == ll;
  if (one != two) {
    return 0;
  }
  return one ? 1 : -1;
}

int qcIndex(ivec4 n) {
  ivec4 k = n & 7;
  ivec4 g = k ^ (k >> 1);
  int i = 0;
  for (int d = 0; d < 3; ++d) {
    for (int a = 0; a < 4; ++a) {
      i |= ((g[a] >> d) & 1) << ((4 * d) + a);
    }
  }
  return i;
}

// Octagon window pi_perp([0,1]^4) as four slabs around its center.
bool qcAccepted(vec2 perp) {
  vec2 d = perp - vec2(dot(vec4(0.5), QC_V1), dot(vec4(0.5), QC_V2));
  for (int k = 0; k < 4; ++k) {
    vec2 wk = vec2(QC_V1[k], QC_V2[k]);
    vec2 nk = normalize(vec2(-wk.y, wk.x));
    float halfWidth = 0.0;
    for (int j = 0; j < 4; ++j) {
      halfWidth += 0.5 * abs(dot(nk, vec2(QC_V1[j], QC_V2[j])));
    }
    if (abs(dot(nk, d)) > halfWidth + 1e-5) {
      return false;
    }
  }
  return true;
}

vec3 qcEdgeColor(int ia, int ib, out float weight) {
  int x = QC_HALF + QC_STRUT;
  if (((ia ^ ib) & QC_HALF) != 0) {
    weight = 0.5;
    return QC_CHORD;
  }
  int a = ia >= QC_HALF ? ia ^ x : ia;
  int b = ib >= QC_HALF ? ib ^ x : ib;
  if (a == 0 || b == 0 || a == QC_STRUT || b == QC_STRUT || (a ^ b) == QC_STRUT) {
    weight = 0.3;
    return QC_FAINT;
  }
  int v = qcDmz(x, a, b);
  weight = v == 0 ? 0.3 : 1.0;
  return v == 0 ? QC_FAINT : (v > 0 ? QC_WARM : QC_COOL);
}

float qcSegment(vec2 p, vec2 a, vec2 b) {
  vec2 ab = b - a;
  float h = clamp(dot(p - a, ab) / dot(ab, ab), 0.0, 1.0);
  return length(p - a - (ab * h));
}

// Light of the tiling at tiling coordinate y with phason offset gamma.
vec3 qcTiling(vec2 y, vec2 gamma, float unitsPerPixel) {
  vec2 c = gamma + vec2(dot(vec4(0.5), QC_V1), dot(vec4(0.5), QC_V2));
  vec4 lift = (QC_U1 * y.x) + (QC_U2 * y.y) + (QC_V1 * c.x) + (QC_V2 * c.y);
  ivec4 base = ivec4(floor(lift + 0.5));
  ivec4 kept[12];
  vec2 keptPar[12];
  int count = 0;
  for (int t = 0; t < 81 && count < 12; ++t) {
    ivec4 n = base + ivec4(t % 3, (t / 3) % 3, (t / 9) % 3, t / 27) - 1;
    vec4 nf = vec4(n);
    vec2 par = vec2(dot(nf, QC_U1), dot(nf, QC_U2));
    if (length(par - y) > 1.1) {
      continue;
    }
    if (!qcAccepted(vec2(dot(nf, QC_V1), dot(nf, QC_V2)) - gamma)) {
      continue;
    }
    kept[count] = n;
    keptPar[count] = par;
    ++count;
  }
  float lineWidth = max(0.025, 1.2 * unitsPerPixel);
  vec3 light = vec3(0.0);
  for (int i = 0; i < count; ++i) {
    int ii = qcIndex(kept[i]);
    for (int j = i + 1; j < count; ++j) {
      ivec4 dn = kept[j] - kept[i];
      int l1 = abs(dn.x) + abs(dn.y) + abs(dn.z) + abs(dn.w);
      if (l1 != 1) {
        continue;
      }
      float d = qcSegment(y, keptPar[i], keptPar[j]);
      float cover = 1.0 - smoothstep(0.5 * lineWidth, 1.5 * lineWidth, d);
      if (cover <= 0.0) {
        continue;
      }
      float weight;
      vec3 col = qcEdgeColor(ii, qcIndex(kept[j]), weight);
      light = max(light, col * (weight * cover));
    }
    // Vertex: hue by the level of the smallest algebra holding e_i.
    float level = ii == 0 ? 0.0 : floor(log2(float(ii))) + 1.0;
    vec3 levelColor = mix(vec3(1.0, 0.45, 0.15), vec3(0.55, 0.85, 1.0), clamp((level - 5.0) / 7.0, 0.0, 1.0));
    float dv = length(y - keptPar[i]);
    light = max(light, levelColor * (1.0 - smoothstep(1.5 * lineWidth, 3.0 * lineWidth, dv)) * 0.8);
  }
  return light;
}

uint qcPcg(uint v) {
  uint state = (v * 747796405u) + 2891336453u;
  uint word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
  return (word >> 22u) ^ word;
}

vec2 qcWallHash(vec2 tile, float plane) {
  ivec2 t = ivec2(latticeCellId(tile));
  int m = int(latticeCellId(vec2(plane)).x);
  uint h = qcPcg(uint(t.x) + qcPcg(uint(t.y) + qcPcg(uint(m) + 0x9e3779b9u)));
  return vec2(float(h & 0xFFFFu), float(qcPcg(h) & 0xFFFFu)) / 65535.0;
}

vec3 quasicrystalWalls(vec3 rayDir, float tEnd, float fogDistance) {
  vec4 a = eyeSlice;
  vec4 b = sliceOffset(rayDir);
  float incidence = abs(b.z);
  if (incidence < 1e-4) {
    return vec3(0.0);
  }
  float pixelAngle = fovScale / max(resolution.y, 1.0);
  float dir = b.z > 0.0 ? 1.0 : -1.0;
  float u0 = a.z / cellSize;
  float first = dir > 0.0 ? floor(u0) + 1.0 : ceil(u0) - 1.0;
  float wallEdge = 1.0 - (2.0 * QC_INSET);
  vec3 sum = vec3(0.0);
  for (int j = 0; j < QC_PLANES; ++j) {
    float plane = first + (dir * float(j));
    float t = ((plane * cellSize) - a.z) / b.z;
    if (t <= 0.0 || t >= tEnd) {
      break;
    }
    vec4 q = a + (b * t);
    vec2 tileCoord = q.xy / cellSize;
    vec2 tile = floor(tileCoord);
    vec2 h = qcWallHash(tile, plane);
    if (h.x > QC_WALL_FRACTION) {
      continue;
    }
    vec2 wallUv = ((tileCoord - tile) - QC_INSET) / wallEdge;
    if (any(lessThan(wallUv, vec2(0.0))) || any(greaterThanEqual(wallUv, vec2(1.0)))) {
      continue;
    }
    float wallPixels = (cellSize * wallEdge * max(incidence, 0.05)) / (t * pixelAngle);
    float unitsPerPixel = QC_TILES / max(wallPixels, 1.0);
    vec2 y = (wallUv * QC_TILES) + (h * 131.0);
    // Phason offset: per wall, drifting with the eye's 4D position (prototype).
    vec2 gamma = (fract(h * 7.31) - 0.5) * 0.6 + vec2(dot(eyeSlice, QC_V1), dot(eyeSlice, QC_V2)) / cellSize;
    vec3 light = qcTiling(y, gamma, unitsPerPixel);
    float edgePixels = min(min(wallUv.x, wallUv.y), min(1.0 - wallUv.x, 1.0 - wallUv.y)) * wallPixels;
    light += vec3(0.5, 0.33, 0.16) * exp(-edgePixels / 1.5) * 0.3;
    float nearFade = smoothstep(0.25, 0.7, t / cellSize);
    float grazing = smoothstep(0.03, 0.3, incidence);
    sum += light * (grazing * nearFade * fogTransmittance(t, fogDistance) * wDim(q.w));
  }
  return sum * 0.35 * strandGlow;
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
  color += quasicrystalWalls(rayDir, hit ? travelled : MAX_MARCH_CELLS * cellSize, fogDistance);

  fragColor = vec4(color, 1.0);
}
