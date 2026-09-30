#ifndef TESSERACT_ALGEBRA_GLSL
#define TESSERACT_ALGEBRA_GLSL

/**
 * @file tesseract_algebra.glsl
 * @brief The tesseract lattice read as the basis of the 4096-dimensional
 *        Cayley-Dickson algebra, and its Ammann-Beenker walls
 *        (src/render/tesseract/algebra_lattice.h holds the CPU twin and the
 *        definitions; docs/plans/tesseract-quasicrystal-algebra.md the design).
 *
 * Requires shader/include/tesseract_slice.glsl and the uniforms resolution
 * and fovScale.
 */

// DMZ mask of the current strut, 64 x 64 texels for the 4096 indices:
// r bit b set when the link i -> i ^ 2^b is a DMZ edge, g bit b when its sign
// is +1. Binding matches TESSERACT_ALGEBRA_MASK_UNIT in tesseract_renderer.h.
layout(binding = 3) uniform usampler2D algebraMask;

const int ALGEBRA_HALF = 2048;           // Generator G of level 12: bit 11 is the assessor-chord direction.
const int ALGEBRA_CHORD_BIT = 11;
const int ALGEBRA_BOX_KITES_PER_VERTEX = 10; // N - 2 local octahedra through a vertex.

// Basis index of lattice point @p n (algebra_lattice.h grayMortonIndex).
int algebraIndex(ivec4 n) {
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

uvec2 algebraMaskAt(int i) {
  return texelFetch(algebraMask, ivec2(i & 63, i >> 6), 0).rg;
}

// Level of the smallest algebra holding e_i (bit length of i), 0 for e_0.
float algebraLevel(int i) {
  return i == 0 ? 0.0 : float(findMSB(i) + 1);
}

// Hue of a vertex by algebra level: 32-D deep amber to 4096-D ice blue.
vec3 algebraLevelColor(int i) {
  return mix(vec3(1.0, 0.45, 0.15), vec3(0.55, 0.85, 1.0), clamp((algebraLevel(i) - 5.0) / 7.0, 0.0, 1.0));
}

// ---- Ammann-Beenker walls -------------------------------------------------

// Orthonormal physical-plane and perpendicular-plane bases (algebra_lattice.h
// AMMANN_BEENKER_PAR and AMMANN_BEENKER_PERP).
const vec4 AB_PAR_X = vec4(0.70710678, 0.5, 0.0, -0.5);
const vec4 AB_PAR_Y = vec4(0.0, 0.5, 0.70710678, 0.5);
const vec4 AB_PERP_X = vec4(0.70710678, -0.5, 0.0, 0.5);
const vec4 AB_PERP_Y = vec4(0.0, 0.5, -0.70710678, 0.5);

// Fraction of plane tiles that hold a wall, the inset of a wall inside its
// tile, tiling edges across a wall, and planes tested per ray.
const float WALL_FRACTION = 0.09;
const float WALL_INSET = 0.08;
const float WALL_TILES = 9.0;
const int WALL_PLANES = 6;
const float WALL_GAIN = 0.35;

const vec3 WALL_WARM = vec3(1.0, 0.62, 0.22);   // DMZ edge, sign +1.
const vec3 WALL_COOL = vec3(0.30, 0.62, 1.0);   // DMZ edge, sign -1.
const vec3 WALL_CHORD = vec3(0.75, 0.35, 1.0);  // Link across bit 11 (assessor chords).
const vec3 WALL_FAINT = vec3(0.35, 0.24, 0.14); // Tiling edge that is no DMZ edge.
const vec3 WALL_FRAME = vec3(0.5, 0.33, 0.16);

// Octagon window pi_perp([0, 1]^4): four slabs about its center; every slab
// has half-width (1 + sqrt 2) / (2 sqrt 2) for this regular octagon.
bool abAccepted(vec2 perp) {
  vec2 d = perp - vec2(dot(vec4(0.5), AB_PERP_X), dot(vec4(0.5), AB_PERP_Y));
  const float halfWidth = 0.85355339;
  for (int k = 0; k < 4; ++k) {
    vec2 wk = vec2(AB_PERP_X[k], AB_PERP_Y[k]);
    vec2 nk = normalize(vec2(-wk.y, wk.x));
    if (abs(dot(nk, d)) > halfWidth + 1e-5) {
      return false;
    }
  }
  return true;
}

float segmentDistance(vec2 p, vec2 a, vec2 b) {
  vec2 ab = b - a;
  float h = clamp(dot(p - a, ab) / dot(ab, ab), 0.0, 1.0);
  return length(p - a - (ab * h));
}

// Color and weight of the tiling edge between indices @p ia and @p ib.
vec3 wallEdgeColor(int ia, int ib, out float weight) {
  int bit = findLSB(ia ^ ib);
  if (bit == ALGEBRA_CHORD_BIT) {
    weight = 0.5;
    return WALL_CHORD;
  }
  uvec2 m = algebraMaskAt(ia);
  if (((m.r >> uint(bit)) & 1u) == 0u) {
    weight = 0.3;
    return WALL_FAINT;
  }
  weight = 1.0;
  return ((m.g >> uint(bit)) & 1u) != 0u ? WALL_WARM : WALL_COOL;
}

// Light of the tiling at physical-plane point @p y for phason offset
// @p gamma: the accepted lattice points within reach of y (a 3^4 search about
// the lift of y onto the window center), the unit steps among them as edges,
// and the points as dots colored by algebra level.
vec3 ammannBeenker(vec2 y, vec2 gamma, float unitsPerPixel) {
  vec2 c = gamma + vec2(dot(vec4(0.5), AB_PERP_X), dot(vec4(0.5), AB_PERP_Y));
  vec4 lift = (AB_PAR_X * y.x) + (AB_PAR_Y * y.y) + (AB_PERP_X * c.x) + (AB_PERP_Y * c.y);
  ivec4 base = ivec4(floor(lift + 0.5));
  ivec4 kept[12];
  vec2 keptPar[12];
  int count = 0;
  for (int t = 0; t < 81 && count < 12; ++t) {
    ivec4 n = base + ivec4(t % 3, (t / 3) % 3, (t / 9) % 3, t / 27) - 1;
    vec4 nf = vec4(n);
    vec2 par = vec2(dot(nf, AB_PAR_X), dot(nf, AB_PAR_Y));
    if (length(par - y) > 1.1) {
      continue;
    }
    if (!abAccepted(vec2(dot(nf, AB_PERP_X), dot(nf, AB_PERP_Y)) - gamma)) {
      continue;
    }
    kept[count] = n;
    keptPar[count] = par;
    ++count;
  }
  float lineWidth = max(0.025, 1.2 * unitsPerPixel);
  vec3 light = vec3(0.0);
  for (int i = 0; i < count; ++i) {
    int ii = algebraIndex(kept[i]);
    for (int j = i + 1; j < count; ++j) {
      ivec4 dn = abs(kept[j] - kept[i]);
      if (dn.x + dn.y + dn.z + dn.w != 1) {
        continue;
      }
      float cover = 1.0 - smoothstep(0.5 * lineWidth, 1.5 * lineWidth, segmentDistance(y, keptPar[i], keptPar[j]));
      if (cover <= 0.0) {
        continue;
      }
      float weight;
      vec3 edge = wallEdgeColor(ii, algebraIndex(kept[j]), weight);
      light = max(light, edge * (weight * cover));
    }
    float vertexCover = 1.0 - smoothstep(1.5 * lineWidth, 3.0 * lineWidth, length(y - keptPar[i]));
    light = max(light, algebraLevelColor(ii) * (0.8 * vertexCover));
  }
  return light;
}

uint wallPcg(uint v) {
  uint state = (v * 747796405u) + 2891336453u;
  uint word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
  return (word >> 22u) ^ word;
}

// Two uniform [0, 1] values for the wall slot of tile @p tile on plane
// @p plane, reduced onto the lattice period so slots repeat with the wrapped eye.
vec2 wallHash(vec2 tile, float plane) {
  ivec2 t = ivec2(latticeCellId(tile));
  int m = int(latticeCellId(vec2(plane)).x);
  uint h = wallPcg(uint(t.x) + wallPcg(uint(t.y) + wallPcg(uint(m) + 0x9e3779b9u)));
  return vec2(float(h & 0xFFFFu), float(wallPcg(h) & 0xFFFFu)) / 65535.0;
}

// Phason offset of the walls from the eye's 4D point: pi_perp of a periodic
// lift of the eye (period latticePeriodCells cells in x, y, z), so the tiles
// flip as the eye travels and the offset is continuous across the lattice wrap.
vec2 wallPhason() {
  float period = latticePeriodCells;
  const float tau = 6.28318530718;
  vec3 xyz = (period / tau) * sin((tau / period) * (eyeSlice.xyz / cellSize));
  vec4 lift = vec4(xyz, eyeSlice.w / cellSize);
  return vec2(dot(lift, AB_PERP_X), dot(lift, AB_PERP_Y));
}

// Additive light of the quasicrystal walls along a ray up to @p tEnd. Walls
// hang on the planes p4.z = m cellSize in WALL_FRACTION of the tiles, inset
// from the beams; p4 is affine in the ray parameter, so each crossing is a division.
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
  float wallEdge = 1.0 - (2.0 * WALL_INSET);
  vec2 phason = wallPhason();
  vec3 sum = vec3(0.0);
  for (int j = 0; j < WALL_PLANES; ++j) {
    float plane = first + (dir * float(j));
    float t = ((plane * cellSize) - a.z) / b.z;
    if (t <= 0.0 || t >= tEnd) {
      break;
    }
    vec4 q = a + (b * t);
    vec2 tileCoord = q.xy / cellSize;
    vec2 tile = floor(tileCoord);
    vec2 h = wallHash(tile, plane);
    if (h.x > WALL_FRACTION) {
      continue;
    }
    vec2 wallUv = ((tileCoord - tile) - WALL_INSET) / wallEdge;
    if (any(lessThan(wallUv, vec2(0.0))) || any(greaterThanEqual(wallUv, vec2(1.0)))) {
      continue;
    }
    float wallPixels = (cellSize * wallEdge * max(incidence, 0.05)) / (t * pixelAngle);
    float unitsPerPixel = WALL_TILES / max(wallPixels, 1.0);
    // Each wall shows its own patch of the tiling and its own phason sheet.
    vec2 y = (wallUv * WALL_TILES) + (h * 131.0);
    vec2 gamma = ((fract(h * 7.31) - 0.5) * 0.6) + phason;
    vec3 light = ammannBeenker(y, gamma, unitsPerPixel);
    float edgePixels = min(min(wallUv.x, wallUv.y), min(1.0 - wallUv.x, 1.0 - wallUv.y)) * wallPixels;
    light += WALL_FRAME * (0.3 * exp(-edgePixels / 1.5));
    float nearFade = smoothstep(0.25, 0.7, t / cellSize);
    float grazing = smoothstep(0.03, 0.3, incidence);
    sum += light * (grazing * nearFade * fogTransmittance(t, fogDistance) * wDim(q.w));
  }
  return sum * WALL_GAIN;
}

#endif // TESSERACT_ALGEBRA_GLSL
