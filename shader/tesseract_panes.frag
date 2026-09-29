#version 460 core
#extension GL_GOOGLE_include_directive : enable
/**
 * @file tesseract_panes.frag
 * @brief Emanation-table panes of the tesseract scene, drawn additively over
 *        the lattice of shader/tesseract.frag.
 *
 * The planes p4.z = m cellSize, which face the corridor axis, carry the
 * strutted emanation table of the 1024-dimensional Cayley-Dickson algebra
 * (src/render/tesseract/emanation_table.h, baked by the CPU into an R16I
 * texture). Each pane tile shows the whole 510 x 510 table, indexed by the two
 * in-plane periodic slice coordinates (p4.x, p4.y), with the beams along its
 * edges. A filled (zero-divisor) cell glows: the high bits of |value| = a ^ b
 * (the table sub-block) set the hue, the sign picks warm or cool.
 *
 * The pass is analytic: p4 is affine in the ray parameter, so a pane crossing
 * is a division, the table is read at the first EMANATION_PANES crossings
 * ahead of the eye, and no march step touches the texture. Panes are light
 * added over the frame, so the beams and strands do not occlude them.
 *
 * Zoom nesting (Theorem 11, de Marrais): the level-l table of a strut is the
 * four corner blocks of its level-(l+1) table. A pane nearer the eye squeezes
 * the central cross of its table away and shows the next lower level, down to
 * the lowest level holding the strut; the texture stays level 10 and the
 * shader maps indices (emanationExpand). A xor-triple walk over the filled
 * cells (xorTripleWalk) marks its lead cell and trail on the nearest panes.
 */

#include "include/interop_raygen.glsl"
#include "include/tesseract_slice.glsl"
#include "include/tesseract_emanation_palette.glsl"

layout(location = 0) out vec4 fragColor;

uniform vec2 resolution;
uniform vec3 eye;
uniform mat3 cameraBasis; // columns (right, up, forward), buildCameraBasis order.
uniform float fovScale;   // tan(fovDeg / 2)
uniform float strandGlow;
uniform float fogDensity;
uniform float emanationGain;
uniform float emanationFill;   // Filled fraction of the addressable table cells.
uniform int emanationMinLevel; // Lowest level whose table holds the strut; 10 turns nesting off.
// Xor-triple pulse walk: lead cell and trail as level-10 (row, column), newest first.
const int EMANATION_TRAIL = 8;
uniform ivec2 emanationTrail[EMANATION_TRAIL];
uniform int emanationTrailCount;
uniform float emanationTrailPhase; // Fraction of the lead step elapsed.

// Level-10 emanation table, signed values in tone-row order, 0 = not filled.
// Binding matches TESSERACT_EMANATION_UNIT in tesseract_renderer.h.
layout(binding = 3) uniform isampler2D emanationTable;

// The lattice pass stops marching at this many cells.
const float MAX_MARCH_CELLS = 24.0;

const int EMANATION_TOP_LEVEL = 10;
// Panes read per ray, nearest first.
const int EMANATION_PANES = 4;
// Zoom nesting: a pane at t cells from the eye has folded
// (FOLD_START - t) * FOLD_RATE times toward the strut's lowest level.
const float EMANATION_FOLD_START = 3.2;
const float EMANATION_FOLD_RATE = 2.0;
// Brightness falls by 1 / (1 + FOLD_DIM * folds): coarse cells cover more pixels.
const float EMANATION_FOLD_DIM = 0.3;
// Pixel footprint in table cells over which a pane blends to its mean fill.
const float EMANATION_BLUR_START = 1.0;
const float EMANATION_BLUR_END = 3.0;
const float EMANATION_GAIN = 0.08;
// Fill fraction at which a pane's per-cell glow is EMANATION_GAIN.
const float EMANATION_REFERENCE_FILL = 0.3;
const float EMANATION_GLOW_CORE = 0.35;
const float EMANATION_GLOW_EDGE = 1.0;
// Pulse walk marker: trail brightness per step of age, size in pixels (at
// least), the nearest panes that carry it, and gain against the pane glow.
const float EMANATION_TRAIL_DECAY = 0.62;
const float EMANATION_TRAIL_PIXELS = 6.0;
const int EMANATION_TRAIL_PANES = 2;
const float EMANATION_TRAIL_GAIN = 1.2;
const vec3 EMANATION_TRAIL_COLOR = vec3(1.0, 0.72, 0.38);

// emanation-map-begin
// Tone-row labels per row and column at level @p level: 2^(level - 1) - 2.
int emanationLevelSize(int level) {
  return (1 << (level - 1)) - 2;
}

// Index at the top level of index @p index of the level-@p level table
// (emanation_table.h expandToLevel). Theorem 11: the level-l table is the four
// corner blocks of the level-(l+1) table, so the second half of the indices
// shifts past the central cross.
int emanationExpand(int index, int level) {
  for (int l = level; l < EMANATION_TOP_LEVEL; ++l) {
    int size = emanationLevelSize(l);
    if (index >= size / 2) {
      index += emanationLevelSize(l + 1) - size;
    }
  }
  return index;
}

// Position in the level-@p level table of display coordinate @p s, when the
// table's central cross (the cells the next lower level lacks) is squeezed to
// (1 - @p fold) of its width: fold 0 shows the level, fold 1 shows the level below.
float emanationFoldPosition(float s, int level, float fold) {
  float size = float(emanationLevelSize(level));
  float below = float(emanationLevelSize(level - 1));
  float corner = 0.5 * below;
  float band = size - below;
  float squeezed = band * (1.0 - fold);
  if (s < corner) {
    return s;
  }
  if (s < corner + squeezed) {
    return corner + ((s - corner) / max(1.0 - fold, 1e-4));
  }
  return s + (fold * band);
}

// emanation-map-end

// Radiance of the level-@p level table at pane display coordinates @p uv (cells
// of the folded table per tile): each filled cell among the 2 x 2 nearest
// contributes a soft round glow of at most one cell radius, joined by max so
// overlapping cells do not sum past a single cell's color. The glow thickens
// the one-cell lines of sparse tables into readable strokes and doubles as
// the antialiasing kernel. Cells of the central cross fade as it folds away.
vec3 emanationGlow(vec2 uv, int level, float fold) {
  int size = emanationLevelSize(level);
  int corner = emanationLevelSize(level - 1) / 2;
  vec2 position = vec2(emanationFoldPosition(uv.x, level, fold),
                       emanationFoldPosition(uv.y, level, fold));
  // The four cells whose centers are nearest: the glow reaches at most one cell.
  ivec2 first = ivec2(floor(position - 0.5));
  // A coarse level's cells span many pixels: keep them crisp instead of a wide halo.
  float coarse = float(EMANATION_TOP_LEVEL - level) / 5.0;
  float glowEdge = mix(EMANATION_GLOW_EDGE, 0.62, coarse);
  float glowCore = mix(EMANATION_GLOW_CORE, 0.34, coarse);
  ivec2 top = ivec2(emanationExpand(first.x, level), emanationExpand(first.y, level));
  ivec2 next = ivec2(emanationExpand(first.x + 1, level), emanationExpand(first.y + 1, level));
  vec3 glow = vec3(0.0);
  for (int dy = 0; dy <= 1; ++dy) {
    for (int dx = 0; dx <= 1; ++dx) {
      ivec2 cell = first + ivec2(dx, dy);
      if (any(lessThan(cell, ivec2(0))) || any(greaterThanEqual(cell, ivec2(size)))) {
        continue;
      }
      int v = texelFetch(emanationTable, ivec2(dx == 0 ? top.x : next.x, dy == 0 ? top.y : next.y), 0).r;
      if (v == 0) {
        continue;
      }
      bool inCross = (cell.x >= corner && cell.x < size - corner) ||
                     (cell.y >= corner && cell.y < size - corner);
      float weight = 1.0 - smoothstep(glowCore, glowEdge, length(position - (vec2(cell) + 0.5)));
      weight *= inCross ? 1.0 - fold : 1.0;
      glow = max(glow, emanationColor(v, level) * weight);
    }
  }
  return glow;
}

// emanation-display-begin
// Display coordinate of the center of level-10 cell @p cell10 in the
// level-@p level table folded by @p fold, or -1 when the cell lies in a central
// cross the fold has removed (inverse of emanationExpand and emanationFoldPosition).
float emanationDisplayPosition(int cell10, int level, float fold) {
  int index = cell10;
  for (int l = EMANATION_TOP_LEVEL - 1; l >= level; --l) {
    int small = emanationLevelSize(l);
    int big = emanationLevelSize(l + 1);
    int corner = small / 2;
    if (index >= corner && index < big - corner) {
      return -1.0;
    }
    if (index >= big - corner) {
      index -= big - small;
    }
  }
  float size = float(emanationLevelSize(level));
  float below = float(emanationLevelSize(max(level - 1, 3)));
  float corner = 0.5 * below;
  float band = size - below;
  float x = float(index) + 0.5;
  if (x < corner) {
    return x;
  }
  if (x < size - corner) {
    return corner + ((x - corner) * (1.0 - fold));
  }
  return x - (fold * band);
}

// emanation-display-end

// Light of the pulse walk at display coordinate @p uv: a soft disc at each
// trail cell, fading by age, at least EMANATION_TRAIL_PIXELS wide.
vec3 emanationTrailGlow(vec2 uv, int level, float fold, float cellsPerPixel) {
  float radius = max(1.5, EMANATION_TRAIL_PIXELS * cellsPerPixel);
  vec3 glow = vec3(0.0);
  for (int i = 0; i < EMANATION_TRAIL; ++i) {
    if (i >= emanationTrailCount) {
      break;
    }
    // Texel x is the table column and texel y the row.
    float sx = emanationDisplayPosition(emanationTrail[i].y, level, fold);
    float sy = emanationDisplayPosition(emanationTrail[i].x, level, fold);
    if (sx < 0.0 || sy < 0.0) {
      continue;
    }
    float d = length(uv - vec2(sx, sy)) / radius;
    // The lead cell brightens through its step, older cells fade by age.
    float age = float(i) + (i == 0 ? 0.0 : emanationTrailPhase);
    float strength = pow(EMANATION_TRAIL_DECAY, age) * (i == 0 ? 0.5 + (0.5 * emanationTrailPhase) : 1.0);
    glow += EMANATION_TRAIL_COLOR * (strength * exp(-2.0 * d * d));
  }
  return glow;
}

// Additive light of the emanation panes along a ray up to @p tEnd: the planes
// p4.z = m cellSize, which face the corridor axis, so the tile of each is seen
// face-on and the beams along its edges frame it. p4 is affine in the ray
// parameter t, so the first EMANATION_PANES crossings ahead of the eye are
// divisions and the table is read once per crossing.
vec3 emanationPanes(vec3 rayDir, float tEnd, float fogDistance) {
  vec4 a = slicePoint(eye);
  vec4 b = (gF0 * rayDir.x) + (gF1 * rayDir.y) + (gF2 * rayDir.z);
  float incidence = abs(b.z);
  if (incidence < 1e-4) {
    return vec3(0.0);
  }
  float pixelAngle = fovScale / max(resolution.y, 1.0);
  float maxFolds = float(EMANATION_TOP_LEVEL - emanationMinLevel);
  float dir = b.z > 0.0 ? 1.0 : -1.0;
  float u0 = a.z / cellSize;
  float first = dir > 0.0 ? floor(u0) + 1.0 : ceil(u0) - 1.0;
  float grazing = smoothstep(0.03, 0.3, incidence);
  vec3 meanLight = emanationFill * mix(EMANATION_WARM_LOW, EMANATION_WARM_HIGH, 0.5);
  vec3 sum = vec3(0.0);
  vec3 trail = vec3(0.0);
  for (int j = 0; j < EMANATION_PANES; ++j) {
    float plane = first + (dir * float(j));
    float t = ((plane * cellSize) - a.z) / b.z;
    if (t <= 0.0 || t >= tEnd) {
      break;
    }
    vec4 q = a + (b * t);
    // Zoom nesting: nearer panes have folded further toward the strut's lowest level.
    float nest = clamp((EMANATION_FOLD_START - (t / cellSize)) * EMANATION_FOLD_RATE, 0.0, maxFolds);
    int level = EMANATION_TOP_LEVEL - int(floor(nest));
    float fold = nest - floor(nest);
    float levelSize = float(emanationLevelSize(level));
    float displaySize = levelSize - (fold * (levelSize - float(emanationLevelSize(max(level - 1, 3)))));
    // Tile coordinates: the two in-plane periodic slice coordinates.
    vec2 uv = fract(q.xy / cellSize) * displaySize;
    // Pixel footprint in display cells; beyond a few cells the table reads as its mean.
    float footprint = (t * pixelAngle) / (max(incidence, 0.05) * (cellSize / displaySize));
    vec3 light = mix(emanationGlow(uv, level, fold), meanLight,
                     smoothstep(EMANATION_BLUR_START, EMANATION_BLUR_END, footprint));
    // A pane closer than a fraction of a cell would fill the frame with one table cell.
    float nearFade = smoothstep(0.25, 0.7, t / cellSize);
    float paneWeight = grazing * nearFade * fogTransmittance(t, fogDistance) * wDim(q.w);
    sum += light * (paneWeight / (1.0 + (EMANATION_FOLD_DIM * nest)));
    if (j < EMANATION_TRAIL_PANES) {
      trail += emanationTrailGlow(uv, level, fold, 2.0 * footprint) * paneWeight;
    }
  }
  // Equal mean pane energy across struts: sparse tables glow brighter per cell.
  float sparsity = clamp(EMANATION_REFERENCE_FILL / max(emanationFill, 0.01), 0.15, 3.0);
  return (sum * (EMANATION_GAIN * sparsity) + (trail * EMANATION_TRAIL_GAIN)) * (emanationGain * strandGlow);
}

void main() {
  buildSliceFrame();
  vec3 rayDir = bhRayDir(gl_FragCoord.xy, resolution, fovScale, cameraBasis);
  float fogDistance = fogDistanceFor(fogDensity);
  fragColor = vec4(emanationPanes(rayDir, MAX_MARCH_CELLS * cellSize, fogDistance), 0.0);
}
