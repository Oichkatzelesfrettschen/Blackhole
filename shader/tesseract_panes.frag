#version 460 core
#extension GL_GOOGLE_include_directive : enable
/**
 * @file tesseract_panes.frag
 * @brief Emanation-table pages of the tesseract scene, drawn additively over
 *        the lattice of shader/tesseract.frag.
 *
 * Pages hang in a sparse set of lattice tiles on the planes p4.z = m cellSize,
 * which face the corridor axis: a hash of the tile and plane picks
 * EMANATION_PAGE_FRACTION of them, and each page is inset from the beams that
 * frame its tile, so the corridor between pages stays dark. A page carries the
 * strutted emanation table of the 1024-dimensional Cayley-Dickson algebra
 * (src/render/tesseract/emanation_table.h, baked by the CPU into an R16I
 * texture), indexed by the two in-plane slice coordinates (p4.x, p4.y). A
 * filled (zero-divisor) cell lights as a square: the high bits of
 * |value| = a ^ b (the table sub-block) set the hue, the sign picks warm or
 * cool; an empty cell adds nothing.
 *
 * The pass is analytic: p4 is affine in the ray parameter, so a plane crossing
 * is a division, the first EMANATION_PLANES crossings ahead of the eye are
 * tested for a page, and no march step touches the texture. Pages are light
 * added over the frame, so the beams and strands do not occlude them.
 *
 * Zoom nesting (Theorem 11, de Marrais): the level-l table of a strut is the
 * four corner blocks of its level-(l+1) table. A page shows the level whose
 * cells span about EMANATION_CELL_PIXELS on screen, down to the lowest level
 * holding the strut, so a distant page shows a coarse table and an
 * approaching page opens the central cross of each level in turn until it
 * shows level 10; the texture stays level 10 and the shader maps indices
 * (emanationExpand). A page whose finest reachable level is still finer than
 * EMANATION_BLUR_START cells per pixel fades out. A xor-triple walk over the
 * filled cells (xorTripleWalk) marks its lead cell and trail on the nearest
 * pages.
 */

#include "include/interop_raygen.glsl"
#include "include/tesseract_slice.glsl"
#include "include/tesseract_emanation_palette.glsl"

layout(location = 0) out vec4 fragColor;

uniform vec2 resolution;
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
// Planes tested per ray, nearest first.
const int EMANATION_PLANES = 6;
// Fraction of plane tiles that hold a page, and the inset of a page from each
// beam of its tile, as a fraction of the tile.
const float EMANATION_PAGE_FRACTION = 0.10;
const float EMANATION_PAGE_INSET = 0.1;
// Screen pixels per table cell the zoom nesting aims for.
const float EMANATION_CELL_PIXELS = 4.0;
// Half the edge of a lit cell's square, in cells: the gap between neighbors
// keeps the table's rows and columns apart.
const float EMANATION_CELL_HALF = 0.36;
// Table cells per pixel over which a page too fine to resolve fades out.
const float EMANATION_BLUR_START = 0.6;
const float EMANATION_BLUR_END = 1.5;
const float EMANATION_GAIN = 0.25;
// Fill fraction at which a page's per-cell glow is EMANATION_GAIN.
const float EMANATION_REFERENCE_FILL = 0.3;
// Faint frame along each page edge, about EMANATION_FRAME_PIXELS wide.
const vec3 EMANATION_FRAME_COLOR = vec3(0.6, 0.4, 0.2);
const float EMANATION_FRAME_PIXELS = 1.5;
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

// Radiance of the level-@p level table at page display coordinates @p uv
// (cells of the folded table across the page): each filled cell among the
// 2 x 2 nearest lights a square of half-edge EMANATION_CELL_HALF, antialiased
// over @p cellsPerPixel and joined by max, so neighbors never sum past one
// cell's color. Cells of the central cross fade as it folds away.
vec3 emanationGlow(vec2 uv, int level, float fold, float cellsPerPixel) {
  int size = emanationLevelSize(level);
  int corner = emanationLevelSize(level - 1) / 2;
  vec2 position = vec2(emanationFoldPosition(uv.x, level, fold),
                       emanationFoldPosition(uv.y, level, fold));
  // The four cells whose centers are nearest.
  ivec2 first = ivec2(floor(position - 0.5));
  ivec2 top = ivec2(emanationExpand(first.x, level), emanationExpand(first.y, level));
  ivec2 next = ivec2(emanationExpand(first.x + 1, level), emanationExpand(first.y + 1, level));
  float edgeWidth = clamp(cellsPerPixel, 0.02, 0.5);
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
      vec2 offset = abs(position - (vec2(cell) + 0.5));
      float weight = 1.0 - smoothstep(EMANATION_CELL_HALF - edgeWidth, EMANATION_CELL_HALF + edgeWidth,
                                      max(offset.x, offset.y));
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

uint emanationPcg(uint v) {
  uint state = (v * 747796405u) + 2891336453u;
  uint word = ((state >> ((state >> 28u) + 4u)) ^ state) * 277803737u;
  return (word >> 22u) ^ word;
}

// Uniform [0, 1] hash of a page slot: tile (x, y) and plane index, each
// reduced onto the lattice period so the slots repeat with the wrapped eye.
float emanationPageHash(vec2 tile, float plane) {
  ivec2 t = ivec2(latticeCellId(tile));
  int m = int(latticeCellId(vec2(plane)).x);
  uint h = emanationPcg(uint(t.x) + emanationPcg(uint(t.y) + emanationPcg(uint(m) + 0x9e3779b9u)));
  return float(h & 0xFFFFu) / 65535.0;
}

// Additive light of the emanation pages along a ray up to @p tEnd. The
// planes p4.z = m cellSize face the corridor axis, so a page is seen face-on
// inside the beams that frame its tile. p4 is affine in the ray parameter t,
// so each crossing ahead of the eye is a division and the table is read once
// per page crossed.
vec3 emanationPanes(vec3 rayDir, float tEnd, float fogDistance) {
  vec4 a = eyeSlice;
  vec4 b = sliceOffset(rayDir);
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
  float pageEdge = 1.0 - (2.0 * EMANATION_PAGE_INSET);
  vec3 sum = vec3(0.0);
  vec3 trail = vec3(0.0);
  int pages = 0;
  for (int j = 0; j < EMANATION_PLANES; ++j) {
    float plane = first + (dir * float(j));
    float t = ((plane * cellSize) - a.z) / b.z;
    if (t <= 0.0 || t >= tEnd) {
      break;
    }
    vec4 q = a + (b * t);
    vec2 tileCoord = q.xy / cellSize;
    vec2 tile = floor(tileCoord);
    if (emanationPageHash(tile, plane) > EMANATION_PAGE_FRACTION) {
      continue;
    }
    vec2 pageUv = ((tileCoord - tile) - EMANATION_PAGE_INSET) / pageEdge;
    if (any(lessThan(pageUv, vec2(0.0))) || any(greaterThanEqual(pageUv, vec2(1.0)))) {
      continue;
    }
    // Page extent in pixels along its foreshortened axis.
    float pagePixels = (cellSize * pageEdge * max(incidence, 0.05)) / (t * pixelAngle);
    // Zoom nesting: the level whose table spans pagePixels / EMANATION_CELL_PIXELS
    // cells, from size 2^(l - 1) - 2.
    float wantedLevel = log2(max(pagePixels / EMANATION_CELL_PIXELS, 1.0) + 2.0) + 1.0;
    float nest = clamp(float(EMANATION_TOP_LEVEL) - wantedLevel, 0.0, maxFolds);
    int level = EMANATION_TOP_LEVEL - int(floor(nest));
    float fold = nest - floor(nest);
    float levelSize = float(emanationLevelSize(level));
    float displaySize = levelSize - (fold * (levelSize - float(emanationLevelSize(max(level - 1, 3)))));
    vec2 uv = pageUv * displaySize;
    float cellsPerPixel = displaySize / pagePixels;
    float resolved = 1.0 - smoothstep(EMANATION_BLUR_START, EMANATION_BLUR_END, cellsPerPixel);
    float edgePixels = min(min(pageUv.x, pageUv.y), min(1.0 - pageUv.x, 1.0 - pageUv.y)) * pagePixels;
    vec3 light = (emanationGlow(uv, level, fold, cellsPerPixel) * resolved) +
                 (EMANATION_FRAME_COLOR * exp(-edgePixels / EMANATION_FRAME_PIXELS));
    // A page closer than a fraction of a cell would fill the frame with one table cell.
    float nearFade = smoothstep(0.25, 0.7, t / cellSize);
    float pageWeight = grazing * nearFade * fogTransmittance(t, fogDistance) * wDim(q.w);
    sum += light * pageWeight;
    if (pages < EMANATION_TRAIL_PANES) {
      trail += emanationTrailGlow(uv, level, fold, 2.0 * cellsPerPixel) * pageWeight * resolved;
    }
    ++pages;
  }
  // Equal mean page energy across struts: sparse tables glow brighter per cell.
  float sparsity = clamp(EMANATION_REFERENCE_FILL / max(emanationFill, 0.01), 0.15, 3.0);
  return (sum * (EMANATION_GAIN * sparsity) + (trail * EMANATION_TRAIL_GAIN)) * (emanationGain * strandGlow);
}

void main() {
  vec3 rayDir = bhRayDir(gl_FragCoord.xy, resolution, fovScale, cameraBasis);
  float fogDistance = fogDistanceFor(fogDensity);
  fragColor = vec4(emanationPanes(rayDir, MAX_MARCH_CELLS * cellSize, fogDistance), 0.0);
}
