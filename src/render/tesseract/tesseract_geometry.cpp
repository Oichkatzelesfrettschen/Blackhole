/**
 * @file tesseract_geometry.cpp
 * @brief 4-cube complex, 4D->3D projections, and library-of-time strands.
 */

#include "render/tesseract/tesseract_geometry.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <vector>

#include <glm/common.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/geometric.hpp>

#include "render/tesseract/so4.h"

namespace blackhole::tesseract {
namespace {

constexpr std::size_t AXIS_COUNT = 4;

/** Bit mask with bit @p axis set. */
constexpr std::size_t bit(std::size_t axis) {
  return std::size_t{1} << axis;
}

// Segments between consecutive @p points, each with its neighbors' points;
// meta x, y, and w come from @p meta per segment. An open polyline caps its
// two ends; a closed one also joins the last point back to the first and
// wraps the neighbors, so no end draws a cap.
template <typename MetaFn>
void appendPolyline(std::vector<SegmentInstance> &out, const std::vector<glm::vec4> &points,
                    bool closed, SegmentKind kind, MetaFn meta) {
  const std::size_t n = points.size();
  if (n < 2) {
    return;
  }
  const std::size_t count = closed ? n : n - 1;
  for (std::size_t k = 0; k < count; ++k) {
    const bool first = !closed && k == 0;
    const bool last = !closed && k + 1 == count;
    SegmentInstance seg;
    seg.a = points.at(k);
    seg.b = points.at((k + 1) % n);
    seg.prev = first ? seg.a : points.at((k + n - 1) % n);
    seg.next = last ? seg.b : points.at((k + 2) % n);
    const glm::vec3 xyw = meta(k);
    seg.meta = glm::vec4(xyw.x, xyw.y, packSegmentTag(kind, first, last), xyw.z);
    out.push_back(seg);
  }
}

glm::vec3 unusedMeta(std::size_t /*segment*/) {
  return {-1.0f, -1.0f, -1.0f};
}

// Points from @p a toward @p b at k / pieces for k in [0, pieces), then b
// when @p withEnd holds.
void appendSubdividedPoints(std::vector<glm::vec4> &points, const glm::vec4 &a, const glm::vec4 &b,
                            std::size_t pieces, bool withEnd) {
  const auto steps = static_cast<float>(pieces);
  for (std::size_t k = 0; k < pieces; ++k) {
    points.push_back(a + ((b - a) * (static_cast<float>(k) / steps)));
  }
  if (withEnd) {
    points.push_back(b);
  }
}

void appendSubdivided(std::vector<SegmentInstance> &out, const glm::vec4 &a, const glm::vec4 &b,
                      std::size_t pieces, SegmentKind kind) {
  std::vector<glm::vec4> points;
  points.reserve(pieces + 1);
  appendSubdividedPoints(points, a, b, pieces, true);
  appendPolyline(out, points, false, kind, unusedMeta);
}

} // namespace

glm::vec4 tesseractVertex(std::size_t index) {
  auto coordinate = [index](std::size_t axis) { return (index & bit(axis)) != 0 ? 1.0f : -1.0f; };
  return {coordinate(0), coordinate(1), coordinate(2), coordinate(3)};
}

TesseractMesh buildTesseract() {
  TesseractMesh mesh;
  for (std::size_t i = 0; i < TESSERACT_VERTEX_COUNT; ++i) {
    mesh.vertices.at(i) = tesseractVertex(i);
  }
  for (std::size_t i = 0; i < TESSERACT_VERTEX_COUNT; ++i) {
    for (std::size_t axis = 0; axis < AXIS_COUNT; ++axis) {
      if ((i & bit(axis)) == 0) {
        mesh.edges.push_back({.a = i, .b = i | bit(axis), .axis = axis});
      }
    }
  }
  for (std::size_t axisA = 0; axisA < AXIS_COUNT; ++axisA) {
    for (std::size_t axisB = axisA + 1; axisB < AXIS_COUNT; ++axisB) {
      const std::size_t spanMask = bit(axisA) | bit(axisB);
      for (std::size_t base = 0; base < TESSERACT_VERTEX_COUNT; ++base) {
        if ((base & spanMask) != 0) {
          continue;
        }
        mesh.faces.push_back(
            {.vertices = {base, base | bit(axisA), base | spanMask, base | bit(axisB)},
             .axisA = axisA,
             .axisB = axisB});
      }
    }
  }
  for (std::size_t axis = 0; axis < AXIS_COUNT; ++axis) {
    for (const bool positive : {false, true}) {
      TesseractCell cell;
      cell.axis = axis;
      cell.sign = positive ? 1.0f : -1.0f;
      std::size_t slot = 0;
      for (std::size_t i = 0; i < TESSERACT_VERTEX_COUNT; ++i) {
        if (((i & bit(axis)) != 0) == positive) {
          cell.vertices.at(slot) = i;
          ++slot;
        }
      }
      mesh.cells.push_back(cell);
    }
  }
  return mesh;
}

glm::vec3 projectPerspective(const glm::vec4 &p, float eyeDistance) {
  const float denom = std::max(eyeDistance - p.w, PERSPECTIVE_MIN_DEPTH);
  return glm::vec3(p) * (eyeDistance / denom);
}

StereographicPoint projectStereographic(const glm::vec4 &p) {
  const float len = glm::length(p);
  const glm::vec4 s = len > STEREOGRAPHIC_MIN_NORM ? p / len : glm::vec4(0.0f, 0.0f, 0.0f, -1.0f);
  const float denom = 1.0f - s.w;
  StereographicPoint out;
  out.fade = glm::smoothstep(STEREOGRAPHIC_MIN_DENOM, STEREOGRAPHIC_FADE_END, denom);
  out.position = glm::vec3(s) / std::max(denom, STEREOGRAPHIC_MIN_DENOM);
  return out;
}

std::vector<LibraryFeature> bedroomFeatures() {
  std::vector<LibraryFeature> features;
  // Shelf: five books along x on the back wall.
  for (const float x : {-0.6f, -0.3f, 0.0f, 0.3f, 0.6f}) {
    features.push_back({.kind = FeatureKind::Shelf, .position = glm::vec3(x, 0.55f, -0.7f)});
  }
  // Window: four frame corners on the +x wall.
  features.push_back({.kind = FeatureKind::Window, .position = glm::vec3(0.75f, 0.0f, -0.4f)});
  features.push_back({.kind = FeatureKind::Window, .position = glm::vec3(0.75f, 0.0f, 0.4f)});
  features.push_back({.kind = FeatureKind::Window, .position = glm::vec3(0.75f, 0.6f, 0.4f)});
  features.push_back({.kind = FeatureKind::Window, .position = glm::vec3(0.75f, 0.6f, -0.4f)});
  // Desk: four corners of the desk top.
  features.push_back({.kind = FeatureKind::Desk, .position = glm::vec3(-0.7f, -0.35f, 0.05f)});
  features.push_back({.kind = FeatureKind::Desk, .position = glm::vec3(-0.1f, -0.35f, 0.05f)});
  features.push_back({.kind = FeatureKind::Desk, .position = glm::vec3(-0.1f, -0.35f, 0.55f)});
  features.push_back({.kind = FeatureKind::Desk, .position = glm::vec3(-0.7f, -0.35f, 0.55f)});
  return features;
}

std::vector<std::array<std::size_t, 2>> bedroomOutline() {
  return {// Shelf line through the five books.
          {0, 1},
          {1, 2},
          {2, 3},
          {3, 4},
          // Window frame loop.
          {5, 6},
          {6, 7},
          {7, 8},
          {8, 5},
          // Desk top loop.
          {9, 10},
          {10, 11},
          {11, 12},
          {12, 9}};
}

std::vector<OutlinePolyline> outlinePolylines() {
  std::vector<OutlinePolyline> lines;
  for (const auto &link : bedroomOutline()) {
    if (lines.empty() || lines.back().closed || lines.back().features.back() != link.at(0)) {
      lines.push_back({.features = {link.at(0)}, .closed = false});
    }
    OutlinePolyline &line = lines.back();
    line.features.push_back(link.at(1));
    line.closed = line.features.size() > 2 && line.features.back() == line.features.front();
  }
  return lines;
}

std::vector<glm::vec4> extrudeWorldTube(const glm::vec3 &point, float timeSpan,
                                        std::size_t samples) {
  const std::size_t count = std::max<std::size_t>(samples, 2);
  const auto last = static_cast<float>(count - 1);
  std::vector<glm::vec4> tube;
  tube.reserve(count);
  for (std::size_t k = 0; k < count; ++k) {
    tube.emplace_back(point, timeSpan * (static_cast<float>(k) / last));
  }
  return tube;
}

glm::vec4 libraryToTesseract(const glm::vec4 &p, float timeSpan) {
  return {p.x, p.y, p.z, ((2.0f * p.w) / timeSpan) - 1.0f};
}

float litMomentEmission(float t, float litMoment, float width) {
  const float u = (t - litMoment) / std::max(width, EMISSION_MIN_WIDTH);
  return std::exp(-0.5f * u * u);
}

float advancePulseTravel(float travel, float distance, float span) {
  if (span <= 0.0f) {
    return 0.0f;
  }
  float wrapped = std::fmod(travel + distance, span);
  if (wrapped < 0.0f) {
    wrapped += span;
  }
  return wrapped;
}

So4Pair<double> advanceOrientation(const So4Pair<double> &orientation,
                                   const std::array<float, 3> &leftRate,
                                   const std::array<float, 3> &rightRate, double ds) {
  const auto step = [ds](const std::array<float, 3> &rate) {
    return quatExp(ds * static_cast<double>(rate.at(0)), ds * static_cast<double>(rate.at(1)),
                   ds * static_cast<double>(rate.at(2)));
  };
  return {.left = normalized(step(leftRate) * orientation.left),
          .right = normalized(step(rightRate) * orientation.right)};
}

TesseractMotion tesseractMotionAt(const std::array<float, 3> &leftRate,
                                  const std::array<float, 3> &rightRate, double resetPhase,
                                  double rotationSpeed, float pulseSpeed, float pulseSpan,
                                  double seconds) {
  TesseractMotion motion;
  motion.orientation = advanceOrientation(So4Pair<double>{}, leftRate, rightRate,
                                          resetPhase + (rotationSpeed * seconds));
  motion.pulseTravel = advancePulseTravel(
      0.0f, static_cast<float>(static_cast<double>(pulseSpeed) * seconds), pulseSpan);
  return motion;
}

float packSegmentTag(SegmentKind kind, bool capA, bool capB) {
  const int tag = static_cast<int>(kind) | (capA ? SEGMENT_CAP_A : 0) | (capB ? SEGMENT_CAP_B : 0);
  return static_cast<float>(tag);
}

SegmentKind segmentKind(const SegmentInstance &segment) {
  return static_cast<SegmentKind>(static_cast<int>(std::lround(segment.meta.z)) &
                                  SEGMENT_KIND_MASK);
}

bool segmentCapped(const SegmentInstance &segment, bool endB) {
  const int bit = endB ? SEGMENT_CAP_B : SEGMENT_CAP_A;
  return (static_cast<int>(std::lround(segment.meta.z)) & bit) != 0;
}

std::vector<SegmentInstance> buildSceneSegments(const SceneSegmentOptions &options) {
  std::vector<SegmentInstance> segments;
  const TesseractMesh mesh = buildTesseract();
  const std::size_t pieces = std::max<std::size_t>(options.edgeSubdivisions, 1);
  for (const TesseractEdge &edge : mesh.edges) {
    appendSubdivided(segments, mesh.vertices.at(edge.a), mesh.vertices.at(edge.b), pieces,
                     SegmentKind::TesseractEdge);
  }

  const std::vector<LibraryFeature> features = bedroomFeatures();
  for (std::size_t strand = 0; strand < features.size(); ++strand) {
    const std::vector<glm::vec4> tube =
        extrudeWorldTube(features.at(strand).position, options.timeSpan, options.tubeSamples);
    std::vector<glm::vec4> points(tube.size());
    std::ranges::transform(tube, points.begin(), [&options](const glm::vec4 &sample) {
      return libraryToTesseract(sample, options.timeSpan);
    });
    appendPolyline(segments, points, false, SegmentKind::WorldTube, [&tube, strand](std::size_t k) {
      return glm::vec3(tube.at(k).w, tube.at(k + 1).w, static_cast<float>(strand));
    });
  }

  const auto corner = [&features](std::size_t index) {
    return glm::vec4(features.at(index).position, 0.0f);
  };
  for (const OutlinePolyline &line : outlinePolylines()) {
    std::vector<glm::vec4> points;
    for (std::size_t k = 0; k + 1 < line.features.size(); ++k) {
      appendSubdividedPoints(points, corner(line.features.at(k)), corner(line.features.at(k + 1)),
                             pieces, false);
    }
    if (!line.closed) {
      points.push_back(corner(line.features.back()));
    }
    appendPolyline(segments, points, line.closed, SegmentKind::LitSlice, unusedMeta);
  }
  return segments;
}

} // namespace blackhole::tesseract
