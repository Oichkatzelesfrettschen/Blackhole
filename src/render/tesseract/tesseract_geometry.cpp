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

#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>

namespace blackhole::tesseract {
namespace {

constexpr std::size_t AXIS_COUNT = 4;

/** Bit mask with bit @p axis set. */
constexpr std::size_t bit(std::size_t axis) {
  return std::size_t{1} << axis;
}

void appendSubdivided(std::vector<SegmentInstance> &out, const glm::vec4 &a, const glm::vec4 &b,
                      std::size_t pieces, SegmentKind kind) {
  const auto steps = static_cast<float>(pieces);
  for (std::size_t k = 0; k < pieces; ++k) {
    const float s0 = static_cast<float>(k) / steps;
    const float s1 = static_cast<float>(k + 1) / steps;
    SegmentInstance seg;
    seg.a = a + ((b - a) * s0);
    seg.b = a + ((b - a) * s1);
    seg.meta = glm::vec4(-1.0f, -1.0f, static_cast<float>(kind), -1.0f);
    out.push_back(seg);
  }
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
  return glm::vec3(p) * (eyeDistance / (eyeDistance - p.w));
}

glm::vec3 projectStereographic(const glm::vec4 &p) {
  return glm::vec3(p) / (1.0f - p.w);
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
  const float u = (t - litMoment) / width;
  return std::exp(-0.5f * u * u);
}

float gravityPulseTime(float wallSeconds, float speed, float tNow, float tPast) {
  const float span = tNow - tPast;
  if (span <= 0.0f) {
    return tNow;
  }
  float travelled = std::fmod(speed * wallSeconds, span);
  if (travelled < 0.0f) {
    travelled += span;
  }
  return tNow - travelled;
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
    for (std::size_t k = 0; k + 1 < tube.size(); ++k) {
      SegmentInstance seg;
      seg.a = libraryToTesseract(tube.at(k), options.timeSpan);
      seg.b = libraryToTesseract(tube.at(k + 1), options.timeSpan);
      seg.meta = glm::vec4(tube.at(k).w, tube.at(k + 1).w,
                           static_cast<float>(SegmentKind::WorldTube), static_cast<float>(strand));
      segments.push_back(seg);
    }
  }

  for (const auto &link : bedroomOutline()) {
    appendSubdivided(segments, glm::vec4(features.at(link.at(0)).position, 0.0f),
                     glm::vec4(features.at(link.at(1)).position, 0.0f), pieces,
                     SegmentKind::LitSlice);
  }
  return segments;
}

} // namespace blackhole::tesseract
