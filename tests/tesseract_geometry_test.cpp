/**
 * @file tesseract_geometry_test.cpp
 * @brief 4-cube complex counts and incidence, 4D->3D projection formulas,
 *        world-tube extrusion, lit-moment and pulse timing, the scene segment
 *        layout, and the row-major -> glm upload of an SO(4) matrix.
 *
 * Float tolerances: 1e-6 covers single-precision products of O(1) values
 * (float epsilon 1.2e-7 times a few operations); 1e-5 covers the O(10)
 * library-time range.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <set>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/geometric.hpp>
#include <glm/gtc/type_ptr.hpp>

#include "render/tesseract/so4.h"
#include "render/tesseract/tesseract_geometry.h"

namespace {

namespace tess = blackhole::tesseract;

constexpr float UNIT_TOL = 1e-6f;
constexpr float TIME_TOL = 1e-5f;

std::array<float, 4> components(const glm::vec4 &v) {
  return {v.x, v.y, v.z, v.w};
}

std::size_t differingBits(std::size_t a, std::size_t b) {
  std::size_t diff = a ^ b;
  std::size_t count = 0;
  while (diff != 0) {
    count += diff & 1U;
    diff >>= 1U;
  }
  return count;
}

TEST(TesseractGeometry, CellCountsAndEulerCharacteristic) {
  const tess::TesseractMesh mesh = tess::buildTesseract();
  EXPECT_EQ(mesh.vertices.size(), 16U);
  EXPECT_EQ(mesh.edges.size(), 32U);
  EXPECT_EQ(mesh.faces.size(), 24U);
  EXPECT_EQ(mesh.cells.size(), 8U);
  const auto chi = static_cast<long>(mesh.vertices.size()) - static_cast<long>(mesh.edges.size()) +
                   static_cast<long>(mesh.faces.size()) - static_cast<long>(mesh.cells.size());
  EXPECT_EQ(chi, 0);
}

TEST(TesseractGeometry, VerticesAreSignVectors) {
  const tess::TesseractMesh mesh = tess::buildTesseract();
  std::set<std::array<int, 4>> distinct;
  for (const glm::vec4 &v : mesh.vertices) {
    for (const float c : components(v)) {
      EXPECT_EQ(std::abs(c), 1.0f);
    }
    distinct.insert({static_cast<int>(v.x), static_cast<int>(v.y), static_cast<int>(v.z),
                     static_cast<int>(v.w)});
  }
  EXPECT_EQ(distinct.size(), 16U);
}

TEST(TesseractGeometry, EdgesJoinVerticesDifferingInOneCoordinate) {
  const tess::TesseractMesh mesh = tess::buildTesseract();
  std::set<std::pair<std::size_t, std::size_t>> edgeSet;
  for (const tess::TesseractEdge &e : mesh.edges) {
    EXPECT_EQ(differingBits(e.a, e.b), 1U);
    EXPECT_FLOAT_EQ(glm::distance(mesh.vertices.at(e.a), mesh.vertices.at(e.b)), 2.0f);
    edgeSet.insert({std::min(e.a, e.b), std::max(e.a, e.b)});
  }
  EXPECT_EQ(edgeSet.size(), 32U);
  // Every face boundary is a 4-cycle of existing edges.
  for (const tess::TesseractFace &f : mesh.faces) {
    for (std::size_t k = 0; k < 4; ++k) {
      const std::size_t a = f.vertices.at(k);
      const std::size_t b = f.vertices.at((k + 1) % 4);
      EXPECT_TRUE(edgeSet.contains({std::min(a, b), std::max(a, b)}));
    }
  }
}

TEST(TesseractGeometry, CellsLieOnTheirBoundingHyperplane) {
  const tess::TesseractMesh mesh = tess::buildTesseract();
  for (const tess::TesseractCell &c : mesh.cells) {
    const std::set<std::size_t> distinct(c.vertices.begin(), c.vertices.end());
    EXPECT_EQ(distinct.size(), 8U);
    for (const std::size_t v : c.vertices) {
      EXPECT_EQ(components(mesh.vertices.at(v)).at(c.axis), c.sign);
    }
  }
}

TEST(TesseractProjection, PerspectiveScalesByEyeDistanceOverDepth) {
  const float d = 3.0f;
  const glm::vec3 atZero = tess::projectPerspective(glm::vec4(1.0f, 2.0f, 3.0f, 0.0f), d);
  EXPECT_NEAR(glm::distance(atZero, glm::vec3(1.0f, 2.0f, 3.0f)), 0.0f, UNIT_TOL);
  // Inner (w = -1) cube shrinks by d/(d+1), outer (w = +1) grows by d/(d-1).
  const glm::vec3 inner = tess::projectPerspective(glm::vec4(1.0f, 1.0f, 1.0f, -1.0f), d);
  const glm::vec3 outer = tess::projectPerspective(glm::vec4(1.0f, 1.0f, 1.0f, 1.0f), d);
  EXPECT_NEAR(inner.x, 0.75f, UNIT_TOL);
  EXPECT_NEAR(outer.x, 1.5f, UNIT_TOL);
}

TEST(TesseractProjection, StereographicPolesEquatorAndRadius) {
  const glm::vec3 south = tess::projectStereographic(glm::vec4(0.0f, 0.0f, 0.0f, -1.0f));
  EXPECT_NEAR(glm::length(south), 0.0f, UNIT_TOL);
  const glm::vec3 equator = tess::projectStereographic(glm::vec4(0.0f, 1.0f, 0.0f, 0.0f));
  EXPECT_NEAR(glm::distance(equator, glm::vec3(0.0f, 1.0f, 0.0f)), 0.0f, UNIT_TOL);
  // |p|^2 = (1 + w) / (1 - w) for any point of S^3.
  const glm::vec4 q = glm::normalize(glm::vec4(0.3f, -0.5f, 0.2f, 0.4f));
  const glm::vec3 p = tess::projectStereographic(q);
  EXPECT_NEAR(glm::dot(p, p), (1.0f + q.w) / (1.0f - q.w), UNIT_TOL);
  // Direction of xyz is preserved.
  EXPECT_NEAR(glm::dot(glm::normalize(p), glm::normalize(glm::vec3(q))), 1.0f, UNIT_TOL);
}

TEST(LibraryOfTime, WorldTubeExtrudesAlongW) {
  const glm::vec3 point(0.3f, -0.2f, 0.7f);
  const float span = 10.0f;
  const std::vector<glm::vec4> tube = tess::extrudeWorldTube(point, span, 11);
  ASSERT_EQ(tube.size(), 11U);
  for (std::size_t k = 0; k < tube.size(); ++k) {
    EXPECT_EQ(glm::vec3(tube.at(k)), point);
    EXPECT_NEAR(tube.at(k).w, static_cast<float>(k), TIME_TOL);
  }
  EXPECT_EQ(tube.front().w, 0.0f);
  EXPECT_EQ(tube.back().w, span);
  EXPECT_EQ(tess::extrudeWorldTube(point, span, 0).size(), 2U);
}

TEST(LibraryOfTime, LibraryTimeMapsOntoTesseractW) {
  const float span = 8.0f;
  EXPECT_NEAR(tess::libraryToTesseract(glm::vec4(0.0f, 0.0f, 0.0f, 0.0f), span).w, -1.0f, UNIT_TOL);
  EXPECT_NEAR(tess::libraryToTesseract(glm::vec4(0.0f, 0.0f, 0.0f, 4.0f), span).w, 0.0f, UNIT_TOL);
  EXPECT_NEAR(tess::libraryToTesseract(glm::vec4(0.0f, 0.0f, 0.0f, 8.0f), span).w, 1.0f, UNIT_TOL);
}

TEST(LibraryOfTime, LitMomentIsUnitGaussianInLibraryTime) {
  EXPECT_FLOAT_EQ(tess::litMomentEmission(6.0f, 6.0f, 0.5f), 1.0f);
  EXPECT_NEAR(tess::litMomentEmission(6.5f, 6.0f, 0.5f), std::exp(-0.5f), UNIT_TOL);
  EXPECT_NEAR(tess::litMomentEmission(5.5f, 6.0f, 0.5f), tess::litMomentEmission(6.5f, 6.0f, 0.5f),
              UNIT_TOL);
}

TEST(LibraryOfTime, GravityPulseRunsFromNowToPast) {
  const float now = 10.0f;
  const float past = 4.0f;
  const float speed = 2.0f;
  EXPECT_NEAR(tess::gravityPulseTime(0.0f, speed, now, past), now, TIME_TOL);
  EXPECT_NEAR(tess::gravityPulseTime(1.5f, speed, now, past), 7.0f, TIME_TOL);
  float previous = now + 1.0f;
  for (int step = 0; step < 29; ++step) {
    const float t = tess::gravityPulseTime(0.1f * static_cast<float>(step), speed, now, past);
    EXPECT_GT(t, past - TIME_TOL);
    EXPECT_LE(t, now + TIME_TOL);
    EXPECT_LT(t, previous); // backward in library time within one traversal
    previous = t;
  }
  // One full traversal takes (now - past) / speed = 3 s, then repeats.
  EXPECT_NEAR(tess::gravityPulseTime(3.0f + 1.5f, speed, now, past), 7.0f, TIME_TOL);
}

tess::SegmentKind kindOf(const tess::SegmentInstance &seg) {
  return static_cast<tess::SegmentKind>(static_cast<int>(seg.meta.z));
}

// Points on a tesseract edge keep three coordinates at +-1.
void expectOnTesseractEdge(const tess::SegmentInstance &seg) {
  const glm::vec4 mid = (seg.a + seg.b) * 0.5f;
  const auto unitCoords = std::ranges::count_if(
      components(mid), [](float c) { return std::abs(std::abs(c) - 1.0f) < UNIT_TOL; });
  EXPECT_EQ(unitCoords, 3);
}

// A world-tube segment is parallel to w, runs forward in library time, and
// stays inside the tesseract's w extent.
void expectWorldTubeSegment(const tess::SegmentInstance &seg) {
  EXPECT_EQ(glm::vec3(seg.a), glm::vec3(seg.b));
  EXPECT_LT(seg.meta.x, seg.meta.y);
  EXPECT_GE(seg.a.w, -1.0f - UNIT_TOL);
  EXPECT_LE(seg.b.w, 1.0f + UNIT_TOL);
}

TEST(SceneSegments, LayoutCountsAndTags) {
  tess::SceneSegmentOptions options;
  options.timeSpan = 10.0f;
  options.tubeSamples = 20;
  options.edgeSubdivisions = 4;
  const std::vector<tess::SegmentInstance> segments = tess::buildSceneSegments(options);
  const std::size_t strands = tess::bedroomFeatures().size();
  const std::size_t outline = tess::bedroomOutline().size();
  const std::size_t edgePieces = std::size_t{32} * options.edgeSubdivisions;
  const std::size_t tubePieces = strands * (options.tubeSamples - 1);
  EXPECT_EQ(strands, 13U);
  EXPECT_EQ(outline, 12U);
  EXPECT_EQ(segments.size(), edgePieces + tubePieces + outline);
  static_assert(sizeof(tess::SegmentInstance) == 12 * sizeof(float));

  std::array<std::size_t, 3> kindCounts{};
  for (const tess::SegmentInstance &seg : segments) {
    const tess::SegmentKind kind = kindOf(seg);
    kindCounts.at(static_cast<std::size_t>(kind)) += 1;
    if (kind == tess::SegmentKind::TesseractEdge) {
      expectOnTesseractEdge(seg);
    } else if (kind == tess::SegmentKind::WorldTube) {
      expectWorldTubeSegment(seg);
    }
  }
  EXPECT_EQ(kindCounts.at(0), edgePieces);
  EXPECT_EQ(kindCounts.at(1), tubePieces);
  EXPECT_EQ(kindCounts.at(2), outline);
}

TEST(So4Upload, ColumnMajorCopyMatchesGlmMatrixVectorProduct) {
  const auto qL = tess::normalized(tess::Quat<double>{.w = 0.3, .x = -0.7, .y = 0.2, .z = 0.6});
  const auto qR = tess::normalized(tess::Quat<double>{.w = 0.6, .x = 0.6, .y = 0.1, .z = -0.5});
  const tess::Mat4<double> m = tess::so4FromPair(qL, qR);
  const std::array<float, 16> packed = tess::toColumnMajor(m);
  const glm::mat4 uploaded = glm::make_mat4(packed.data());
  const tess::Vec4<double> v = {0.25, -1.0, 0.5, 0.75};
  const tess::Vec4<double> expected = tess::applyMatrix(m, v);
  const glm::vec4 actual = uploaded * glm::vec4(0.25f, -1.0f, 0.5f, 0.75f);
  const std::array<float, 4> actualComponents = components(actual);
  for (std::size_t k = 0; k < 4; ++k) {
    EXPECT_NEAR(actualComponents.at(k), static_cast<float>(expected.at(k)), UNIT_TOL);
  }
}

} // namespace
