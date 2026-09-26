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

TEST(TesseractProjection, PerspectiveClampsAtAndBehindTheEye) {
  const float d = 3.0f;
  // d - w = 0 and d - w < 0 both divide by PERSPECTIVE_MIN_DEPTH.
  const glm::vec3 atEye = tess::projectPerspective(glm::vec4(1.0f, 0.0f, 0.0f, d), d);
  const glm::vec3 behind = tess::projectPerspective(glm::vec4(1.0f, 0.0f, 0.0f, d + 2.0f), d);
  const float clamped = d / tess::PERSPECTIVE_MIN_DEPTH;
  EXPECT_NEAR(atEye.x, clamped, clamped * UNIT_TOL);
  EXPECT_NEAR(behind.x, clamped, clamped * UNIT_TOL);
  EXPECT_TRUE(std::isfinite(atEye.x));
}

TEST(TesseractProjection, StereographicPolesEquatorAndRadius) {
  const tess::StereographicPoint south =
      tess::projectStereographic(glm::vec4(0.0f, 0.0f, 0.0f, -1.0f));
  EXPECT_NEAR(glm::length(south.position), 0.0f, UNIT_TOL);
  EXPECT_FLOAT_EQ(south.fade, 1.0f);
  const tess::StereographicPoint equator =
      tess::projectStereographic(glm::vec4(0.0f, 1.0f, 0.0f, 0.0f));
  EXPECT_NEAR(glm::distance(equator.position, glm::vec3(0.0f, 1.0f, 0.0f)), 0.0f, UNIT_TOL);
  // |p|^2 = (1 + w) / (1 - w) for any point of S^3 away from the clamp.
  const glm::vec4 q = glm::normalize(glm::vec4(0.3f, -0.5f, 0.2f, 0.4f));
  const glm::vec3 p = tess::projectStereographic(q).position;
  EXPECT_NEAR(glm::dot(p, p), (1.0f + q.w) / (1.0f - q.w), UNIT_TOL);
  // Direction of xyz is preserved.
  EXPECT_NEAR(glm::dot(glm::normalize(p), glm::normalize(glm::vec3(q))), 1.0f, UNIT_TOL);
}

TEST(TesseractProjection, StereographicNormalizesOntoTheSphere) {
  const glm::vec4 onSphere = glm::normalize(glm::vec4(0.3f, -0.5f, 0.2f, 0.4f));
  const tess::StereographicPoint unit = tess::projectStereographic(onSphere);
  const tess::StereographicPoint scaled = tess::projectStereographic(onSphere * 2.0f);
  EXPECT_NEAR(glm::distance(unit.position, scaled.position), 0.0f, UNIT_TOL);
  EXPECT_FLOAT_EQ(unit.fade, scaled.fade);
  // A vanishing point goes to the south pole, the origin of the image.
  const tess::StereographicPoint zero = tess::projectStereographic(glm::vec4(0.0f));
  EXPECT_EQ(zero.position, glm::vec3(0.0f));
  EXPECT_FLOAT_EQ(zero.fade, 1.0f);
}

TEST(TesseractProjection, StereographicGuardsThePole) {
  // At the pole 1 - w = 0: finite image, divided by the clamp, fully faded.
  const tess::StereographicPoint pole =
      tess::projectStereographic(glm::vec4(0.0f, 0.0f, 0.0f, 1.0f));
  EXPECT_TRUE(std::isfinite(pole.position.x));
  EXPECT_EQ(pole.position, glm::vec3(0.0f));
  EXPECT_FLOAT_EQ(pole.fade, 0.0f);
  // Just off the pole the divisor stays at STEREOGRAPHIC_MIN_DENOM.
  const glm::vec4 nearPole = glm::normalize(glm::vec4(0.01f, 0.0f, 0.0f, 1.0f));
  const tess::StereographicPoint near = tess::projectStereographic(nearPole);
  EXPECT_NEAR(near.position.x, nearPole.x / tess::STEREOGRAPHIC_MIN_DENOM, 1e-4f);
  EXPECT_FLOAT_EQ(near.fade, 0.0f);
  // The fade is a smoothstep between the clamp and STEREOGRAPHIC_FADE_END.
  const float midDenom = 0.5f * (tess::STEREOGRAPHIC_MIN_DENOM + tess::STEREOGRAPHIC_FADE_END);
  const float w = 1.0f - midDenom;
  const glm::vec4 mid(std::sqrt(1.0f - (w * w)), 0.0f, 0.0f, w);
  EXPECT_NEAR(tess::projectStereographic(mid).fade, 0.5f, 1e-4f);
  const float wFull = 1.0f - tess::STEREOGRAPHIC_FADE_END;
  const glm::vec4 full(std::sqrt(1.0f - (wFull * wFull)), 0.0f, 0.0f, wFull);
  // 1 - (1 - FADE_END) rounds to within an ulp of FADE_END, so the fade sits
  // at the top of the smoothstep to about 1e-6.
  EXPECT_NEAR(tess::projectStereographic(full).fade, 1.0f, 1e-5f);
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
  EXPECT_FLOAT_EQ(tube.back().w, span); // T * (k / last) at k = last, within 4 ulps
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
  // A zero width divides by EMISSION_MIN_WIDTH: 1 at the moment, 0 elsewhere.
  EXPECT_FLOAT_EQ(tess::litMomentEmission(6.0f, 6.0f, 0.0f), 1.0f);
  EXPECT_EQ(tess::litMomentEmission(6.5f, 6.0f, 0.0f), 0.0f);
}

TEST(LibraryOfTime, GravityPulseRunsFromNowToPast) {
  const float now = 10.0f;
  const float past = 4.0f;
  const float span = now - past;
  const float speed = 2.0f;
  const float dt = 0.1f;
  // 15 frames of 0.1 s at 2 units/s put the pulse 3 units back, at t = 7.
  float travel = 0.0f;
  float previous = now + 1.0f;
  for (int frame = 0; frame < 15; ++frame) {
    travel = tess::advancePulseTravel(travel, speed * dt, span);
    const float t = now - travel;
    EXPECT_GT(t, past - TIME_TOL);
    EXPECT_LE(t, now + TIME_TOL);
    EXPECT_LT(t, previous); // backward in library time within one traversal
    previous = t;
  }
  EXPECT_NEAR(now - travel, 7.0f, TIME_TOL);
  // The pulse wraps from t_past back to t_now.
  EXPECT_NEAR(tess::advancePulseTravel(5.5f, 1.0f, span), 0.5f, TIME_TOL);
  // Shrinking the span re-wraps without a step; a degenerate span parks it.
  EXPECT_NEAR(tess::advancePulseTravel(5.0f, 0.0f, 2.0f), 1.0f, TIME_TOL);
  EXPECT_EQ(tess::advancePulseTravel(3.0f, 1.0f, 0.0f), 0.0f);
}

TEST(LibraryOfTime, PulseSpeedChangeAffectsOnlyLaterMotion) {
  // Ten minutes of frames at 60 Hz, then a speed change: the next frame moves
  // the pulse by the new speed times one frame, never by speed * elapsed.
  const float span = 6.0f;
  const float dt = 1.0f / 60.0f;
  float travel = 0.0f;
  for (int frame = 0; frame < 36000; ++frame) {
    travel = tess::advancePulseTravel(travel, 1.5f * dt, span);
  }
  const float next = tess::advancePulseTravel(travel, 9.0f * dt, span);
  const float moved = std::fmod(next - travel + span, span);
  EXPECT_NEAR(moved, 9.0f * dt, 1e-4f);
}

double quatDistance(const tess::Quat<double> &a, const tess::Quat<double> &b) {
  const double direct =
      std::abs(a.w - b.w) + std::abs(a.x - b.x) + std::abs(a.y - b.y) + std::abs(a.z - b.z);
  const double flipped =
      std::abs(a.w + b.w) + std::abs(a.x + b.x) + std::abs(a.y + b.y) + std::abs(a.z + b.z);
  return std::min(direct, flipped);
}

TEST(TesseractAnimation, AccumulatedStepsMatchClosedFormForConstantRates) {
  const std::array<float, 3> left = {0.35f, 0.0f, 0.15f};
  const std::array<float, 3> right = {-0.35f, 0.12f, 0.0f};
  tess::So4Pair<double> orientation{};
  const double ds = 1.0 / 60.0;
  const int steps = 600;
  for (int k = 0; k < steps; ++k) {
    orientation = tess::advanceOrientation(orientation, left, right, ds);
  }
  const double s = ds * steps;
  const auto closed = [s](const std::array<float, 3> &r) {
    return tess::quatExp(s * static_cast<double>(r.at(0)), s * static_cast<double>(r.at(1)),
                         s * static_cast<double>(r.at(2)));
  };
  EXPECT_LT(quatDistance(orientation.left, closed(left)), 1e-12);
  EXPECT_LT(quatDistance(orientation.right, closed(right)), 1e-12);
}

TEST(TesseractAnimation, OutputClockMotionMatchesFrameAccumulation) {
  // A recording evaluates tesseractMotionAt at frameIndex / fps; accumulating
  // the same frames one by one from the reset state reaches the same state,
  // so a capture resumed at frame k reproduces frame k of the full capture.
  const std::array<float, 3> left = {0.35f, 0.0f, 0.15f};
  const std::array<float, 3> right = {-0.35f, 0.12f, 0.0f};
  const double resetPhase = 2.5;
  const double speed = 1.0;
  const float pulseSpeed = 1.5f;
  const float span = 4.0f;
  const double fps = 60.0;
  tess::TesseractMotion accumulated =
      tess::tesseractMotionAt(left, right, resetPhase, speed, pulseSpeed, span, 0.0);
  for (int frame = 1; frame <= 300; ++frame) {
    accumulated.orientation =
        tess::advanceOrientation(accumulated.orientation, left, right, speed / fps);
    accumulated.pulseTravel = tess::advancePulseTravel(
        accumulated.pulseTravel, static_cast<float>(static_cast<double>(pulseSpeed) / fps), span);
    const tess::TesseractMotion direct = tess::tesseractMotionAt(
        left, right, resetPhase, speed, pulseSpeed, span, static_cast<double>(frame) / fps);
    EXPECT_LT(quatDistance(direct.orientation.left, accumulated.orientation.left), 1e-12);
    EXPECT_LT(quatDistance(direct.orientation.right, accumulated.orientation.right), 1e-12);
    EXPECT_NEAR(direct.pulseTravel, accumulated.pulseTravel, 1e-4f);
  }
  // Time 0 is the reset state; the pulse starts at t_now.
  const tess::TesseractMotion reset =
      tess::tesseractMotionAt(left, right, resetPhase, speed, pulseSpeed, span, 0.0);
  EXPECT_EQ(reset.pulseTravel, 0.0f);
}

TEST(TesseractAnimation, RateChangeAfterLongRunMovesOnlyOneStep) {
  // Ten minutes at 60 Hz, then the rate sliders jump: one more frame turns
  // the orientation by at most |rate| * ds, not by |rate change| * s.
  const std::array<float, 3> left = {0.35f, 0.0f, 0.15f};
  const std::array<float, 3> right = {-0.35f, 0.12f, 0.0f};
  const double ds = 1.0 / 60.0;
  tess::So4Pair<double> orientation{};
  for (int k = 0; k < 36000; ++k) {
    orientation = tess::advanceOrientation(orientation, left, right, ds);
  }
  const std::array<float, 3> newLeft = {-0.9f, 0.4f, 0.0f};
  const std::array<float, 3> newRight = {0.0f, 0.0f, 0.8f};
  const tess::So4Pair<double> next = tess::advanceOrientation(orientation, newLeft, newRight, ds);
  // |exp(ds v) q - q| <= 2 sin(|v| ds / 2) <= |v| ds per component group.
  EXPECT_LT(quatDistance(next.left, orientation.left), 4.0 * 1.0 * ds);
  EXPECT_LT(quatDistance(next.right, orientation.right), 4.0 * 1.0 * ds);
  // Animation off (ds = 0) holds the orientation: the step is the identity and
  // only renormalization of an already-unit quaternion touches the last bits.
  const tess::So4Pair<double> frozen =
      tess::advanceOrientation(orientation, newLeft, newRight, 0.0);
  EXPECT_LT(quatDistance(frozen.left, orientation.left), 1e-15);
  EXPECT_LT(quatDistance(frozen.right, orientation.right), 1e-15);
  // Unit norm survives the long accumulation.
  EXPECT_NEAR(tess::norm(orientation.left), 1.0, 1e-12);
  EXPECT_NEAR(tess::norm(orientation.right), 1.0, 1e-12);
}

tess::SegmentKind kindOf(const tess::SegmentInstance &seg) {
  return tess::segmentKind(seg);
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
  const std::size_t outlinePieces = outline * options.edgeSubdivisions;
  EXPECT_EQ(strands, 13U);
  EXPECT_EQ(outline, 12U);
  EXPECT_EQ(segments.size(), edgePieces + tubePieces + outlinePieces);
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
  EXPECT_EQ(kindCounts.at(2), outlinePieces);
}

// Every polyline caps its two true endpoints and nothing else: the 32 edges,
// one world tube per strand, and the room outline links.
TEST(SceneSegments, CapsOnlyPolylineEnds) {
  tess::SceneSegmentOptions options;
  options.tubeSamples = 20;
  options.edgeSubdivisions = 4;
  const std::vector<tess::SegmentInstance> segments = tess::buildSceneSegments(options);
  const std::size_t polylines =
      std::size_t{32} + tess::bedroomFeatures().size() + tess::bedroomOutline().size();
  const auto capsA = std::ranges::count_if(
      segments, [](const tess::SegmentInstance &s) { return tess::segmentCapped(s, false); });
  const auto capsB = std::ranges::count_if(
      segments, [](const tess::SegmentInstance &s) { return tess::segmentCapped(s, true); });
  EXPECT_EQ(static_cast<std::size_t>(capsA), polylines);
  EXPECT_EQ(static_cast<std::size_t>(capsB), polylines);
  // A capped a starts a polyline; the segment before it capped its b.
  for (std::size_t i = 1; i < segments.size(); ++i) {
    EXPECT_EQ(tess::segmentCapped(segments.at(i), false),
              tess::segmentCapped(segments.at(i - 1), true))
        << i;
  }
  EXPECT_TRUE(tess::segmentCapped(segments.front(), false));
  EXPECT_TRUE(tess::segmentCapped(segments.back(), true));
}

TEST(SceneSegments, TagRoundTripsKindAndCaps) {
  for (const auto kind : {tess::SegmentKind::TesseractEdge, tess::SegmentKind::WorldTube,
                          tess::SegmentKind::LitSlice}) {
    for (const bool capA : {false, true}) {
      for (const bool capB : {false, true}) {
        tess::SegmentInstance seg;
        seg.meta.z = tess::packSegmentTag(kind, capA, capB);
        EXPECT_EQ(tess::segmentKind(seg), kind);
        EXPECT_EQ(tess::segmentCapped(seg, false), capA);
        EXPECT_EQ(tess::segmentCapped(seg, true), capB);
      }
    }
  }
}

TEST(So4Upload, ColumnMajorCopyMatchesGlmMatrixVectorProduct) {
  const auto qL = tess::normalized(tess::Quat<double>{.w = 0.3, .x = -0.7, .y = 0.2, .z = 0.6});
  const auto qR = tess::normalized(tess::Quat<double>{.w = 0.6, .x = 0.6, .y = 0.1, .z = -0.5});
  const tess::Mat4<double> m = tess::so4FromPair(qL, qR);
  const std::array<float, 16> packed = tess::toColumnMajor(m);
  // Column by column, as GLSL reads the uniform: column c holds packed[4c..4c+3].
  // glm::make_mat4 memcpys through the first column's vec4 subobject, which
  // GCC -Warray-bounds=2 rejects.
  const auto column = [&packed](std::size_t c) {
    return glm::vec4(packed.at(4 * c), packed.at((4 * c) + 1), packed.at((4 * c) + 2),
                     packed.at((4 * c) + 3));
  };
  const glm::mat4 uploaded(column(0), column(1), column(2), column(3));
  const tess::Vec4<double> v = {0.25, -1.0, 0.5, 0.75};
  const tess::Vec4<double> expected = tess::applyMatrix(m, v);
  const glm::vec4 actual = uploaded * glm::vec4(0.25f, -1.0f, 0.5f, 0.75f);
  const std::array<float, 4> actualComponents = components(actual);
  for (std::size_t k = 0; k < 4; ++k) {
    EXPECT_NEAR(actualComponents.at(k), static_cast<float>(expected.at(k)), UNIT_TOL);
  }
}

} // namespace
