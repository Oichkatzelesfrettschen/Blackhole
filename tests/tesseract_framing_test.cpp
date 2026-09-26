/**
 * @file tesseract_framing_test.cpp
 * @brief The tesseract view follows the black-hole camera: record distance
 *        and field of view, and the showcase-orbit frame offset.
 *
 * tesseractFraming places a recorded frame's eye so the scene's bounding
 * sphere fills TESSERACT_RECORD_FILL of the room between its center and the
 * nearer frame edge at any record field of view, which passes through inside
 * glm::perspective's domain, centered or moved off center by a frame offset;
 * interactive frames keep the UI values. tesseractBoundingRadius must hold
 * every projected scene point under any SO(4) rotation. tesseractView places
 * the eye on the black-hole camera's focus line with that camera's aimed
 * orientation, so a frame offset puts the tesseract where the black hole sits
 * on screen.
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <optional>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <glm/common.hpp>
#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/scalar_constants.hpp>
#include <glm/ext/vector_float2.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/geometric.hpp>
#include <glm/gtc/matrix_access.hpp>
#include <glm/matrix.hpp>
#include <glm/trigonometric.hpp>

#include "render/camera_math.h"
#include "render/tesseract/so4.h"
#include "render/tesseract/tesseract_geometry.h"
#include "render/tesseract/tesseract_renderer.h"

namespace {

using blackhole::buildCameraBasis;
using blackhole::TESSERACT_MAX_FOV_DEG;
using blackhole::TESSERACT_MIN_FOV_DEG;
using blackhole::TESSERACT_MIN_VIEW_DISTANCE;
using blackhole::TESSERACT_NEAR_PLANE;
using blackhole::TESSERACT_RECORD_FILL;
using blackhole::tesseractFocusTangent;
using blackhole::TesseractFraming;
using blackhole::tesseractFraming;
using blackhole::TesseractRecordCamera;

constexpr float UI_DISTANCE = 8.0f;
constexpr float UI_FOV = 50.0f;

// Default scene: perspective along w at eye distance 3, scene scale 1.3.
constexpr float DEFAULT_SCENE_SCALE = 1.3f;
constexpr float DEFAULT_EYE_W = 3.0f;

float defaultRadius() {
  return blackhole::tesseractBoundingRadius(false, DEFAULT_SCENE_SCALE, DEFAULT_EYE_W);
}

// Landscape record target (the 1343 x 1056 capture) and a portrait one
// (BLACKHOLE_RECORD_WIDTH/HEIGHT 1080 x 1920).
constexpr float LANDSCAPE_ASPECT = 1343.0f / 1056.0f;
constexpr float PORTRAIT_ASPECT = 1080.0f / 1920.0f;

TesseractFraming recorded(float fovDeg, float aspect = LANDSCAPE_ASPECT) {
  return tesseractFraming(UI_DISTANCE, UI_FOV, defaultRadius(), aspect,
                          TesseractRecordCamera{.fovDeg = fovDeg});
}

// Silhouette of a centered sphere of radius r at distance d, in units of the
// narrower half-extent of a target of @p aspect with vertical fov @p fovDeg.
float sphereNarrowFill(float radius, float distance, float fovDeg, float aspect) {
  const float verticalTan = std::tan(glm::radians(fovDeg) * 0.5f);
  const float narrowTan = std::min(verticalTan, aspect * verticalTan);
  return std::tan(std::asin(radius / distance)) / narrowTan;
}

TEST(TesseractFraming, InteractiveFramesKeepTheUiValues) {
  const TesseractFraming framing =
      tesseractFraming(UI_DISTANCE, UI_FOV, defaultRadius(), LANDSCAPE_ASPECT, std::nullopt);
  EXPECT_FLOAT_EQ(framing.viewDistance, UI_DISTANCE);
  EXPECT_FLOAT_EQ(framing.fovDeg, UI_FOV);
}

// The showcase telephoto (20), the above-disk and centered compositions'
// lenses, and the old wide showcase lens (68) all show the bounding sphere at
// the same size.
TEST(TesseractFraming, EveryRecordFieldOfViewFillsTheSameFraction) {
  for (const float aspect : {LANDSCAPE_ASPECT, PORTRAIT_ASPECT, 1.0f, 21.0f / 9.0f}) {
    for (const float fov : {20.0f, 32.2042f, 37.2738f, 45.0f, 68.0f, 90.0f}) {
      const TesseractFraming framing = recorded(fov, aspect);
      EXPECT_NEAR(sphereNarrowFill(defaultRadius(), framing.viewDistance, framing.fovDeg, aspect),
                  TESSERACT_RECORD_FILL, 1e-4f)
          << fov << " aspect " << aspect;
    }
  }
  // A portrait target, narrower across, backs the eye away.
  EXPECT_GT(recorded(37.2738f, PORTRAIT_ASPECT).viewDistance,
            recorded(37.2738f, LANDSCAPE_ASPECT).viewDistance);
  // A narrower lens backs the eye away rather than cropping.
  EXPECT_GT(recorded(20.0f).viewDistance, recorded(68.0f).viewDistance);
}

TEST(TesseractFraming, BoundingRadiusFollowsTheProjection) {
  // 2 d / sqrt(d^2 - 4) at the default eye distance 3, times the scale.
  EXPECT_FLOAT_EQ(defaultRadius(), DEFAULT_SCENE_SCALE * 6.0f / std::sqrt(5.0f));
  // Eye distances below the clamp use the clamp.
  EXPECT_FLOAT_EQ(blackhole::tesseractBoundingRadius(false, 1.0f, 1.0f),
                  blackhole::tesseractBoundingRadius(
                      false, 1.0f, blackhole::TESSERACT_MIN_PERSPECTIVE_DISTANCE));
  // The fully lit stereographic image reaches radius 3.
  EXPECT_FLOAT_EQ(blackhole::tesseractBoundingRadius(true, 2.0f, 3.0f), 6.0f);
}

TEST(TesseractFraming, RecordFieldOfViewPassesThroughInsideThePerspectiveDomain) {
  EXPECT_FLOAT_EQ(recorded(68.0f).fovDeg, 68.0f);
  // Wider than the UI slider still passes: --record-fov 120 frames at 120.
  EXPECT_FLOAT_EQ(recorded(120.0f).fovDeg, 120.0f);
  EXPECT_FLOAT_EQ(recorded(200.0f).fovDeg, TESSERACT_MAX_FOV_DEG);
  EXPECT_FLOAT_EQ(recorded(0.0f).fovDeg, TESSERACT_MIN_FOV_DEG);
}

// A showcase-orbit black-hole camera as updateFrameCamera builds it: the eye
// orbits the focus at the origin and turns toward an aim point offset by
// (frameX, frameY) half-extents of the frame.
struct OffsetCamera {
  glm::mat3 basis{1.0f};
  glm::vec3 focusDirection{0.0f};
  glm::vec2 focusNdc{0.0f};
};

constexpr float OFFSET_FOV = 68.0f;
constexpr float OFFSET_ASPECT = 16.0f / 9.0f;

OffsetCamera offsetCamera(float frameX, float frameY, float fovDeg = OFFSET_FOV,
                          float aspect = OFFSET_ASPECT) {
  const glm::vec3 focus(0.0f);
  const glm::vec3 cameraPos = glm::vec3(0.35f, -0.24f, -0.9f) * 14.0f;
  const float distance = glm::length(cameraPos - focus);
  const glm::mat3 baseBasis = buildCameraBasis(cameraPos, focus, 0.0f);
  const float halfHeight = std::tan(glm::radians(fovDeg) * 0.5f) * distance;
  const float halfWidth = halfHeight * aspect;
  const glm::vec3 aim =
      focus + (baseBasis[0] * (frameX * halfWidth)) + (baseBasis[1] * (frameY * halfHeight));
  OffsetCamera out;
  out.basis = buildCameraBasis(cameraPos, aim, 0.0f);
  out.focusDirection = glm::normalize(focus - cameraPos);
  const glm::mat4 projection = glm::perspective(glm::radians(fovDeg), aspect, 0.1f, 100.0f);
  const glm::mat4 view = glm::lookAt(cameraPos, aim, out.basis[1]);
  const glm::vec4 clip = projection * view * glm::vec4(focus, 1.0f);
  out.focusNdc = glm::vec2(clip) / clip.w;
  return out;
}

glm::vec2 originNdc(const glm::mat4 &viewProjection) {
  const glm::vec4 clip = viewProjection * glm::vec4(0.0f, 0.0f, 0.0f, 1.0f);
  return glm::vec2(clip) / clip.w;
}

TEST(TesseractFraming, UnshiftedCameraLooksAtTheOrigin) {
  const OffsetCamera cam = offsetCamera(0.0f, 0.0f);
  const glm::mat4 vp = blackhole::tesseractViewProjection(cam.basis, cam.focusDirection,
                                                          UI_DISTANCE, OFFSET_FOV, OFFSET_ASPECT);
  const glm::vec2 ndc = originNdc(vp);
  EXPECT_NEAR(ndc.x, 0.0f, 1e-5f);
  EXPECT_NEAR(ndc.y, 0.0f, 1e-5f);
}

TEST(TesseractFraming, FrameOffsetPlacesTheTesseractWhereTheBlackHoleSits) {
  for (const auto &[frameX, frameY] :
       {std::pair{0.2f, 0.0f}, std::pair{-0.18f, 0.12f}, std::pair{0.0f, -0.25f}}) {
    const OffsetCamera cam = offsetCamera(frameX, frameY);
    // The black-hole path turns the camera by the offset, so the focus lands
    // off center, horizontally near -frameX when frameY is 0 (the world-up
    // basis rebuild tilts it slightly off the pitched camera's axis).
    if (frameY == 0.0f) {
      EXPECT_NEAR(cam.focusNdc.x, -frameX, 2e-3f);
    }
    const glm::mat4 vp = blackhole::tesseractViewProjection(cam.basis, cam.focusDirection,
                                                            UI_DISTANCE, OFFSET_FOV, OFFSET_ASPECT);
    const glm::vec2 ndc = originNdc(vp);
    EXPECT_NEAR(ndc.x, cam.focusNdc.x, 1e-4f) << frameX << "," << frameY;
    EXPECT_NEAR(ndc.y, cam.focusNdc.y, 1e-4f) << frameX << "," << frameY;
  }
}

TEST(TesseractFraming, FrameOffsetKeepsTheBlackHoleViewingDirection) {
  // The tesseract is seen from where the black-hole camera sees its focus,
  // not along the aimed forward axis.
  const OffsetCamera cam = offsetCamera(0.2f, 0.1f);
  const glm::mat4 view = blackhole::tesseractView(cam.basis, cam.focusDirection, UI_DISTANCE);
  const glm::vec3 eye = glm::vec3(glm::inverse(view)[3]);
  const glm::vec3 fromFocus = glm::normalize(eye);
  EXPECT_NEAR(glm::dot(fromFocus, -cam.focusDirection), 1.0f, 1e-5f);
  EXPECT_NEAR(glm::length(eye), UI_DISTANCE, 1e-3f);
  // The orientation stays the black-hole camera's aimed basis.
  EXPECT_NEAR(glm::dot(-glm::vec3(glm::row(view, 2)), cam.basis[2]), 1.0f, 1e-5f);
}

// Unit quaternion from a deterministic sequence of angles.
blackhole::tesseract::Quat<double> sampleQuat(int i, double phase) {
  const double a = (0.37 * i) + phase;
  const double b = (0.91 * i) + (2.0 * phase);
  const double c = (1.73 * i) + (3.0 * phase);
  const blackhole::tesseract::Quat<double> q{.w = std::cos(a) * std::cos(b),
                                             .x = std::sin(a) * std::cos(c),
                                             .y = std::cos(a) * std::sin(b),
                                             .z = std::sin(a) * std::sin(c)};
  const double n = std::sqrt((q.w * q.w) + (q.x * q.x) + (q.y * q.y) + (q.z * q.z));
  return {.w = q.w / n, .x = q.x / n, .y = q.y / n, .z = q.z / n};
}

// Largest clip-space z / w over every scene endpoint in front of the eye,
// under many SO(4) rotations, at the slider extremes that put geometry
// farthest from the eye: scene scale 3, view distance 3, eye w distance 2.1.
constexpr float EXTREME_SCENE_SCALE = 3.0f;
constexpr float EXTREME_EYE_W = 2.1f;

float deepestClipDepth(const glm::mat4 &viewProjection, bool stereographic) {
  const std::vector<blackhole::tesseract::SegmentInstance> segments =
      blackhole::tesseract::buildSceneSegments({});
  float deepest = -1.0f;
  for (int i = 0; i < 64; ++i) {
    const auto rotation = blackhole::tesseract::so4FromPair(sampleQuat(i, 0.1), sampleQuat(i, 0.7));
    for (const auto &seg : segments) {
      for (const glm::vec4 &p : {seg.a, seg.b}) {
        const blackhole::tesseract::Vec4<double> r = blackhole::tesseract::applyMatrix(
            rotation,
            blackhole::tesseract::Vec4<double>{static_cast<double>(p.x), static_cast<double>(p.y),
                                               static_cast<double>(p.z), static_cast<double>(p.w)});
        const glm::vec4 rotated(static_cast<float>(r[0]), static_cast<float>(r[1]),
                                static_cast<float>(r[2]), static_cast<float>(r[3]));
        const glm::vec3 projected =
            stereographic ? blackhole::tesseract::projectStereographic(rotated).position
                          : blackhole::tesseract::projectPerspective(rotated, EXTREME_EYE_W);
        const glm::vec4 clip = viewProjection * glm::vec4(projected * EXTREME_SCENE_SCALE, 1.0f);
        if (clip.w > TESSERACT_NEAR_PLANE) {
          deepest = std::max(deepest, clip.z / clip.w);
        }
      }
    }
  }
  return deepest;
}

TEST(TesseractFraming, FarPlaneKeepsEveryProjectedPoint) {
  const OffsetCamera cam = offsetCamera(0.0f, 0.0f);
  const glm::mat4 vp = blackhole::tesseractViewProjection(
      cam.basis, cam.focusDirection, TESSERACT_MIN_VIEW_DISTANCE, OFFSET_FOV, OFFSET_ASPECT);
  // A far plane at four view distances (12) clipped both modes here.
  const glm::mat4 finiteFar =
      glm::perspective(glm::radians(OFFSET_FOV), OFFSET_ASPECT, TESSERACT_NEAR_PLANE,
                       TESSERACT_MIN_VIEW_DISTANCE * 4.0f) *
      blackhole::tesseractView(cam.basis, cam.focusDirection, TESSERACT_MIN_VIEW_DISTANCE);
  for (const bool stereographic : {false, true}) {
    EXPECT_LT(deepestClipDepth(vp, stereographic), 1.0f) << "stereographic " << stereographic;
    EXPECT_GT(deepestClipDepth(finiteFar, stereographic), 1.0f)
        << "stereographic " << stereographic;
  }
}

// Largest |NDC| on each axis over every scene endpoint under 64 SO(4)
// rotations seen through @p viewProjection. Stereographic points still
// fading toward the pole are skipped: the bound covers the lit image.
glm::vec2 largestSceneNdc(const glm::mat4 &viewProjection, bool stereographic, float sceneScale,
                          float eyeW) {
  const std::vector<blackhole::tesseract::SegmentInstance> segments =
      blackhole::tesseract::buildSceneSegments({});
  glm::vec2 largest{0.0f};
  for (int i = 0; i < 64; ++i) {
    const auto rotation = blackhole::tesseract::so4FromPair(sampleQuat(i, 0.3), sampleQuat(i, 1.1));
    for (const auto &seg : segments) {
      for (const glm::vec4 &p : {seg.a, seg.b}) {
        const blackhole::tesseract::Vec4<double> r = blackhole::tesseract::applyMatrix(
            rotation,
            blackhole::tesseract::Vec4<double>{static_cast<double>(p.x), static_cast<double>(p.y),
                                               static_cast<double>(p.z), static_cast<double>(p.w)});
        const glm::vec4 rotated(static_cast<float>(r[0]), static_cast<float>(r[1]),
                                static_cast<float>(r[2]), static_cast<float>(r[3]));
        glm::vec3 projected{0.0f};
        if (stereographic) {
          const blackhole::tesseract::StereographicPoint point =
              blackhole::tesseract::projectStereographic(rotated);
          if (point.fade < 1.0f) {
            continue;
          }
          projected = point.position;
        } else {
          projected = blackhole::tesseract::projectPerspective(rotated, eyeW);
        }
        const glm::vec4 clip = viewProjection * glm::vec4(projected * sceneScale, 1.0f);
        largest = glm::max(largest, glm::abs(glm::vec2(clip) / clip.w));
      }
    }
  }
  return largest;
}

// Largest extent of the scene framed by a centered record camera at
// @p fovDeg on a target of @p aspect, with each axis in units of the
// narrower half-extent.
float largestRecordedExtent(bool stereographic, float sceneScale, float eyeW, float fovDeg,
                            float aspect) {
  const float radius = blackhole::tesseractBoundingRadius(stereographic, sceneScale, eyeW);
  const TesseractFraming framing = tesseractFraming(UI_DISTANCE, UI_FOV, radius, aspect,
                                                    TesseractRecordCamera{.fovDeg = fovDeg});
  const OffsetCamera cam = offsetCamera(0.0f, 0.0f);
  const glm::mat4 vp = blackhole::tesseractViewProjection(
      cam.basis, cam.focusDirection, framing.viewDistance, framing.fovDeg, aspect);
  // NDC to narrower-half-extent units: the vertical axis scales by
  // tan(fov/2) / narrow, the horizontal one by aspect tan(fov/2) / narrow.
  const float yUnits = 1.0f / std::min(1.0f, aspect);
  const float xUnits = aspect * yUnits;
  const glm::vec2 ndc = largestSceneNdc(vp, stereographic, sceneScale, eyeW);
  return std::max(ndc.x * xUnits, ndc.y * yUnits);
}

// The bounding radius holds the rotating scene: at the default and extreme
// settings, in both projections, no recorded point leaves the fill fraction.
TEST(TesseractFraming, RecordedSceneStaysInsideTheFill) {
  for (const float aspect : {LANDSCAPE_ASPECT, PORTRAIT_ASPECT}) {
    for (const float fov : {20.0f, 37.2738f, 68.0f}) {
      EXPECT_LE(largestRecordedExtent(false, DEFAULT_SCENE_SCALE, DEFAULT_EYE_W, fov, aspect),
                TESSERACT_RECORD_FILL)
          << fov << " aspect " << aspect;
      EXPECT_LE(largestRecordedExtent(false, EXTREME_SCENE_SCALE, EXTREME_EYE_W, fov, aspect),
                TESSERACT_RECORD_FILL)
          << fov << " aspect " << aspect;
      EXPECT_LE(largestRecordedExtent(true, DEFAULT_SCENE_SCALE, DEFAULT_EYE_W, fov, aspect),
                TESSERACT_RECORD_FILL)
          << fov << " aspect " << aspect;
    }
    // The default scene fills most of the fraction, so the bound is not loose.
    EXPECT_GT(largestRecordedExtent(false, DEFAULT_SCENE_SCALE, DEFAULT_EYE_W, 37.2738f, aspect),
              0.5f * TESSERACT_RECORD_FILL);
  }
}

// The showcase-orbit compositions' offsets: left-third, wide-right, and one
// with both axes large.
constexpr std::array<std::pair<float, float>, 3> COMPOSITION_OFFSETS = {
    {{0.36f, 0.06f}, {-0.24f, -0.04f}, {0.3f, -0.3f}}};
constexpr float LEFT_THIRD_FOV = 30.9819f;

// Largest |NDC| on each axis over the surface of a sphere of @p radius about
// the origin: 360 x 720 samples resolve the silhouette to about 1e-4.
glm::vec2 largestSphereNdc(const glm::mat4 &viewProjection, float radius) {
  constexpr int polarSamples = 360;
  constexpr int azimuthSamples = 720;
  glm::vec2 largest{0.0f};
  for (int i = 0; i <= polarSamples; ++i) {
    const float theta = glm::pi<float>() * static_cast<float>(i) / static_cast<float>(polarSamples);
    for (int j = 0; j < azimuthSamples; ++j) {
      const float phi =
          2.0f * glm::pi<float>() * static_cast<float>(j) / static_cast<float>(azimuthSamples);
      const glm::vec3 point = radius * glm::vec3(std::sin(theta) * std::cos(phi),
                                                 std::sin(theta) * std::sin(phi), std::cos(theta));
      const glm::vec4 clip = viewProjection * glm::vec4(point, 1.0f);
      largest = glm::max(largest, glm::abs(glm::vec2(clip) / clip.w));
    }
  }
  return largest;
}

// The outer edge the fill allows on each axis, in NDC, for a center at
// @p centerNdc: |c| + k (1 - |c|).
glm::vec2 fillEdgeNdc(const glm::vec2 &centerNdc) {
  const glm::vec2 c = glm::abs(centerNdc);
  return c + (TESSERACT_RECORD_FILL * (glm::vec2(1.0f) - c));
}

TesseractFraming offsetRecorded(const OffsetCamera &cam, float fovDeg, float aspect, float radius) {
  return tesseractFraming(
      UI_DISTANCE, UI_FOV, radius, aspect,
      TesseractRecordCamera{.fovDeg = fovDeg,
                            .focusTangent = tesseractFocusTangent(cam.basis, cam.focusDirection)});
}

TEST(TesseractFraming, FocusTangentPlacesTheCenterWhereTheBlackHoleSits) {
  const OffsetCamera centered = offsetCamera(0.0f, 0.0f);
  const glm::vec2 zero = tesseractFocusTangent(centered.basis, centered.focusDirection);
  EXPECT_NEAR(zero.x, 0.0f, 1e-5f);
  EXPECT_NEAR(zero.y, 0.0f, 1e-5f);
  for (const auto &[frameX, frameY] : COMPOSITION_OFFSETS) {
    const OffsetCamera cam = offsetCamera(frameX, frameY);
    const float verticalTan = std::tan(glm::radians(OFFSET_FOV) * 0.5f);
    const glm::vec2 tangent = tesseractFocusTangent(cam.basis, cam.focusDirection);
    EXPECT_NEAR(std::abs(tangent.x) / (OFFSET_ASPECT * verticalTan), std::abs(cam.focusNdc.x),
                1e-4f)
        << frameX << "," << frameY;
    EXPECT_NEAR(std::abs(tangent.y) / verticalTan, std::abs(cam.focusNdc.y), 1e-4f)
        << frameX << "," << frameY;
  }
}

// Off center, the bounding sphere reaches exactly the fill edge on its
// tighter axis and stays inside it on the other, at telephoto and wide lenses
// on landscape and portrait targets.
TEST(TesseractFraming, OffsetRecordFrameFitsTheSphereInsideTheRemainingRoom) {
  const float radius = defaultRadius();
  for (const float aspect : {LANDSCAPE_ASPECT, PORTRAIT_ASPECT}) {
    for (const float fov : {20.0f, LEFT_THIRD_FOV, 90.0f, 120.0f}) {
      for (const auto &[frameX, frameY] : COMPOSITION_OFFSETS) {
        const OffsetCamera cam = offsetCamera(frameX, frameY, fov, aspect);
        const TesseractFraming framing = offsetRecorded(cam, fov, aspect, radius);
        const glm::mat4 vp = blackhole::tesseractViewProjection(
            cam.basis, cam.focusDirection, framing.viewDistance, framing.fovDeg, aspect);
        const glm::vec2 edge = fillEdgeNdc(originNdc(vp));
        const glm::vec2 reach = largestSphereNdc(vp, radius);
        EXPECT_LE(reach.x, edge.x + 1e-3f) << fov << " " << aspect << " " << frameX;
        EXPECT_LE(reach.y, edge.y + 1e-3f) << fov << " " << aspect << " " << frameY;
        EXPECT_NEAR(std::max(reach.x - edge.x, reach.y - edge.y), 0.0f, 1e-3f)
            << fov << " " << aspect << " " << frameX << "," << frameY;
      }
    }
  }
}

// The portrait left-third capture: the framing that ignores the offset
// pushes the sphere past the frame edge, and the offset-aware framing keeps
// the sphere and every rotated scene point inside the fill.
TEST(TesseractFraming, PortraitLeftThirdKeepsTheTesseractInFrame) {
  const float radius = defaultRadius();
  const OffsetCamera cam = offsetCamera(0.36f, 0.06f, LEFT_THIRD_FOV, PORTRAIT_ASPECT);
  const TesseractFraming centered =
      tesseractFraming(UI_DISTANCE, UI_FOV, radius, PORTRAIT_ASPECT,
                       TesseractRecordCamera{.fovDeg = LEFT_THIRD_FOV});
  const glm::mat4 centeredVp = blackhole::tesseractViewProjection(
      cam.basis, cam.focusDirection, centered.viewDistance, centered.fovDeg, PORTRAIT_ASPECT);
  EXPECT_GT(largestSphereNdc(centeredVp, radius).x, 1.0f);

  const TesseractFraming framing = offsetRecorded(cam, LEFT_THIRD_FOV, PORTRAIT_ASPECT, radius);
  EXPECT_GT(framing.viewDistance, centered.viewDistance);
  const glm::mat4 vp = blackhole::tesseractViewProjection(
      cam.basis, cam.focusDirection, framing.viewDistance, framing.fovDeg, PORTRAIT_ASPECT);
  const glm::vec2 edge = fillEdgeNdc(originNdc(vp));
  const glm::vec2 scene = largestSceneNdc(vp, false, DEFAULT_SCENE_SCALE, DEFAULT_EYE_W);
  EXPECT_LE(scene.x, edge.x);
  EXPECT_LE(scene.y, edge.y);
}

} // namespace
