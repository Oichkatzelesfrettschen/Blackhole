/**
 * @file tesseract_framing_test.cpp
 * @brief The tesseract view follows the black-hole camera: record distance
 *        and field of view, and the showcase-orbit frame offset.
 *
 * tesseractFraming maps the black-hole record camera distance d to the
 * tesseract view distance viewDistance * d / TESSERACT_RECORD_REFERENCE_DISTANCE
 * with a TESSERACT_MIN_VIEW_DISTANCE floor, and passes the field of view
 * through inside glm::perspective's domain; interactive frames keep the UI
 * values. tesseractView places the eye on the black-hole camera's focus line
 * with that camera's aimed orientation, so a frame offset puts the tesseract
 * where the black hole sits on screen.
 */

#include <algorithm>
#include <cmath>
#include <optional>
#include <utility>
#include <vector>

#include <gtest/gtest.h>

#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/vector_float2.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/geometric.hpp>
#include <glm/gtc/matrix_access.hpp>
#include <glm/matrix.hpp>
#include <glm/trigonometric.hpp>

#include "input.h"
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
using blackhole::TESSERACT_RECORD_REFERENCE_DISTANCE;
using blackhole::TesseractFraming;
using blackhole::tesseractFraming;
using blackhole::TesseractRecordCamera;

constexpr float UI_DISTANCE = 8.0f;
constexpr float UI_FOV = 50.0f;

TesseractFraming recorded(float distance, float fovDeg) {
  return tesseractFraming(UI_DISTANCE, UI_FOV,
                          TesseractRecordCamera{.distance = distance, .fovDeg = fovDeg});
}

TEST(TesseractFraming, InteractiveFramesKeepTheUiValues) {
  const TesseractFraming framing = tesseractFraming(UI_DISTANCE, UI_FOV, std::nullopt);
  EXPECT_FLOAT_EQ(framing.viewDistance, UI_DISTANCE);
  EXPECT_FLOAT_EQ(framing.fovDeg, UI_FOV);
}

TEST(TesseractFraming, ReferenceIsTheBlackHoleCameraDefault) {
  EXPECT_FLOAT_EQ(CameraState{}.distance, TESSERACT_RECORD_REFERENCE_DISTANCE);
  EXPECT_FLOAT_EQ(recorded(TESSERACT_RECORD_REFERENCE_DISTANCE, UI_FOV).viewDistance, UI_DISTANCE);
}

TEST(TesseractFraming, RecordDistanceScalesTheViewByItsRatio) {
  // The cinematic establishing shot (120) and its closing wide shot (140).
  EXPECT_FLOAT_EQ(recorded(120.0f, UI_FOV).viewDistance,
                  UI_DISTANCE * 120.0f / TESSERACT_RECORD_REFERENCE_DISTANCE);
  EXPECT_FLOAT_EQ(recorded(140.0f, UI_FOV).viewDistance,
                  UI_DISTANCE * 140.0f / TESSERACT_RECORD_REFERENCE_DISTANCE);
  EXPECT_FLOAT_EQ(recorded(480.0f, UI_FOV).viewDistance / recorded(240.0f, UI_FOV).viewDistance,
                  2.0f);
}

TEST(TesseractFraming, CloseRecordCamerasStopAtTheMinimumDistance) {
  // The cinematic path's close passes (18 to 40) map below the floor.
  EXPECT_FLOAT_EQ(recorded(18.0f, UI_FOV).viewDistance, TESSERACT_MIN_VIEW_DISTANCE);
  EXPECT_FLOAT_EQ(recorded(0.0f, UI_FOV).viewDistance, TESSERACT_MIN_VIEW_DISTANCE);
}

TEST(TesseractFraming, RecordFieldOfViewPassesThroughInsideThePerspectiveDomain) {
  EXPECT_FLOAT_EQ(recorded(15.0f, 68.0f).fovDeg, 68.0f);
  // Wider than the UI slider still passes: --record-fov 120 frames at 120.
  EXPECT_FLOAT_EQ(recorded(15.0f, 120.0f).fovDeg, 120.0f);
  EXPECT_FLOAT_EQ(recorded(15.0f, 200.0f).fovDeg, TESSERACT_MAX_FOV_DEG);
  EXPECT_FLOAT_EQ(recorded(15.0f, 0.0f).fovDeg, TESSERACT_MIN_FOV_DEG);
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

OffsetCamera offsetCamera(float frameX, float frameY) {
  const glm::vec3 focus(0.0f);
  const glm::vec3 cameraPos = glm::vec3(0.35f, -0.24f, -0.9f) * 14.0f;
  const float distance = glm::length(cameraPos - focus);
  const glm::mat3 baseBasis = buildCameraBasis(cameraPos, focus, 0.0f);
  const float halfHeight = std::tan(glm::radians(OFFSET_FOV) * 0.5f) * distance;
  const float halfWidth = halfHeight * OFFSET_ASPECT;
  const glm::vec3 aim =
      focus + (baseBasis[0] * (frameX * halfWidth)) + (baseBasis[1] * (frameY * halfHeight));
  OffsetCamera out;
  out.basis = buildCameraBasis(cameraPos, aim, 0.0f);
  out.focusDirection = glm::normalize(focus - cameraPos);
  const glm::mat4 projection =
      glm::perspective(glm::radians(OFFSET_FOV), OFFSET_ASPECT, 0.1f, 100.0f);
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

} // namespace
