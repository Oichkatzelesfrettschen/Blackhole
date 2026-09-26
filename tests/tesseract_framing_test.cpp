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

#include <cmath>
#include <optional>
#include <utility>

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
#include "render/tesseract/tesseract_renderer.h"

namespace {

using blackhole::buildCameraBasis;
using blackhole::TESSERACT_MAX_FOV_DEG;
using blackhole::TESSERACT_MIN_FOV_DEG;
using blackhole::TESSERACT_MIN_VIEW_DISTANCE;
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
  // The showcase-orbit default (14) and the cinematic establishing shot (120).
  EXPECT_FLOAT_EQ(recorded(14.0f, UI_FOV).viewDistance, UI_DISTANCE * 14.0f / 15.0f);
  EXPECT_FLOAT_EQ(recorded(120.0f, UI_FOV).viewDistance, UI_DISTANCE * 8.0f);
  EXPECT_FLOAT_EQ(recorded(30.0f, UI_FOV).viewDistance / recorded(15.0f, UI_FOV).viewDistance,
                  2.0f);
}

TEST(TesseractFraming, CloseRecordCamerasStopAtTheMinimumDistance) {
  // The cinematic path's closest distance, 5.2, maps below the floor.
  EXPECT_FLOAT_EQ(recorded(5.2f, UI_FOV).viewDistance, TESSERACT_MIN_VIEW_DISTANCE);
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

} // namespace
