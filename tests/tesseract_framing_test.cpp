/**
 * @file tesseract_framing_test.cpp
 * @brief Recorded tesseract frames follow the record camera's distance and
 *        field of view.
 *
 * tesseractFraming maps the black-hole record camera distance d to the
 * tesseract view distance viewDistance * d / TESSERACT_RECORD_REFERENCE_DISTANCE
 * with a TESSERACT_MIN_VIEW_DISTANCE floor, and passes the field of view
 * through inside glm::perspective's domain; interactive frames keep the UI
 * values.
 */

#include <optional>

#include <gtest/gtest.h>

#include "input.h"
#include "render/tesseract/tesseract_renderer.h"

namespace {

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

} // namespace
