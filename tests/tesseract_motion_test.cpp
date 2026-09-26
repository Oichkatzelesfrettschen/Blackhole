/**
 * @file tesseract_motion_test.cpp
 * @brief Interactive tesseract animation follows the effective frame step.
 *
 * main feeds advanceTesseractMotion InputManager::getEffectiveDeltaTime, so
 * pause holds the orientation and pulse in place and the time scale sets the
 * step; recorded frames ignore the step and read the output clock. Zoom
 * input in the tesseract scene moves the tesseract view distance and leaves
 * the black-hole camera distance alone, and Reset Camera returns both to
 * their defaults. These
 * cases run GL-free on a heap RenderState and restore the shared
 * InputManager singleton they change.
 */

#include <cstddef>
#include <memory>
#include <optional>

#include <gtest/gtest.h>
#include <imgui.h>

#include "input.h"
#include "render/render_state.h"
#include "render/tesseract/so4.h"
#include "render/tesseract/tesseract_renderer.h"

namespace {

using blackhole::advanceTesseractMotion;
using blackhole::RenderState;
using blackhole::TESSERACT_DEFAULT_VIEW_DISTANCE;
using blackhole::TESSERACT_MAX_VIEW_DISTANCE;
using blackhole::TESSERACT_MIN_VIEW_DISTANCE;
using blackhole::TesseractRecordFrame;
using blackhole::tesseractViewDistanceAfterInput;
using blackhole::tesseractZoom;

// One interactive frame at 60 Hz.
constexpr float FRAME_S = 1.0f / 60.0f;

double orientationDistance(const RenderState &a, const RenderState &b) {
  const auto ma = blackhole::tesseract::toColumnMajor(
      blackhole::tesseract::so4FromPair(a.tesseract.orientation));
  const auto mb = blackhole::tesseract::toColumnMajor(
      blackhole::tesseract::so4FromPair(b.tesseract.orientation));
  double sum = 0.0;
  for (std::size_t i = 0; i < ma.size(); ++i) {
    const double d = static_cast<double>(ma.at(i)) - static_cast<double>(mb.at(i));
    sum += d * d;
  }
  return sum;
}

class TesseractMotion : public ::testing::Test {
protected:
  void SetUp() override { wasPaused_ = InputManager::instance().isPaused(); }
  void TearDown() override { InputManager::instance().setPaused(wasPaused_); }

  static std::unique_ptr<RenderState> seeded() {
    auto rs = std::make_unique<RenderState>();
    // Seed the orientation from the reset phase with a zero step.
    advanceTesseractMotion(*rs, 0.0f, std::nullopt);
    return rs;
  }

private:
  bool wasPaused_ = false;
};

TEST_F(TesseractMotion, PauseHoldsTheScene) {
  InputManager &input = InputManager::instance();
  input.setPaused(true);
  const auto before = seeded();
  const auto after = seeded();
  const float pulseBefore = after->tesseract.pulseTravel;
  for (int frame = 0; frame < 30; ++frame) {
    advanceTesseractMotion(*after, input.getEffectiveDeltaTime(FRAME_S), std::nullopt);
  }
  EXPECT_DOUBLE_EQ(orientationDistance(*before, *after), 0.0);
  EXPECT_FLOAT_EQ(after->tesseract.pulseTravel, pulseBefore);
}

TEST_F(TesseractMotion, RunningFramesAdvanceByTheScaledStep) {
  InputManager &input = InputManager::instance();
  input.setPaused(false);
  const float step = input.getEffectiveDeltaTime(FRAME_S);
  EXPECT_FLOAT_EQ(step, FRAME_S * input.getTimeScale());
  const auto stepped = seeded();
  const auto reference = seeded();
  advanceTesseractMotion(*stepped, step, std::nullopt);
  advanceTesseractMotion(*reference, FRAME_S * input.getTimeScale(), std::nullopt);
  EXPECT_DOUBLE_EQ(orientationDistance(*stepped, *reference), 0.0);
  if (input.getTimeScale() > 0.0f) {
    EXPECT_GT(orientationDistance(*seeded(), *stepped), 0.0);
  }
}

TEST_F(TesseractMotion, RecordedFramesIgnoreTheStep) {
  const auto a = seeded();
  const auto b = seeded();
  const TesseractRecordFrame record{.outputClockSeconds = 2.5, .camera = {}};
  advanceTesseractMotion(*a, 0.0f, record);
  advanceTesseractMotion(*b, 0.2f, record);
  EXPECT_DOUBLE_EQ(orientationDistance(*a, *b), 0.0);
}

// Redirected zoom scales the tesseract view by the black-hole framing ratio
// and stays inside the View distance slider range.
TEST(TesseractZoom, RedirectedZoomMovesTheViewDistance) {
  EXPECT_FLOAT_EQ(tesseractZoom(8.0f, 0.0f), 8.0f);
  EXPECT_FLOAT_EQ(tesseractZoom(8.0f, -1.5f), 8.0f - (1.5f * 8.0f / 15.0f));
  EXPECT_FLOAT_EQ(tesseractZoom(8.0f, 3.0f), 8.0f + (3.0f * 8.0f / 15.0f));
  EXPECT_FLOAT_EQ(tesseractZoom(3.2f, -10.0f), TESSERACT_MIN_VIEW_DISTANCE);
  EXPECT_FLOAT_EQ(tesseractZoom(19.0f, 40.0f), TESSERACT_MAX_VIEW_DISTANCE);
}

// While redirected, a scroll step accumulates as pending zoom and the camera
// distance holds; without the redirect the same step moves the camera.
TEST(TesseractZoom, ScrollLeavesTheBlackHoleCameraWhileRedirected) {
  ImGuiContext *const context = ImGui::CreateContext();
  InputManager &input = InputManager::instance();
  const CameraState saved = input.camera();
  const bool wasPaused = input.isPaused();
  const bool gamepad = input.isGamepadEnabled();
  input.setPaused(false);
  input.setGamepadEnabled(false);
  input.setIgnoreGuiCapture(true);
  // At the default 240 the black-hole zoom rate is 16 times its reference
  // rate; the redirected delta stays in reference-rate units.
  input.camera().distance = 240.0f;
  const float step = input.getScrollSensitivity() * 0.5f * input.getTimeScale();

  input.setZoomRedirect(true);
  input.onScroll(0.0, 2.0);
  input.update(1.0f / 60.0f);
  EXPECT_FLOAT_EQ(input.camera().distance, 240.0f);
  EXPECT_FLOAT_EQ(input.takeZoomDelta(), -2.0f * step);
  EXPECT_FLOAT_EQ(input.takeZoomDelta(), 0.0f);

  input.setZoomRedirect(false);
  input.onScroll(0.0, 2.0);
  input.update(1.0f / 60.0f);
  EXPECT_FLOAT_EQ(input.camera().distance, 240.0f - (2.0f * step * zoomRateScale(240.0f)));
  EXPECT_FLOAT_EQ(input.takeZoomDelta(), 0.0f);

  input.setIgnoreGuiCapture(false);
  input.setGamepadEnabled(gamepad);
  input.setPaused(wasPaused);
  input.camera() = saved;
  ImGui::DestroyContext(context);
}

TEST(TesseractZoom, CameraResetReturnsTheDefaultViewDistance) {
  EXPECT_FLOAT_EQ(std::make_unique<RenderState>()->tesseract.viewDistance,
                  TESSERACT_DEFAULT_VIEW_DISTANCE);
  EXPECT_FLOAT_EQ(tesseractViewDistanceAfterInput(15.0f, 0.0f, true),
                  TESSERACT_DEFAULT_VIEW_DISTANCE);
  // The reset frame drops its zoom.
  EXPECT_FLOAT_EQ(tesseractViewDistanceAfterInput(4.0f, 3.0f, true),
                  TESSERACT_DEFAULT_VIEW_DISTANCE);
  EXPECT_FLOAT_EQ(tesseractViewDistanceAfterInput(8.0f, 3.0f, false), tesseractZoom(8.0f, 3.0f));
}

// resetCamera, which the key and gamepad Reset Camera actions run, resets
// the camera pose and reports the reset once, so the frame that reads it
// resets the tesseract view distance too.
TEST(TesseractZoom, ResetCameraReportsTheResetOnce) {
  InputManager &input = InputManager::instance();
  const CameraState saved = input.camera();
  static_cast<void>(input.takeCameraReset());
  EXPECT_FALSE(input.takeCameraReset());

  input.camera().distance = 30.0f;
  input.camera().yaw = 40.0f;
  input.resetCamera();
  EXPECT_FLOAT_EQ(input.camera().distance, CameraState{}.distance);
  EXPECT_FLOAT_EQ(input.camera().yaw, CameraState{}.yaw);
  const bool reset = input.takeCameraReset();
  EXPECT_TRUE(reset);
  EXPECT_FALSE(input.takeCameraReset());
  EXPECT_FLOAT_EQ(tesseractViewDistanceAfterInput(15.0f, 0.0f, reset),
                  TESSERACT_DEFAULT_VIEW_DISTANCE);

  input.camera() = saved;
}

// The tesseract view keeps its scene at the origin, so the gizmo target
// moves the camera focus in the black-hole scene alone.
TEST(TesseractScene, GizmoTargetAppliesToTheBlackHoleSceneOnly) {
  auto rs = std::make_unique<RenderState>();
  EXPECT_FALSE(rs->gizmoTargetActive());
  rs->camera.gizmoEnabled = true;
  EXPECT_TRUE(rs->gizmoTargetActive());
  rs->scene.mode = RenderState::SceneMode::Tesseract;
  EXPECT_FALSE(rs->gizmoTargetActive());
}

} // namespace
