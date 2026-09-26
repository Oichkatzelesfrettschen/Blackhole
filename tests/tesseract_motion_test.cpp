/**
 * @file tesseract_motion_test.cpp
 * @brief Interactive tesseract animation follows the effective frame step.
 *
 * main feeds advanceTesseractMotion InputManager::getEffectiveDeltaTime, so
 * pause holds the orientation and pulse in place and the time scale sets the
 * step; recorded frames ignore the step and read the output clock. These
 * cases run GL-free on a heap RenderState and restore the shared
 * InputManager singleton they change.
 */

#include <cstddef>
#include <memory>
#include <optional>

#include <gtest/gtest.h>

#include "input.h"
#include "render/render_state.h"
#include "render/tesseract/so4.h"
#include "render/tesseract/tesseract_renderer.h"

namespace {

using blackhole::advanceTesseractMotion;
using blackhole::RenderState;
using blackhole::TesseractRecordFrame;

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

} // namespace
