/**
 * @file tesseract_label_test.cpp
 * @brief The speculative-provenance label fits every render target it can.
 *
 * Targets span a 4K frame down to a narrow, short docked viewport. Each layout
 * line, with its 2*scale background pad per side and SPECULATIVE_LABEL_MARGIN
 * per side, must fit the width; the block of n lines, n *
 * HudOverlay::lineHeight(scale) plus the pad above and below and a margin on
 * each side, must fit the height. The lines joined with spaces must equal the
 * label so no word is dropped by wrapping.
 */

#include <algorithm>
#include <string>
#include <utility>
#include <vector>

#include <gtest/gtest.h>
#include <stb_easy_font.h>

#include "hud_overlay.h"
#include "render/tesseract/tesseract_renderer.h"

namespace {

using blackhole::layoutSpeculativeLabel;
using blackhole::SPECULATIVE_LABEL_MARGIN;
using blackhole::SPECULATIVE_LABEL_MAX_SCALE;
using blackhole::SPECULATIVE_LABEL_MIN_SCALE;
using blackhole::SPECULATIVE_LABEL_MIN_TARGET_HEIGHT;
using blackhole::SPECULATIVE_LABEL_MIN_TARGET_WIDTH;
using blackhole::SpeculativeLabelLayout;
using blackhole::TESSERACT_SPECULATIVE_LABEL;

// Taller than any layout needs, so width alone constrains the fit.
constexpr int TALL = 2160;
// Float slack for comparing layout arithmetic against re-measured extents.
constexpr float FIT_EPSILON_PX = 1e-3f;

std::string joined(const std::vector<std::string> &lines) {
  std::string out;
  for (const std::string &line : lines) {
    if (!out.empty()) {
      out += ' ';
    }
    out += line;
  }
  return out;
}

float occupiedWidth(const std::string &line, float scale) {
  return HudOverlay::measureText(line, scale).x + (4.0f * scale);
}

float occupiedHeight(const SpeculativeLabelLayout &layout) {
  return (static_cast<float>(layout.lines.size()) * HudOverlay::lineHeight(layout.scale)) +
         (4.0f * layout.scale);
}

float available(int extent) {
  return static_cast<float>(extent) - (2.0f * SPECULATIVE_LABEL_MARGIN);
}

bool widthFits(const SpeculativeLabelLayout &layout, int width) {
  return std::ranges::all_of(layout.lines, [&layout, width](const std::string &line) {
    return occupiedWidth(line, layout.scale) <= available(width) + FIT_EPSILON_PX;
  });
}

bool heightFits(const SpeculativeLabelLayout &layout, int height) {
  return occupiedHeight(layout) <= available(height) + FIT_EPSILON_PX;
}

void expectFits(int width, int height) {
  const SpeculativeLabelLayout layout = layoutSpeculativeLabel(width, height);
  EXPECT_EQ(joined(layout.lines), std::string(TESSERACT_SPECULATIVE_LABEL))
      << width << "x" << height;
  EXPECT_TRUE(widthFits(layout, width)) << width << "x" << height << " scale " << layout.scale;
  EXPECT_TRUE(heightFits(layout, height))
      << width << "x" << height << " lines " << layout.lines.size() << " scale " << layout.scale;
  EXPECT_GE(layout.scale, SPECULATIVE_LABEL_MIN_SCALE);
  EXPECT_LE(layout.scale, SPECULATIVE_LABEL_MAX_SCALE);
}

TEST(SpeculativeLabel, WideTargetsUseOneLineAtMaximumScale) {
  const SpeculativeLabelLayout layout = layoutSpeculativeLabel(1920, 1080);
  ASSERT_EQ(layout.lines.size(), 1U);
  EXPECT_EQ(layout.lines.front(), std::string(TESSERACT_SPECULATIVE_LABEL));
  EXPECT_FLOAT_EQ(layout.scale, SPECULATIVE_LABEL_MAX_SCALE);
}

TEST(SpeculativeLabel, EveryWidthFitsWithoutDroppingWords) {
  for (const int width : {3840, 1343, 900, 810, 640, 480, 360, 240, 160, 120, 96, 80}) {
    expectFits(width, TALL);
  }
}

TEST(SpeculativeLabel, NarrowTargetsWrapBeforeShrinkingBelowUnitScale) {
  // One pixel below the width where the single line reaches scale 1, the
  // layout wraps and keeps a legible scale >= 1.
  const float oneLine = occupiedWidth(std::string(TESSERACT_SPECULATIVE_LABEL), 1.0f);
  const int width = static_cast<int>(oneLine + (2.0f * SPECULATIVE_LABEL_MARGIN)) - 1;
  const SpeculativeLabelLayout layout = layoutSpeculativeLabel(width, TALL);
  EXPECT_GT(layout.lines.size(), 1U) << "width " << width;
  EXPECT_GE(layout.scale, 1.0f);
  // Above that width the label stays on one line.
  EXPECT_EQ(layoutSpeculativeLabel(width + 2, TALL).lines.size(), 1U);
}

TEST(SpeculativeLabel, ShortTargetsFitTheBlockHeight) {
  // Short and narrow viewports, where a width-only fit wraps into lines that
  // run below the target.
  for (const auto &[width, height] : {std::pair{240, 60}, std::pair{240, 80}, std::pair{160, 72},
                                      std::pair{360, 50}, std::pair{120, 100}, std::pair{96, 70},
                                      std::pair{480, 40}, std::pair{1920, 40}}) {
    expectFits(width, height);
  }
  // A wide, short strip keeps one line and shrinks to the height.
  const SpeculativeLabelLayout strip = layoutSpeculativeLabel(1920, 40);
  EXPECT_EQ(strip.lines.size(), 1U);
  EXPECT_LT(strip.scale, 1.0f);
}

TEST(SpeculativeLabel, EveryTargetAboveTheMinimumHoldsTheBlock) {
  for (int width = SPECULATIVE_LABEL_MIN_TARGET_WIDTH; width <= 720; ++width) {
    for (const int height :
         {SPECULATIVE_LABEL_MIN_TARGET_HEIGHT, SPECULATIVE_LABEL_MIN_TARGET_HEIGHT + 1, 80, 120,
          240, TALL}) {
      expectFits(width, height);
    }
  }
  for (int height = SPECULATIVE_LABEL_MIN_TARGET_HEIGHT; height <= 480; ++height) {
    for (const int width : {SPECULATIVE_LABEL_MIN_TARGET_WIDTH,
                            SPECULATIVE_LABEL_MIN_TARGET_WIDTH + 1, 120, 240, 640, 1920}) {
      expectFits(width, height);
    }
  }
}

TEST(SpeculativeLabel, MinimumTargetIsTight) {
  // One pixel narrower than the minimum, the widest word overflows; one pixel
  // shorter at the minimum width, the wrapped block overflows.
  const SpeculativeLabelLayout narrow =
      layoutSpeculativeLabel(SPECULATIVE_LABEL_MIN_TARGET_WIDTH - 1, TALL);
  EXPECT_FALSE(widthFits(narrow, SPECULATIVE_LABEL_MIN_TARGET_WIDTH - 1));
  const SpeculativeLabelLayout shortTarget = layoutSpeculativeLabel(
      SPECULATIVE_LABEL_MIN_TARGET_WIDTH, SPECULATIVE_LABEL_MIN_TARGET_HEIGHT - 1);
  EXPECT_FALSE(heightFits(shortTarget, SPECULATIVE_LABEL_MIN_TARGET_HEIGHT - 1));
}

TEST(SpeculativeLabel, TargetsBelowTheMinimumKeepEveryWord) {
  for (const auto &[width, height] :
       {std::pair{0, 0}, std::pair{1, 1}, std::pair{20, 20}, std::pair{40, 400},
        std::pair{400, 20}}) {
    EXPECT_EQ(joined(layoutSpeculativeLabel(width, height).lines),
              std::string(TESSERACT_SPECULATIVE_LABEL))
        << width << "x" << height;
  }
}

// HudOverlay::measureText must use the same glyph spacing as the vertices it
// renders, from the first call on, with no HudOverlay initialized. Appending
// one 'A' widens the text by the glyph advance plus HUD_GLYPH_SPACING.
TEST(SpeculativeLabel, MeasurementUsesRenderSpacingWithoutInit) {
  const int advance = stb_easy_font_charinfo['A' - 32].advance & 15;
  const float step = HudOverlay::measureText("AA", 1.0f).x - HudOverlay::measureText("A", 1.0f).x;
  EXPECT_FLOAT_EQ(step, static_cast<float>(advance) + HUD_GLYPH_SPACING);
}

} // namespace
