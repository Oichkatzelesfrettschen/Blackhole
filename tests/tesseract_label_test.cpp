/**
 * @file tesseract_label_test.cpp
 * @brief The speculative-provenance label fits every render width it can.
 *
 * Widths span a 4K target down to a narrow docked viewport. Each layout line,
 * with its 2*scale background pad per side and SPECULATIVE_LABEL_MARGIN per
 * side, must fit the width; the lines joined with spaces must equal the label
 * so no word is dropped by wrapping.
 */

#include <string>
#include <vector>

#include <gtest/gtest.h>
#include <stb_easy_font.h>

#include "hud_overlay.h"
#include "render/tesseract/tesseract_renderer.h"

namespace {

using blackhole::layoutSpeculativeLabel;
using blackhole::SPECULATIVE_LABEL_MARGIN;
using blackhole::SPECULATIVE_LABEL_MAX_SCALE;
using blackhole::SpeculativeLabelLayout;
using blackhole::TESSERACT_SPECULATIVE_LABEL;

std::string joined(const std::vector<std::string> &lines) {
  std::string out;
  for (const std::string &line : lines) {
    out += out.empty() ? line : " " + line;
  }
  return out;
}

float occupiedWidth(const std::string &line, float scale) {
  return HudOverlay::measureText(line, scale).x + (4.0f * scale);
}

TEST(SpeculativeLabel, WideTargetsUseOneLineAtMaximumScale) {
  const SpeculativeLabelLayout layout = layoutSpeculativeLabel(1920);
  ASSERT_EQ(layout.lines.size(), 1U);
  EXPECT_EQ(layout.lines.front(), std::string(TESSERACT_SPECULATIVE_LABEL));
  EXPECT_FLOAT_EQ(layout.scale, SPECULATIVE_LABEL_MAX_SCALE);
}

TEST(SpeculativeLabel, EveryWidthFitsWithoutDroppingWords) {
  for (const int width : {3840, 1343, 900, 810, 640, 480, 360, 240, 160}) {
    const SpeculativeLabelLayout layout = layoutSpeculativeLabel(width);
    EXPECT_EQ(joined(layout.lines), std::string(TESSERACT_SPECULATIVE_LABEL)) << width;
    const float available = static_cast<float>(width) - (2.0f * SPECULATIVE_LABEL_MARGIN);
    for (const std::string &line : layout.lines) {
      EXPECT_LE(occupiedWidth(line, layout.scale), available + 1e-3f)
          << "width " << width << " line '" << line << "'";
    }
    EXPECT_LE(layout.scale, SPECULATIVE_LABEL_MAX_SCALE);
  }
}

TEST(SpeculativeLabel, NarrowTargetsWrapBeforeShrinkingBelowUnitScale) {
  // One pixel below the width where the single line reaches scale 1, the
  // layout wraps and keeps a legible scale >= 1.
  const float oneLine = occupiedWidth(std::string(TESSERACT_SPECULATIVE_LABEL), 1.0f);
  const int width = static_cast<int>(oneLine + (2.0f * SPECULATIVE_LABEL_MARGIN)) - 1;
  const SpeculativeLabelLayout layout = layoutSpeculativeLabel(width);
  EXPECT_GT(layout.lines.size(), 1U) << "width " << width;
  EXPECT_GE(layout.scale, 1.0f);
  // Above that width the label stays on one line.
  EXPECT_EQ(layoutSpeculativeLabel(width + 2).lines.size(), 1U);
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
