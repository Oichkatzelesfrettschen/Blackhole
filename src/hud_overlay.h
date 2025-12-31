#pragma once

/**
 * @file hud_overlay.h
 * @brief Minimal HUD/text overlay utility used for performance/debug overlays.
 *
 * Current implementation (see `src/hud_overlay.cpp`) uses `stb_easy_font` to
 * emit simple quads for ASCII text. The overlay is intentionally lightweight
 * and suitable for showing performance data (FPS, frametime, GPU timers) as
 * described in `docs/mangohud-hud-scope.md`.
 *
 * Expansion notes (design goals):
 *  - Keep the default fast path (stb_easy_font) for compact overlays.
 *  - Support a richer backend (TrueType glyph atlas / SDF font) for UTF-8
 *    and better typographic control in future.
 *  - Provide convenient layout options (alignment, origin, spacing) and
 *    an API that allows the caller to maintain a persistent overlay state
 *    (so callers don't need to re-pass lines every frame unless desired).
 */

#include <string>
#include <vector>
#include <cstdint>
#include <optional>

#include <glm/glm.hpp>
#include "gl_loader.h"

// The minimal data for a single overlay line.
struct HudOverlayLine {
  std::string text;
  glm::vec4 color = glm::vec4(1.0f);
  // Optional per-line background (alpha == 0 means no background).
  glm::vec4 background = glm::vec4(0.0f);
};

// Layout and renderer options for the overlay.
struct HudOverlayOptions {
  enum class Align { Left, Center, Right };
  enum class Origin { TopLeft, BottomLeft };

  float scale = 1.0f;          // Global scale multiplier
  float margin = 4.0f;         // Margin from chosen origin
  float lineSpacing = 1.0f;    // Multiplier on default line height
  Align align = Align::Left;   // Horizontal alignment
  Origin origin = Origin::TopLeft;

  // If true, draw a compact background box behind each line when
  // HudOverlayLine::background.a > 0.
  bool drawBackground = false;

  // Backend selection: by default the implementation uses stb_easy_font
  // (ASCII-only, very cheap). A future TrueType backend may be added and
  // selected via the `fontFile` member.
  std::optional<std::string> fontFile;
};

class HudOverlay {
public:
  HudOverlay() = default;
  ~HudOverlay();

  // Initialize GL resources if necessary. Safe to call multiple times.
  void init();

  // Release GL resources. Safe to call multiple times.
  void shutdown();

  // Convenience RAII-style helpers.
  bool isInitialized() const;

  // Set/get options (layout + backend hints). Changes take effect on next render.
  void setOptions(const HudOverlayOptions &opts);
  const HudOverlayOptions &options() const;

  // Manage the lines owned by the overlay. The overlay stores the given
  // set and will use them for subsequent `render(width,height)` calls.
  void setLines(const std::vector<HudOverlayLine> &lines);
  void addLine(const HudOverlayLine &line);
  void clearLines();

  // Render with the stored options and lines.
  void render(int width, int height);

  // Immediate-mode render: render these lines for a single frame using
  // provided scale/margin (backwards compatible with existing call sites).
  void render(int width, int height, float scale, float margin,
              const std::vector<HudOverlayLine> &lines);

  // Measure the approximate pixel size of a text string at given scale.
  // This is cheap for the easy-font backend and approximate for other backends.
  glm::vec2 measureText(const std::string &text, float scale = 1.0f) const;

  // Low-level accessors (useful for tests or custom rendering paths).
  GLuint program() const { return program_; }
  GLuint vao() const { return vao_; }
  GLuint vbo() const { return vbo_; }

private:
  HudOverlayOptions options_;
  std::vector<HudOverlayLine> lines_;

  // GL state: owned by the overlay implementation.
  GLuint vao_ = 0;
  GLuint vbo_ = 0;
  GLuint program_ = 0;

  // CPU-side vertex staging buffer (x,y,r,g,b,a interleaved as floats).
  std::vector<float> vertices_;

  // Helper: rebuild vertices_ from lines_ and options_.
  void rebuildVertices(int width, int height);
};
