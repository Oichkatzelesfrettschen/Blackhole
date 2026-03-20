#ifndef HUD_OVERLAY_H
#define HUD_OVERLAY_H

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

/** @brief A single line of text rendered by the HUD overlay. */
struct HudOverlayLine {
  std::string text;
  glm::vec4 color = glm::vec4(1.0f);
  /** @brief Per-line background color; alpha == 0 disables the background box. */
  glm::vec4 background = glm::vec4(0.0f);
};

/** @brief Layout and renderer options controlling how the overlay is positioned and drawn. */
struct HudOverlayOptions {
  /** @brief Horizontal text alignment within the viewport. */
  enum class Align { Left, Center, Right };
  /** @brief Anchor corner from which Y positions are measured. */
  enum class Origin { TopLeft, BottomLeft };

  float scale = 1.0f;          /**< @brief Global scale multiplier applied to all glyphs. */
  float margin = 4.0f;         /**< @brief Pixel margin from the chosen origin corner. */
  float lineSpacing = 1.0f;    /**< @brief Multiplier on the default line height. */
  Align align = Align::Left;   /**< @brief Horizontal alignment for all lines. */
  Origin origin = Origin::TopLeft; /**< @brief Anchor corner for layout. */

  /**
   * @brief When true, draw a background box behind each line whose
   * HudOverlayLine::background alpha is greater than zero.
   */
  bool drawBackground = false;

  /**
   * @brief Optional path to a font file for a future TrueType backend.
   * When empty the default stb_easy_font (ASCII-only) backend is used.
   */
  std::optional<std::string> fontFile;
};

/**
 * @brief Lightweight OpenGL HUD overlay that renders ASCII text using stb_easy_font.
 *
 * Owns its own VAO, VBO, and shader program.  Call init() once after the GL
 * context is ready, then either use the stateful API (setLines / render) or
 * the immediate-mode overload for backwards compatibility.
 */
class HudOverlay {
public:
  HudOverlay() = default;
  ~HudOverlay();
  HudOverlay(const HudOverlay &) = delete;
  HudOverlay &operator=(const HudOverlay &) = delete;
  HudOverlay(HudOverlay &&) = delete;
  HudOverlay &operator=(HudOverlay &&) = delete;

  /** @brief Initialize GL resources (VAO, VBO, shader). Safe to call multiple times. */
  void init();

  /** @brief Release all GL resources. Safe to call multiple times. */
  void shutdown();

  /** @brief Return true when init() has successfully created all GL objects. */
  [[nodiscard]] bool isInitialized() const;

  /**
   * @brief Replace the current layout and backend options.
   * @param opts New options; changes take effect on the next render() call.
   */
  void setOptions(const HudOverlayOptions &opts);

  /** @brief Return a reference to the current overlay options. */
  [[nodiscard]] const HudOverlayOptions &options() const;

  /**
   * @brief Replace the stored line list used by the stateful render overload.
   * @param lines New set of lines; the overlay takes a copy.
   */
  void setLines(const std::vector<HudOverlayLine> &lines);

  /**
   * @brief Append a single line to the stored line list.
   * @param line Line to append.
   */
  void addLine(const HudOverlayLine &line);

  /** @brief Remove all stored lines. */
  void clearLines();

  /**
   * @brief Render the stored lines with the stored options.
   * @param width  Framebuffer width in pixels.
   * @param height Framebuffer height in pixels.
   */
  void render(int width, int height);

  /**
   * @brief Immediate-mode render -- renders the given lines for a single frame.
   *
   * Backwards-compatible overload; does not modify stored state.
   *
   * @param width  Framebuffer width in pixels.
   * @param height Framebuffer height in pixels.
   * @param scale  Glyph scale multiplier.
   * @param margin Pixel margin from the top-left corner.
   * @param lines  Lines to render this frame.
   */
  void render(int width, int height, float scale, float margin,
              const std::vector<HudOverlayLine> &lines);

  /**
   * @brief Measure the approximate pixel extents of a text string.
   *
   * Uses stb_easy_font vertex scanning; cheap and approximate.
   *
   * @param text  String to measure.
   * @param scale Glyph scale multiplier (default 1.0).
   * @return      {width, height} in pixels at the given scale.
   */
  static glm::vec2 measureText(const std::string &text, float scale = 1.0f);

  /** @brief Return the compiled overlay shader program handle. */
  [[nodiscard]] GLuint program() const { return program_; }
  /** @brief Return the vertex array object handle. */
  [[nodiscard]] GLuint vao() const { return vao_; }
  /** @brief Return the vertex buffer object handle. */
  [[nodiscard]] GLuint vbo() const { return vbo_; }

private:
  HudOverlayOptions options_;
  std::vector<HudOverlayLine> lines_;

  /** @brief GL VAO handle; 0 when uninitialized. */
  GLuint vao_ = 0;
  /** @brief GL VBO handle; 0 when uninitialized. */
  GLuint vbo_ = 0;
  /** @brief Linked shader program handle; 0 when uninitialized. */
  GLuint program_ = 0;

  /** @brief CPU staging buffer -- x,y,r,g,b,a float tuples for every glyph vertex. */
  std::vector<float> vertices_;

  /**
   * @brief Rebuild vertices_ from lines_ and options_ for the given viewport.
   * @param width  Viewport width in pixels.
   * @param height Viewport height in pixels.
   */
  void rebuildVertices(int width, int height);
};

#endif // HUD_OVERLAY_H
