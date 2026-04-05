/**
 * @file hud_overlay.cpp
 * @brief Implementation of HudOverlay -- stb_easy_font-based text overlay renderer.
 */
#include "hud_overlay.h"

#include <algorithm>
#include <cstddef> // std::size_t
#include <string>  // std::string (include-cleaner: direct use in append_text signature)
#include <vector>  // std::vector (include-cleaner: direct use in append_text signature)

// NOLINTBEGIN(misc-include-cleaner)
// glbinding/gl/gl.h is the conventional umbrella header; include-cleaner
// prefers per-symbol sub-headers but the umbrella is required for 'using namespace gl'.
#include <glbinding/gl/gl.h>
// NOLINTEND(misc-include-cleaner)

#include <stb_easy_font.h>

#include "physics/safe_limits.h"
#include "shader.h"
#include "tracy_support.h"

using namespace gl;

/* WHY: All GL symbols (glDrawArrays, GL_TRIANGLES, GLsizeiptr, etc.) come from
 * the glbinding umbrella header above. clang-tidy include-cleaner cannot resolve
 * umbrella headers to per-symbol sub-headers, so suppress it for this section. */
// NOLINTBEGIN(misc-include-cleaner)

namespace {

/** @brief Raw vertex layout produced by stb_easy_font_print. */
struct EasyFontVertex {
  float x;
  float y;
  [[maybe_unused]] float z;
  [[maybe_unused]] unsigned char color[4];
};

/**
 * @brief Return the pixel height of one text line at the given scale.
 * @param scale Glyph scale multiplier.
 * @return Line height in pixels.
 */
float lineHeight(float scale) {
  const char *sample = "Ag";
  // NOLINTBEGIN(cppcoreguidelines-pro-type-const-cast)
  // WHY: stb_easy_font_height takes char* (not const char*); no const version exists.
  return (static_cast<float>(stb_easy_font_height(const_cast<char *>(sample))) * scale) +
         (2.0f * scale);
  // NOLINTEND(cppcoreguidelines-pro-type-const-cast)
}

/**
 * @brief Rasterize a text string into the interleaved float vertex buffer.
 *
 * Converts stb_easy_font quads into two triangles each (x,y,r,g,b,a layout)
 * and appends them to @p out.
 *
 * @param out     Destination vertex buffer (x,y,r,g,b,a per vertex, appended).
 * @param scratch Reusable scratch buffer for stb_easy_font output (resized internally).
 * @param x       Left origin in pixels.
 * @param y       Top origin in pixels.
 * @param scale   Glyph scale multiplier.
 * @param text    String to rasterize (ASCII only).
 * @param color   RGBA color in [0,1] range.
 */
void appendText(std::vector<float> &out, std::vector<unsigned char> &scratch, float x, float y,
                float scale, const std::string &text, const glm::vec4 &color) {
  if (text.empty()) {
    return;
  }

  const int estimated = static_cast<int>((text.size() * 270) + 16);
  scratch.assign(static_cast<std::size_t>(estimated), 0);

  unsigned char rgba[4] = {static_cast<unsigned char>(std::clamp(color.r, 0.0f, 1.0f) * 255.0f),
                           static_cast<unsigned char>(std::clamp(color.g, 0.0f, 1.0f) * 255.0f),
                           static_cast<unsigned char>(std::clamp(color.b, 0.0f, 1.0f) * 255.0f),
                           static_cast<unsigned char>(std::clamp(color.a, 0.0f, 1.0f) * 255.0f)};

  // NOLINTBEGIN(cppcoreguidelines-pro-type-const-cast)
  // WHY: stb_easy_font_print takes char* (not const char*); no const version exists.
  const int quads = stb_easy_font_print(0.0f, 0.0f, const_cast<char *>(text.c_str()), rgba,
                                        scratch.data(), estimated);
  // NOLINTEND(cppcoreguidelines-pro-type-const-cast)
  const auto *verts = reinterpret_cast<const EasyFontVertex *>(scratch.data());

  out.reserve(out.size() + (static_cast<std::size_t>(quads) * 6U * 6U));
  for (int q = 0; q < quads; ++q) {
    // NOLINTNEXTLINE(bugprone-implicit-widening-of-multiplication-result)
    const EasyFontVertex *v = verts + (q * 4);
    const int indices[6] = {0, 1, 2, 0, 2, 3};
    for (const int idx : indices) {
      const EasyFontVertex &src = v[idx];
      const float px = x + (src.x * scale);
      const float py = y + (src.y * scale);
      out.push_back(px);
      out.push_back(py);
      out.push_back(color.r);
      out.push_back(color.g);
      out.push_back(color.b);
      out.push_back(color.a);
    }
  }
}

} // namespace

void HudOverlay::init() {
  BH_ZONE();
  if (program_ == 0) {
    program_ = createShaderProgram(std::string("shader/overlay_text.vert"),
                                   std::string("shader/overlay_text.frag"));
  }
  if (vao_ == 0) {
    glGenVertexArrays(1, &vao_);
  }
  if (vbo_ == 0) {
    glGenBuffers(1, &vbo_);
  }

  glBindVertexArray(vao_);
  glBindBuffer(GL_ARRAY_BUFFER, vbo_);
  glBufferData(GL_ARRAY_BUFFER, 0, nullptr, GL_DYNAMIC_DRAW);

  const auto stride = static_cast<GLsizei>(6 * sizeof(float));
  glEnableVertexAttribArray(0);
  glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, stride, nullptr);
  glEnableVertexAttribArray(1);
  // WHY: glVertexAttribPointer offset is passed as a void* cast from byte offset.
  glVertexAttribPointer(
      1, 4, GL_FLOAT, GL_FALSE, stride,
      reinterpret_cast<void *>(
          2 *
          sizeof(
              float))); // NOLINT(cppcoreguidelines-pro-type-reinterpret-cast,performance-no-int-to-ptr)

  glBindVertexArray(0);
  stb_easy_font_spacing(1.0f);
}

void HudOverlay::shutdown() {
  BH_ZONE();
  if (vbo_ != 0) {
    glDeleteBuffers(1, &vbo_);
    vbo_ = 0;
  }
  if (vao_ != 0) {
    glDeleteVertexArrays(1, &vao_);
    vao_ = 0;
  }
  if (program_ != 0) {
    glDeleteProgram(program_);
    program_ = 0;
  }
  vertices_.clear();
}

HudOverlay::~HudOverlay() {
  shutdown();
}

bool HudOverlay::isInitialized() const {
  return program_ != 0 && vao_ != 0 && vbo_ != 0;
}

void HudOverlay::setOptions(const HudOverlayOptions &opts) {
  options_ = opts;
}

const HudOverlayOptions &HudOverlay::options() const {
  return options_;
}

void HudOverlay::setLines(const std::vector<HudOverlayLine> &lines) {
  lines_ = lines;
}

void HudOverlay::addLine(const HudOverlayLine &line) {
  lines_.push_back(line);
}

void HudOverlay::clearLines() {
  lines_.clear();
}

// Measure text by invoking stb_easy_font and scanning vertex extents.
glm::vec2 HudOverlay::measureText(const std::string &text, float scale) {
  if (text.empty()) {
    return glm::vec2(0.0f);
  }

  const int estimated = static_cast<int>((text.size() * 270) + 16);
  std::vector<unsigned char> scratch(static_cast<std::size_t>(estimated));

  unsigned char rgba[4] = {255, 255, 255, 255};
  // NOLINTBEGIN(cppcoreguidelines-pro-type-const-cast)
  // WHY: stb_easy_font_print takes char* (not const char*); no const version exists.
  const int quads = stb_easy_font_print(0.0f, 0.0f, const_cast<char *>(text.c_str()), rgba,
                                        scratch.data(), estimated);
  // NOLINTEND(cppcoreguidelines-pro-type-const-cast)
  if (quads <= 0) {
    return glm::vec2(0.0f);
  }

  const auto *verts = reinterpret_cast<const EasyFontVertex *>(scratch.data());
  auto minx = physics::safeMax<float>();
  auto miny = physics::safeMax<float>();
  auto maxx = physics::safeLowest<float>();
  auto maxy = physics::safeLowest<float>();

  for (int q = 0; q < quads; ++q) {
    // NOLINTNEXTLINE(bugprone-implicit-widening-of-multiplication-result)
    const EasyFontVertex *v = verts + (q * 4);
    for (int i = 0; i < 4; ++i) {
      minx = std::min(minx, v[i].x);
      miny = std::min(miny, v[i].y);
      maxx = std::max(maxx, v[i].x);
      maxy = std::max(maxy, v[i].y);
    }
  }

  const float width = (maxx - minx) * scale;
  const float height = (maxy - miny) * scale;
  return {width, height};
}

void HudOverlay::rebuildVertices(int width, int height) {
  BH_ZONE();
  vertices_.clear();
  if (lines_.empty() || width <= 0 || height <= 0) {
    return;
  }

  const float scale = std::max(options_.scale, 0.25f);
  const float baseLine = lineHeight(scale);
  const float lineStep = baseLine * options_.lineSpacing;

  // Precompute the starting Y depending on origin.
  float cursorY = 0.0f;
  if (options_.origin == HudOverlayOptions::Origin::TopLeft) {
    cursorY = options_.margin;
  } else {
    // Bottom-left origin: start such that last line sits at margin from bottom.
    cursorY = static_cast<float>(height) - options_.margin -
              (baseLine * (static_cast<float>(lines_.size()) - 1.0f) * options_.lineSpacing);
  }

  std::vector<unsigned char> scratch;
  for (const auto &line : lines_) {
    // Determine text extents to support alignment and background.
    const glm::vec2 extents = measureText(line.text, scale);
    float x = 0.0f;
    if (options_.align == HudOverlayOptions::Align::Left) {
      x = options_.margin;
    } else if (options_.align == HudOverlayOptions::Align::Center) {
      x = (static_cast<float>(width) * 0.5f) - (extents.x * 0.5f);
    } else { // Right
      x = static_cast<float>(width) - options_.margin - extents.x;
    }

    // Optional background box
    if (options_.drawBackground && line.background.a > 0.0f) {
      const float pad = 2.0f * scale;
      const float bx0 = x - pad;
      const float by0 = cursorY - pad;
      const float bx1 = x + extents.x + pad;
      const float by1 = cursorY + baseLine + pad;

      // Two triangles (6 vertices)
      const glm::vec4 bg = line.background;
      auto pushVertex = [&](float px, float py) {
        vertices_.push_back(px);
        vertices_.push_back(py);
        vertices_.push_back(bg.r);
        vertices_.push_back(bg.g);
        vertices_.push_back(bg.b);
        vertices_.push_back(bg.a);
      };

      // Triangle 1
      pushVertex(bx0, by0);
      pushVertex(bx1, by0);
      pushVertex(bx1, by1);
      // Triangle 2
      pushVertex(bx0, by0);
      pushVertex(bx1, by1);
      pushVertex(bx0, by1);
    }

    // Append the text glyph quads
    appendText(vertices_, scratch, x, cursorY, scale, line.text, line.color);

    cursorY += lineStep;
  }
}

void HudOverlay::render(int width, int height) {
  BH_ZONE();
  if (width <= 0 || height <= 0) {
    return;
  }
  if (!isInitialized()) {
    init();
  }

  rebuildVertices(width, height);

  if (vertices_.empty()) {
    return;
  }

  glUseProgram(program_);
  glUniform2f(glGetUniformLocation(program_, "uScreenSize"), static_cast<float>(width),
              static_cast<float>(height));

  glBindVertexArray(vao_);
  glBindBuffer(GL_ARRAY_BUFFER, vbo_);
  glBufferData(GL_ARRAY_BUFFER, static_cast<GLsizeiptr>(vertices_.size() * sizeof(float)),
               vertices_.data(), GL_DYNAMIC_DRAW);

  glDisable(GL_DEPTH_TEST);
  glEnable(GL_BLEND);
  glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

  const auto vertexCount = static_cast<GLsizei>(vertices_.size() / 6);
  glDrawArrays(GL_TRIANGLES, 0, vertexCount);

  glBindVertexArray(0);
  glUseProgram(0);
}

// Backwards-compatible immediate-mode render (keeps original behavior).
void HudOverlay::render(int width, int height, float scale, float margin,
                        const std::vector<HudOverlayLine> &lines) {
  BH_ZONE();
  if (lines.empty() || width <= 0 || height <= 0) {
    return;
  }
  if (!isInitialized()) {
    init();
  }

  scale = std::max(scale, 0.25f);
  float cursorY = margin;
  const float lineStep = lineHeight(scale);

  vertices_.clear();
  std::vector<unsigned char> scratch;
  for (const auto &line : lines) {
    appendText(vertices_, scratch, margin, cursorY, scale, line.text, line.color);
    cursorY += lineStep;
  }

  if (vertices_.empty()) {
    return;
  }

  glUseProgram(program_);
  glUniform2f(glGetUniformLocation(program_, "uScreenSize"), static_cast<float>(width),
              static_cast<float>(height));

  glBindVertexArray(vao_);
  glBindBuffer(GL_ARRAY_BUFFER, vbo_);
  glBufferData(GL_ARRAY_BUFFER, static_cast<GLsizeiptr>(vertices_.size() * sizeof(float)),
               vertices_.data(), GL_DYNAMIC_DRAW);

  glDisable(GL_DEPTH_TEST);
  glEnable(GL_BLEND);
  glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

  const auto vertexCount = static_cast<GLsizei>(vertices_.size() / 6);
  glDrawArrays(GL_TRIANGLES, 0, vertexCount);

  glBindVertexArray(0);
  glUseProgram(0);
}

// NOLINTEND(misc-include-cleaner)
