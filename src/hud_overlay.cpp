#include "hud_overlay.h"

#include <algorithm>
#include <cstdint>

#include "shader.h"
#include "tracy_support.h"

#include <stb_easy_font.h>

namespace {

struct EasyFontVertex {
  float x;
  float y;
  [[maybe_unused]] float z;
  [[maybe_unused]] unsigned char color[4];
};

float line_height(float scale) {
  const char *sample = "Ag";
  return static_cast<float>(stb_easy_font_height(const_cast<char *>(sample))) * scale +
         2.0f * scale;
}

void append_text(std::vector<float> &out, std::vector<unsigned char> &scratch, float x, float y,
                 float scale, const std::string &text, const glm::vec4 &color) {
  if (text.empty()) {
    return;
  }

  const int estimated = static_cast<int>(text.size() * 270 + 16);
  scratch.assign(static_cast<std::size_t>(estimated), 0);

  unsigned char rgba[4] = {
      static_cast<unsigned char>(std::clamp(color.r, 0.0f, 1.0f) * 255.0f),
      static_cast<unsigned char>(std::clamp(color.g, 0.0f, 1.0f) * 255.0f),
      static_cast<unsigned char>(std::clamp(color.b, 0.0f, 1.0f) * 255.0f),
      static_cast<unsigned char>(std::clamp(color.a, 0.0f, 1.0f) * 255.0f)};

  int quads = stb_easy_font_print(0.0f, 0.0f, const_cast<char *>(text.c_str()), rgba,
                                  scratch.data(), estimated);
  const auto *verts = reinterpret_cast<const EasyFontVertex *>(scratch.data());

  out.reserve(out.size() + static_cast<std::size_t>(quads) * 6 * 6);
  for (int q = 0; q < quads; ++q) {
    const EasyFontVertex *v = verts + q * 4;
    const int indices[6] = {0, 1, 2, 0, 2, 3};
    for (int idx = 0; idx < 6; ++idx) {
      const EasyFontVertex &src = v[indices[idx]];
      float px = x + src.x * scale;
      float py = y + src.y * scale;
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

  const GLsizei stride = static_cast<GLsizei>(6 * sizeof(float));
  glEnableVertexAttribArray(0);
  glVertexAttribPointer(0, 2, GL_FLOAT, GL_FALSE, stride, nullptr);
  glEnableVertexAttribArray(1);
  glVertexAttribPointer(1, 4, GL_FLOAT, GL_FALSE, stride,
                        reinterpret_cast<void *>(2 * sizeof(float)));

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

bool HudOverlay::isInitialized() const { return program_ != 0 && vao_ != 0 && vbo_ != 0; }

void HudOverlay::setOptions(const HudOverlayOptions &opts) {
  options_ = opts;
}

const HudOverlayOptions &HudOverlay::options() const { return options_; }

void HudOverlay::setLines(const std::vector<HudOverlayLine> &lines) {
  lines_ = lines;
}

void HudOverlay::addLine(const HudOverlayLine &line) { lines_.push_back(line); }

void HudOverlay::clearLines() { lines_.clear(); }

// Measure text by invoking stb_easy_font and scanning vertex extents.
glm::vec2 HudOverlay::measureText(const std::string &text, float scale) {
  if (text.empty()) {
    return glm::vec2(0.0f);
  }

  int estimated = static_cast<int>(text.size() * 270 + 16);
  std::vector<unsigned char> scratch(static_cast<std::size_t>(estimated));

  unsigned char rgba[4] = {255, 255, 255, 255};
  int quads = stb_easy_font_print(0.0f, 0.0f, const_cast<char *>(text.c_str()), rgba,
                                  scratch.data(), estimated);
  if (quads <= 0) {
    return glm::vec2(0.0f);
  }

  const EasyFontVertex *verts = reinterpret_cast<const EasyFontVertex *>(scratch.data());
  float minx = std::numeric_limits<float>::infinity();
  float miny = std::numeric_limits<float>::infinity();
  float maxx = -std::numeric_limits<float>::infinity();
  float maxy = -std::numeric_limits<float>::infinity();

  for (int q = 0; q < quads; ++q) {
    const EasyFontVertex *v = verts + q * 4;
    for (int i = 0; i < 4; ++i) {
      minx = std::min(minx, v[i].x);
      miny = std::min(miny, v[i].y);
      maxx = std::max(maxx, v[i].x);
      maxy = std::max(maxy, v[i].y);
    }
  }

  float width = (maxx - minx) * scale;
  float height = (maxy - miny) * scale;
  return glm::vec2(width, height);
}

void HudOverlay::rebuildVertices(int width, int height) {
  BH_ZONE();
  vertices_.clear();
  if (lines_.empty() || width <= 0 || height <= 0) {
    return;
  }

  float scale = std::max(options_.scale, 0.25f);
  const float baseLine = line_height(scale);
  const float lineStep = baseLine * options_.lineSpacing;

  // Precompute the starting Y depending on origin.
  float cursorY = 0.0f;
  if (options_.origin == HudOverlayOptions::Origin::TopLeft) {
    cursorY = options_.margin;
  } else {
    // Bottom-left origin: start such that last line sits at margin from bottom.
    cursorY = static_cast<float>(height) - options_.margin -
              baseLine * (static_cast<float>(lines_.size()) - 1) * options_.lineSpacing;
  }

  std::vector<unsigned char> scratch;
  for (const auto &line : lines_) {
    // Determine text extents to support alignment and background.
    glm::vec2 extents = measureText(line.text, scale);
    float x = 0.0f;
    if (options_.align == HudOverlayOptions::Align::Left) {
      x = options_.margin;
    } else if (options_.align == HudOverlayOptions::Align::Center) {
      x = static_cast<float>(width) * 0.5f - extents.x * 0.5f;
    } else { // Right
      x = static_cast<float>(width) - options_.margin - extents.x;
    }

    // Optional background box
    if (options_.drawBackground && line.background.a > 0.0f) {
      const float pad = 2.0f * scale;
      float bx0 = x - pad;
      float by0 = cursorY - pad;
      float bx1 = x + extents.x + pad;
      float by1 = cursorY + baseLine + pad;

      // Two triangles (6 vertices)
      glm::vec4 bg = line.background;
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
    append_text(vertices_, scratch, x, cursorY, scale, line.text, line.color);

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
  glBufferData(GL_ARRAY_BUFFER,
               static_cast<GLsizeiptr>(vertices_.size() * sizeof(float)),
               vertices_.data(), GL_DYNAMIC_DRAW);

  glDisable(GL_DEPTH_TEST);
  glEnable(GL_BLEND);
  glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

  const GLsizei vertexCount = static_cast<GLsizei>(vertices_.size() / 6);
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
  const float lineStep = line_height(scale);

  vertices_.clear();
  std::vector<unsigned char> scratch;
  for (const auto &line : lines) {
    append_text(vertices_, scratch, margin, cursorY, scale, line.text, line.color);
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
  glBufferData(GL_ARRAY_BUFFER,
               static_cast<GLsizeiptr>(vertices_.size() * sizeof(float)),
               vertices_.data(), GL_DYNAMIC_DRAW);

  glDisable(GL_DEPTH_TEST);
  glEnable(GL_BLEND);
  glBlendFunc(GL_SRC_ALPHA, GL_ONE_MINUS_SRC_ALPHA);

  const GLsizei vertexCount = static_cast<GLsizei>(vertices_.size() / 6);
  glDrawArrays(GL_TRIANGLES, 0, vertexCount);

  glBindVertexArray(0);
  glUseProgram(0);
}
