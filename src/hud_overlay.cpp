#include "hud_overlay.h"

#include <algorithm>
#include <cstdint>

#include "shader.h"

#include <stb_easy_font.h>

namespace {

struct EasyFontVertex {
  float x;
  float y;
  float z;
  unsigned char color[4];
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
  if (program_ == 0) {
    program_ = createShaderProgram("shader/overlay_text.vert", "shader/overlay_text.frag");
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

void HudOverlay::render(int width, int height, float scale, float margin,
                        const std::vector<HudOverlayLine> &lines) {
  if (lines.empty() || width <= 0 || height <= 0) {
    return;
  }
  if (program_ == 0 || vao_ == 0 || vbo_ == 0) {
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
