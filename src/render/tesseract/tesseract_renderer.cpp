/**
 * @file tesseract_renderer.cpp
 * @brief SDF-raymarch GL pass for the speculative tesseract scene.
 */

#include "render/tesseract/tesseract_renderer.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <chrono>
#include <cstddef>
#include <future>
#include <iostream>
#include <numeric>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include <glbinding/gl/boolean.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include <glm/common.hpp>
#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/vector_float2.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/geometric.hpp>
#include <glm/gtc/matrix_access.hpp>
#include <glm/gtc/type_ptr.hpp>
#include <glm/trigonometric.hpp>

#include "hud_overlay.h"
#include "input.h"
#include "render.h"
#include "render/render_state.h"
#include "render/tesseract/emanation_table.h"
#include "render/tesseract/so4.h"
#include "render/tesseract/tesseract_geometry.h"
#include "shader.h"

using namespace gl;

namespace blackhole {
namespace {

// Largest frame time one animation step consumes, in seconds.
constexpr float MAX_ANIMATION_STEP_S = 0.25f;

GLint uniformLocation(GLuint program, const char *name) {
  return glGetUniformLocation(program, name);
}

/**
 * Every piece of GL state the pass changes, restored after drawing: blend
 * enable, functions, and equations; depth-test enable; the viewport; the
 * vertex array; the read and draw framebuffer bindings, which
 * glBindFramebuffer(GL_FRAMEBUFFER) sets together; and the program.
 */
struct SavedGlState {
  GLboolean blendEnabled = GL_FALSE;
  GLboolean depthTestEnabled = GL_FALSE;
  std::array<GLint, 4> viewport{};
  GLint blendSrcRgb = 0;
  GLint blendDstRgb = 0;
  GLint blendSrcAlpha = 0;
  GLint blendDstAlpha = 0;
  GLint blendEquationRgb = 0;
  GLint blendEquationAlpha = 0;
  GLint vertexArray = 0;
  GLint drawFramebuffer = 0;
  GLint readFramebuffer = 0;
  GLint program = 0;
  GLint activeTexture = 0;
  GLint emanationBinding = 0;

  void capture() {
    blendEnabled = glIsEnabled(GL_BLEND);
    depthTestEnabled = glIsEnabled(GL_DEPTH_TEST);
    glGetIntegerv(GL_VIEWPORT, viewport.data());
    glGetIntegerv(GL_BLEND_SRC_RGB, &blendSrcRgb);
    glGetIntegerv(GL_BLEND_DST_RGB, &blendDstRgb);
    glGetIntegerv(GL_BLEND_SRC_ALPHA, &blendSrcAlpha);
    glGetIntegerv(GL_BLEND_DST_ALPHA, &blendDstAlpha);
    glGetIntegerv(GL_BLEND_EQUATION_RGB, &blendEquationRgb);
    glGetIntegerv(GL_BLEND_EQUATION_ALPHA, &blendEquationAlpha);
    glGetIntegerv(GL_VERTEX_ARRAY_BINDING, &vertexArray);
    glGetIntegerv(GL_DRAW_FRAMEBUFFER_BINDING, &drawFramebuffer);
    glGetIntegerv(GL_READ_FRAMEBUFFER_BINDING, &readFramebuffer);
    glGetIntegerv(GL_CURRENT_PROGRAM, &program);
    // The pass binds one texture unit; glBindTextureUnit leaves the active
    // unit alone, but reading a unit's binding goes through it.
    glGetIntegerv(GL_ACTIVE_TEXTURE, &activeTexture);
    glActiveTexture(static_cast<GLenum>(static_cast<int>(GL_TEXTURE0) + TESSERACT_EMANATION_UNIT));
    glGetIntegerv(GL_TEXTURE_BINDING_2D, &emanationBinding);
    glActiveTexture(static_cast<GLenum>(activeTexture));
  }

  void restore() const {
    glBlendFuncSeparate(static_cast<GLenum>(blendSrcRgb), static_cast<GLenum>(blendDstRgb),
                        static_cast<GLenum>(blendSrcAlpha), static_cast<GLenum>(blendDstAlpha));
    glBlendEquationSeparate(static_cast<GLenum>(blendEquationRgb),
                            static_cast<GLenum>(blendEquationAlpha));
    if (blendEnabled == GL_TRUE) {
      glEnable(GL_BLEND);
    } else {
      glDisable(GL_BLEND);
    }
    if (depthTestEnabled == GL_TRUE) {
      glEnable(GL_DEPTH_TEST);
    } else {
      glDisable(GL_DEPTH_TEST);
    }
    glViewport(viewport.at(0), viewport.at(1), viewport.at(2), viewport.at(3));
    glBindVertexArray(static_cast<GLuint>(vertexArray));
    glBindFramebuffer(GL_DRAW_FRAMEBUFFER, static_cast<GLuint>(drawFramebuffer));
    glBindFramebuffer(GL_READ_FRAMEBUFFER, static_cast<GLuint>(readFramebuffer));
    glUseProgram(static_cast<GLuint>(program));
    glBindTextureUnit(static_cast<GLuint>(TESSERACT_EMANATION_UNIT),
                      static_cast<GLuint>(emanationBinding));
  }
};

// Uploads the slice frame both passes march from (shader/include/tesseract_slice.glsl).
void bindSliceUniforms(GLuint program, const TesseractSliceFrame &slice, float cellSize) {
  std::array<float, 12> axes{};
  for (std::size_t c = 0; c < slice.axes.size(); ++c) {
    for (std::size_t r = 0; r < 4; ++r) {
      axes.at((4 * c) + r) = static_cast<float>(slice.axes.at(c).at(r));
    }
  }
  glUniform4fv(uniformLocation(program, "sliceAxes"), 3, axes.data());
  glUniform4f(uniformLocation(program, "eyeSlice"), static_cast<float>(slice.eye[0]),
              static_cast<float>(slice.eye[1]), static_cast<float>(slice.eye[2]),
              static_cast<float>(slice.eye[3]));
  glUniform1f(uniformLocation(program, "cellSize"), cellSize);
  glUniform1f(uniformLocation(program, "latticePeriodCells"),
              static_cast<float>(TESSERACT_LATTICE_PERIOD_CELLS));
}

} // namespace

TesseractRenderer::~TesseractRenderer() {
  shutdown();
}

void TesseractRenderer::shutdown() {
  if (program_ != 0) {
    glDeleteProgram(program_);
    program_ = 0;
  }
  if (panesProgram_ != 0) {
    glDeleteProgram(panesProgram_);
    panesProgram_ = 0;
  }
  if (vao_ != 0) {
    glDeleteVertexArrays(1, &vao_);
    vao_ = 0;
  }
  if (fbo_ != 0) {
    glDeleteFramebuffers(1, &fbo_);
    fbo_ = 0;
  }
  if (pendingTable_.valid()) {
    pendingTable_.wait();
    pendingTable_ = {};
  }
  pendingStrut_ = 0;
  if (emanationTexture_ != 0) {
    glDeleteTextures(1, &emanationTexture_);
    emanationTexture_ = 0;
  }
  emanationStrut_ = 0;
  emanationDmz_ = 0;
  emanationFill_ = 0.0f;
}

bool TesseractRenderer::reloadShaders() {
  if (program_ == 0) {
    return true;
  }
  // createShaderProgram throws const char* on compile or link failure and
  // std::string when a source file cannot be read. Each program keeps its last
  // working build when its own source fails.
  bool reloaded = true;
  const auto reload = [&reloaded](GLuint &program, const char *vertex, const char *fragment) {
    try {
      const GLuint fresh = createShaderProgram(std::string(vertex), std::string(fragment));
      glDeleteProgram(program);
      program = fresh;
      std::cout << "[HotReload] Reloaded " << fragment << '\n';
    } catch (const char *error) {
      std::cerr << "[HotReload] " << fragment << " kept: " << error << '\n';
      reloaded = false;
    } catch (const std::string &error) {
      std::cerr << "[HotReload] " << fragment << " kept: " << error << '\n';
      reloaded = false;
    }
  };
  reload(program_, "shader/simple.vert", "shader/tesseract.frag");
  if (panesProgram_ != 0) {
    reload(panesProgram_, "shader/simple.vert", "shader/tesseract_panes.frag");
  }
  return reloaded;
}

bool TesseractRenderer::isLlvmpipe() {
  if (!llvmpipeChecked_) {
    llvmpipeChecked_ = true;
    const auto *rendererString = reinterpret_cast<const char *>(glGetString(GL_RENDERER));
    llvmpipeDetected_ =
        rendererString != nullptr && std::string_view(rendererString).contains("llvmpipe");
  }
  return llvmpipeDetected_;
}

void TesseractRenderer::ensureResources() {
  if (program_ == 0) {
    program_ = createShaderProgram(std::string("shader/simple.vert"),
                                   std::string("shader/tesseract.frag"));
  }
  if (panesProgram_ == 0) {
    panesProgram_ = createShaderProgram(std::string("shader/simple.vert"),
                                        std::string("shader/tesseract_panes.frag"));
  }
  if (fbo_ == 0) {
    glCreateFramebuffers(1, &fbo_);
  }
  if (vao_ == 0) {
    vao_ = createQuadVAO();
  }
}

void TesseractRenderer::bakeEmanation(int strut, bool blocking) {
  if (emanationTexture_ != 0 && strut == emanationStrut_) {
    return;
  }
  if (pendingTable_.valid()) {
    const bool ready =
        pendingTable_.wait_for(std::chrono::seconds(0)) == std::future_status::ready;
    if (ready || blocking || emanationTexture_ == 0) {
      const int builtStrut = pendingStrut_;
      const tesseract::EmanationTable built = pendingTable_.get();
      if (builtStrut == strut) {
        uploadEmanation(strut, built);
        return;
      }
    } else {
      // One build runs at a time; a strut requested meanwhile starts after it.
      return;
    }
  }
  if (blocking || emanationTexture_ == 0) {
    uploadEmanation(strut, tesseract::createStruttedEt(TESSERACT_EMANATION_LEVEL, strut));
    return;
  }
  pendingStrut_ = strut;
  pendingTable_ = std::async(std::launch::async, [strut] {
    return tesseract::createStruttedEt(TESSERACT_EMANATION_LEVEL, strut);
  });
}

void TesseractRenderer::uploadEmanation(int strut, const tesseract::EmanationTable &table) {
  if (emanationTexture_ == 0) {
    glCreateTextures(GL_TEXTURE_2D, 1, &emanationTexture_);
    glTextureStorage2D(emanationTexture_, 1, GL_R16I, TESSERACT_EMANATION_SIZE,
                       TESSERACT_EMANATION_SIZE);
    // Integer textures do not filter; the shader reads them with texelFetch.
    glTextureParameteri(emanationTexture_, GL_TEXTURE_MIN_FILTER, static_cast<GLint>(GL_NEAREST));
    glTextureParameteri(emanationTexture_, GL_TEXTURE_MAG_FILTER, static_cast<GLint>(GL_NEAREST));
  }
  GLint unpackAlignment = 4;
  glGetIntegerv(GL_UNPACK_ALIGNMENT, &unpackAlignment);
  glPixelStorei(GL_UNPACK_ALIGNMENT, 2);
  glTextureSubImage2D(emanationTexture_, 0, 0, 0, TESSERACT_EMANATION_SIZE,
                      TESSERACT_EMANATION_SIZE, GL_RED_INTEGER, GL_SHORT, table.value.data());
  glPixelStorei(GL_UNPACK_ALIGNMENT, unpackAlignment);
  emanationStrut_ = strut;
  emanationDmz_ = table.dmzCount;
  emanationWalk_ = tesseract::xorTripleWalk(table, tesseract::EMANATION_WALK_LENGTH);
  emanationWalkValues_.resize(emanationWalk_.size());
  std::ranges::transform(emanationWalk_, emanationWalkValues_.begin(),
                         [&table](const tesseract::WalkCell &cell) {
                           return table.at(cell.row, cell.col);
                         });
  emanationFill_ = table.totalPossible == 0
                       ? 0.0f
                       : static_cast<float>(table.dmzCount) / static_cast<float>(table.totalPossible);
}

TesseractRenderer::EmanationTrail TesseractRenderer::updateEmanationTrail(
    const TesseractFrameInputs &inputs) {
  EmanationTrail trail;
  emanationTrail_.clear();
  if (!inputs.emanationWalk || emanationWalk_.empty()) {
    return trail;
  }
  const auto length = static_cast<long long>(emanationWalk_.size());
  for (int i = 0; i < TESSERACT_EMANATION_TRAIL; ++i) {
    const long long step = static_cast<long long>(inputs.emanationWalkStep) - i;
    const auto index = static_cast<std::size_t>(((step % length) + length) % length);
    const tesseract::WalkCell cell = emanationWalk_[index];
    emanationTrail_.push_back(cell);
    // The uniform holds level-10 table indices, row first.
    const std::size_t slot = 2 * static_cast<std::size_t>(i);
    trail.cells.at(slot) = cell.row;
    trail.cells.at(slot + 1) = cell.col;
    if (i == 0) {
      trail.leadValue = emanationWalkValues_[index];
    }
  }
  return trail;
}

void TesseractRenderer::drawEmanationPanes(const TesseractFrameInputs &inputs,
                                           const TesseractSliceFrame &slice,
                                           const EmanationTrail &trail) {
  // Panes add light over the lattice already in the target.
  glEnable(GL_BLEND);
  glBlendFunc(GL_ONE, GL_ONE);
  glBlendEquation(GL_FUNC_ADD);
  glUseProgram(panesProgram_);
  glUniform2f(uniformLocation(panesProgram_, "resolution"), static_cast<float>(inputs.width),
              static_cast<float>(inputs.height));
  glUniformMatrix3fv(uniformLocation(panesProgram_, "cameraBasis"), 1, GL_FALSE,
                     glm::value_ptr(inputs.cameraBasis));
  glUniform1f(uniformLocation(panesProgram_, "fovScale"), inputs.fovScale);
  bindSliceUniforms(panesProgram_, slice, inputs.cellSize);
  glUniform1f(uniformLocation(panesProgram_, "strandGlow"), inputs.strandGlow);
  glUniform1f(uniformLocation(panesProgram_, "fogDensity"), inputs.fogDensity);
  glUniform1f(uniformLocation(panesProgram_, "emanationGain"), inputs.emanationGain);
  glUniform1f(uniformLocation(panesProgram_, "emanationFill"), emanationFill_);
  glUniform1i(uniformLocation(panesProgram_, "emanationMinLevel"),
              inputs.emanationNesting ? tesseract::minLevelForStrut(emanationStrut_)
                                      : TESSERACT_EMANATION_LEVEL);
  glUniform2iv(uniformLocation(panesProgram_, "emanationTrail"), TESSERACT_EMANATION_TRAIL,
               trail.cells.data());
  glUniform1i(uniformLocation(panesProgram_, "emanationTrailCount"),
              static_cast<GLint>(emanationTrail_.size()));
  glUniform1f(uniformLocation(panesProgram_, "emanationTrailPhase"), inputs.emanationWalkPhase);
  glDrawArrays(GL_TRIANGLES, 0, 6);
}

void TesseractRenderer::render(const TesseractFrameInputs &inputs) {
  if (inputs.targetTexture == 0 || inputs.width <= 0 || inputs.height <= 0) {
    return;
  }
  // Capture state before ensureResources(): createQuadVAO's classic (non-DSA)
  // glGenVertexArrays/glBindVertexArray path changes the current VAO binding
  // on the pass's first call, so capturing after it would save that VAO as
  // the caller's own and restore() would never rebind the caller's real one.
  SavedGlState saved;
  saved.capture();

  ensureResources();
  bakeEmanation(std::clamp(inputs.emanationStrut, 1, TESSERACT_EMANATION_MAX_STRUT),
                inputs.emanationBakeBlocking);
  glBindTextureUnit(static_cast<GLuint>(TESSERACT_EMANATION_UNIT), emanationTexture_);

  glNamedFramebufferTexture(fbo_, GL_COLOR_ATTACHMENT0, inputs.targetTexture, 0);
  glBindFramebuffer(GL_FRAMEBUFFER, fbo_);
  glViewport(0, 0, inputs.width, inputs.height);
  glDisable(GL_DEPTH_TEST);
  glDisable(GL_BLEND);

  glUseProgram(program_);
  glUniform2f(uniformLocation(program_, "resolution"), static_cast<float>(inputs.width),
              static_cast<float>(inputs.height));
  glUniformMatrix3fv(uniformLocation(program_, "cameraBasis"), 1, GL_FALSE,
                     glm::value_ptr(inputs.cameraBasis));
  glUniform1f(uniformLocation(program_, "fovScale"), inputs.fovScale);
  const TesseractSliceFrame slice = tesseractSliceFrame(inputs.rotation, inputs.sceneScale,
                                                        inputs.cellSize, inputs.eye, inputs.drift);
  bindSliceUniforms(program_, slice, inputs.cellSize);
  const double period = std::max(static_cast<double>(inputs.corridorPeriod), 1e-3);
  const double depth = static_cast<double>(inputs.eye.z) + inputs.drift.z +
                       (TESSERACT_LATTICE_OFFSET_CELLS[2] * static_cast<double>(inputs.cellSize));
  glUniform1f(uniformLocation(program_, "corridorPeriod"), inputs.corridorPeriod);
  glUniform1f(uniformLocation(program_, "eyeDepth"),
              static_cast<float>(depth - (period * std::floor(depth / period))));
  glUniform1f(uniformLocation(program_, "nowDepth"), inputs.nowDepth);
  glUniform1f(uniformLocation(program_, "nowWidth"), inputs.nowWidth);
  glUniform1f(uniformLocation(program_, "pulseDepth"), inputs.pulseDepth);
  glUniform1f(uniformLocation(program_, "pulseWidth"), inputs.pulseWidth);
  glUniform1i(uniformLocation(program_, "pulseEnabled"), inputs.pulseEnabled ? 1 : 0);
  glUniform1f(uniformLocation(program_, "strandGlow"), inputs.strandGlow);
  glUniform1f(uniformLocation(program_, "fogDensity"), inputs.fogDensity);
  glUniform1i(uniformLocation(program_, "qualityTier"), inputs.qualityTier);
  const EmanationTrail trail = updateEmanationTrail(inputs);
  glUniform1i(uniformLocation(program_, "pulseTintEnabled"),
              inputs.emanationEnabled && !emanationTrail_.empty() ? 1 : 0);
  glUniform1i(uniformLocation(program_, "emanationLeadValue"), trail.leadValue);

  glBindVertexArray(vao_);
  glDrawArrays(GL_TRIANGLES, 0, 6);

  if (inputs.emanationEnabled) {
    drawEmanationPanes(inputs, slice, trail);
  }

  saved.restore();
}

SpeculativeLabelLayout layoutSpeculativeLabel(int renderWidth, int renderHeight) {
  const std::string_view label = TESSERACT_SPECULATIVE_LABEL;
  const std::size_t citationEnd = label.find(": ") + 1;
  const std::size_t citationStart = label.find(" (");
  const std::string head(label.substr(0, citationStart));
  const std::string citation(label.substr(citationStart + 1, citationEnd - citationStart - 1));
  const std::string verdict(label.substr(citationEnd + 1));
  const std::array<std::vector<std::string>, 3> candidates = {
      std::vector<std::string>{std::string(label)},
      std::vector<std::string>{head + " " + citation, verdict},
      std::vector<std::string>{head, citation, verdict}};

  const float availableWidth =
      std::max(static_cast<float>(renderWidth) - (2.0f * SPECULATIVE_LABEL_MARGIN), 1.0f);
  const float availableHeight =
      std::max(static_cast<float>(renderHeight) - (2.0f * SPECULATIVE_LABEL_MARGIN), 1.0f);
  const float unitLineHeight = HudOverlay::lineHeight(1.0f);
  // At scale s a line of unit width w occupies (w + 4) * s across, and n
  // lines occupy (n * lineHeight(1) + 4) * s down, pad included.
  const auto fitScale = [availableWidth, availableHeight,
                         unitLineHeight](const std::vector<std::string> &lines) {
    const float widest =
        std::accumulate(lines.begin(), lines.end(), 0.0f, [](float acc, const std::string &line) {
          return std::max(acc, HudOverlay::measureText(line, 1.0f).x);
        });
    const float blockHeight = (static_cast<float>(lines.size()) * unitLineHeight) + 4.0f;
    return std::min({availableWidth / (widest + 4.0f), availableHeight / blockHeight,
                     SPECULATIVE_LABEL_MAX_SCALE});
  };
  for (const auto &lines : candidates) {
    const float scale = fitScale(lines);
    if (scale >= SPECULATIVE_LABEL_WRAP_SCALE) {
      return {.lines = lines, .scale = scale};
    }
  }
  // No phrase break reaches the wrap scale: take the one that fits largest,
  // fewer lines first on a tie.
  const std::vector<std::string> *best = &candidates.front();
  float bestScale = fitScale(*best);
  for (const auto &lines : candidates) {
    const float scale = fitScale(lines);
    if (scale > bestScale) {
      best = &lines;
      bestScale = scale;
    }
  }
  if (bestScale >= SPECULATIVE_LABEL_MIN_SCALE) {
    return {.lines = *best, .scale = bestScale};
  }
  // Below that, wrap word by word at HudOverlay's scale floor. Every line
  // fits once the target is SPECULATIVE_LABEL_MIN_TARGET_WIDTH wide and the
  // block fits once it is SPECULATIVE_LABEL_MIN_TARGET_HEIGHT tall.
  const float unitBudget = (availableWidth / SPECULATIVE_LABEL_MIN_SCALE) - 4.0f;
  std::vector<std::string> wrapped;
  std::string current;
  std::size_t pos = 0;
  while (pos < label.size()) {
    const std::size_t next = std::min(label.find(' ', pos), label.size());
    const std::string word(label.substr(pos, next - pos));
    std::string candidate = current;
    if (!candidate.empty()) {
      candidate += ' ';
    }
    candidate += word;
    if (!current.empty() && HudOverlay::measureText(candidate, 1.0f).x > unitBudget) {
      wrapped.push_back(current);
      current = word;
    } else {
      current = candidate;
    }
    pos = next + 1;
  }
  if (!current.empty()) {
    wrapped.push_back(current);
  }
  return {.lines = wrapped, .scale = SPECULATIVE_LABEL_MIN_SCALE};
}

float tesseractBoundingRadius(bool stereographic, float sceneScale, float perspectiveDistance) {
  if (stereographic) {
    const float fadeEnd = tesseract::STEREOGRAPHIC_FADE_END;
    return sceneScale * std::sqrt((2.0f - fadeEnd) / fadeEnd);
  }
  const float d = std::max(perspectiveDistance, TESSERACT_MIN_PERSPECTIVE_DISTANCE);
  return sceneScale * 2.0f * d / std::sqrt((d * d) - 4.0f);
}

TesseractFraming tesseractFraming(float viewDistance, float fovDeg, float boundingRadius,
                                  float aspect,
                                  const std::optional<TesseractRecordCamera> &record) {
  if (!record.has_value()) {
    return {.viewDistance = viewDistance, .fovDeg = fovDeg};
  }
  const float fov = std::clamp(record->fovDeg, TESSERACT_MIN_FOV_DEG, TESSERACT_MAX_FOV_DEG);
  const float verticalTan = std::tan(glm::radians(fov) * 0.5f);
  const glm::vec2 halfTan(aspect * verticalTan, verticalTan);
  const glm::vec2 center =
      glm::min(glm::abs(record->focusTangent), TESSERACT_RECORD_FILL * halfTan);
  const float centerNorm = std::sqrt(1.0f + glm::dot(center, center));
  // Per axis: the silhouette's outer edge reaches tangent
  // E = |c| + k (T - |c|) at the distance that axis needs.
  const auto axisDistance = [&](float c, float t) {
    const float edge = c + (TESSERACT_RECORD_FILL * (t - c));
    const float halfAngle = std::atan(edge) - std::atan(c);
    return boundingRadius / std::sin(halfAngle) * centerNorm / std::sqrt(1.0f + (c * c));
  };
  const float distance =
      std::max(axisDistance(center.x, halfTan.x), axisDistance(center.y, halfTan.y));
  return {.viewDistance = std::max(distance, TESSERACT_MIN_VIEW_DISTANCE), .fovDeg = fov};
}

float tesseractZoom(float viewDistance, float zoomDelta) {
  const float zoomed = viewDistance + (zoomDelta * viewDistance / K_ZOOM_RATE_REFERENCE_DISTANCE);
  return std::clamp(zoomed, TESSERACT_MIN_VIEW_DISTANCE, TESSERACT_MAX_VIEW_DISTANCE);
}

float tesseractViewDistanceAfterInput(float viewDistance, float zoomDelta, bool cameraReset) {
  return cameraReset ? TESSERACT_DEFAULT_VIEW_DISTANCE : tesseractZoom(viewDistance, zoomDelta);
}

glm::mat4 tesseractView(const glm::mat3 &cameraBasis, const glm::vec3 &focusDirection,
                        float viewDistance) {
  const glm::vec3 forward = glm::column(cameraBasis, 2);
  const glm::vec3 up = glm::column(cameraBasis, 1);
  const glm::vec3 eye = -focusDirection * viewDistance;
  return glm::lookAt(eye, eye + forward, up);
}

glm::vec2 tesseractFocusTangent(const glm::mat3 &cameraBasis, const glm::vec3 &focusDirection) {
  const float forward =
      std::max(glm::dot(focusDirection, glm::column(cameraBasis, 2)), TESSERACT_MIN_FOCUS_COSINE);
  return glm::vec2(glm::dot(focusDirection, glm::column(cameraBasis, 0)),
                   glm::dot(focusDirection, glm::column(cameraBasis, 1))) /
         forward;
}

glm::mat4 tesseractViewProjection(const glm::mat3 &cameraBasis, const glm::vec3 &focusDirection,
                                  float viewDistance, float fovDeg, float aspect) {
  const glm::mat4 view = tesseractView(cameraBasis, focusDirection, viewDistance);
  const glm::mat4 projection =
      glm::infinitePerspective(glm::radians(fovDeg), aspect, TESSERACT_NEAR_PLANE);
  return projection * view;
}

TesseractSliceFrame tesseractSliceFrame(const std::array<float, 16> &rotation, float sceneScale,
                                        float cellSize, const glm::vec3 &eye,
                                        const glm::dvec3 &drift) {
  using Vec4 = std::array<double, 4>;
  const auto dot = [](const Vec4 &a, const Vec4 &b) {
    return (a[0] * b[0]) + (a[1] * b[1]) + (a[2] * b[2]) + (a[3] * b[3]);
  };
  const auto axpy = [](const Vec4 &y, double a, const Vec4 &x) {
    return Vec4{y[0] + (a * x[0]), y[1] + (a * x[1]), y[2] + (a * x[2]), y[3] + (a * x[3])};
  };
  const auto normalized = [&dot](const Vec4 &v) {
    const double inverse = 1.0 / std::sqrt(dot(v, v));
    return Vec4{v[0] * inverse, v[1] * inverse, v[2] * inverse, v[3] * inverse};
  };
  const double blend = std::clamp(0.10 * static_cast<double>(sceneScale), 0.0, 0.6);
  std::array<Vec4, 3> blended{};
  for (std::size_t c = 0; c < blended.size(); ++c) {
    for (std::size_t r = 0; r < 4; ++r) {
      const double identity = r == c ? 1.0 : 0.0;
      blended.at(c).at(r) =
          identity + (blend * (static_cast<double>(rotation.at((4 * c) + r)) - identity));
    }
  }
  TesseractSliceFrame slice;
  slice.axes[0] = normalized(blended[0]);
  slice.axes[1] = normalized(axpy(blended[1], -dot(blended[1], slice.axes[0]), slice.axes[0]));
  const Vec4 third = axpy(blended[2], -dot(blended[2], slice.axes[0]), slice.axes[0]);
  slice.axes[2] = normalized(axpy(third, -dot(third, slice.axes[1]), slice.axes[1]));

  const auto cell = static_cast<double>(cellSize);
  const std::array<double, 3> local{
      static_cast<double>(eye.x) + (TESSERACT_LATTICE_OFFSET_CELLS[0] * cell),
      static_cast<double>(eye.y) + (TESSERACT_LATTICE_OFFSET_CELLS[1] * cell),
      static_cast<double>(eye.z) + (TESSERACT_LATTICE_OFFSET_CELLS[2] * cell)};
  Vec4 point{drift.x, drift.y, drift.z, TESSERACT_SLICE_W_CELLS * cell};
  for (std::size_t c = 0; c < local.size(); ++c) {
    point = axpy(point, local.at(c), slice.axes.at(c));
  }
  const double period = static_cast<double>(TESSERACT_LATTICE_PERIOD_CELLS) * cell;
  for (std::size_t r = 0; r < 3; ++r) {
    point.at(r) -= period * std::floor((point.at(r) / period) + 0.5);
  }
  slice.eye = point;
  return slice;
}

int tesseractEmanationStrut(bool ride, double clockSeconds, float dwellSeconds, int manualStrut) {
  if (!ride) {
    return std::clamp(manualStrut, 1, TESSERACT_EMANATION_MAX_STRUT);
  }
  static const std::vector<int> skyRide = tesseract::skyRegimeStruts(TESSERACT_EMANATION_LEVEL);
  const double dwell = std::max(static_cast<double>(dwellSeconds), 0.1);
  const auto step = static_cast<long long>(std::floor(std::max(clockSeconds, 0.0) / dwell));
  return skyRide[static_cast<std::size_t>(step % static_cast<long long>(skyRide.size()))];
}

void advanceTesseractMotion(RenderState &rs, float deltaSeconds,
                            const std::optional<TesseractRecordFrame> &record) {
  auto &tg = rs.tesseract;
  tg.timeSpan = std::max(tg.timeSpan, 0.5f);
  tg.cellSize = std::max(tg.cellSize, 0.3f);
  tg.litMoment = std::clamp(tg.litMoment, 0.0f, tg.timeSpan);
  tg.pulseNow = std::clamp(tg.pulseNow, 0.0f, tg.timeSpan);
  tg.pulsePast = std::clamp(tg.pulsePast, 0.0f, tg.pulseNow);

  const float pulseSpan = tg.pulseNow - tg.pulsePast;
  if (record.has_value()) {
    const double seconds = tg.animate ? record->outputClockSeconds : 0.0;
    const tesseract::TesseractMotion motion = tesseract::tesseractMotionAt(
        tg.leftRate, tg.rightRate, static_cast<double>(tg.resetPhase),
        static_cast<double>(tg.rotationSpeed), tg.pulseSpeed, pulseSpan, seconds);
    tg.orientation = motion.orientation;
    tg.pulseTravel = motion.pulseTravel;
    tg.orientationInitialized = true;
    tg.driftDistance = static_cast<double>(tg.driftSpeed) * seconds;
    tg.emanationClock = seconds;
  } else {
    if (!tg.orientationInitialized) {
      const tesseract::TesseractMotion reset = tesseract::tesseractMotionAt(
          tg.leftRate, tg.rightRate, static_cast<double>(tg.resetPhase), 0.0, 0.0f, pulseSpan, 0.0);
      tg.orientation = reset.orientation;
      tg.pulseTravel = reset.pulseTravel;
      tg.orientationInitialized = true;
    }
    // A stalled frame (window drag, breakpoint) advances by at most MAX_STEP.
    const float step = tg.animate ? std::clamp(deltaSeconds, 0.0f, MAX_ANIMATION_STEP_S) : 0.0f;
    tg.orientation = tesseract::advanceOrientation(tg.orientation, tg.leftRate, tg.rightRate,
                                                   static_cast<double>(step) *
                                                       static_cast<double>(tg.rotationSpeed));
    tg.pulseTravel = tesseract::advancePulseTravel(tg.pulseTravel, step * tg.pulseSpeed, pulseSpan);
    tg.driftDistance += static_cast<double>(step) * static_cast<double>(tg.driftSpeed);
    tg.emanationClock += static_cast<double>(step);
  }
}

void renderTesseractScene(RenderState &rs, const glm::mat3 &cameraBasis,
                          const glm::vec3 &focusDirection, float deltaSeconds,
                          const std::optional<TesseractRecordFrame> &record) {
  advanceTesseractMotion(rs, deltaSeconds, record);
  auto &tg = rs.tesseract;
  const tesseract::Mat4<double> rotation = tesseract::so4FromPair(tg.orientation);

  const float aspect = static_cast<float>(std::max(rs.targets.renderWidth, 1)) /
                       static_cast<float>(std::max(rs.targets.renderHeight, 1));

  if (!tg.qualityUserSet && tg.renderer.isLlvmpipe()) {
    tg.quality = RenderState::TesseractGroup::Quality::Sparse;
  }

  TesseractFrameInputs inputs;
  inputs.targetTexture = rs.targets.texBlackhole;
  inputs.width = rs.targets.renderWidth;
  inputs.height = rs.targets.renderHeight;
  const bool stereographic =
      tg.projection == RenderState::TesseractGroup::Projection::Stereographic;
  const TesseractFraming framing = tesseractFraming(
      tg.viewDistance, tg.fovDeg,
      tesseractBoundingRadius(stereographic, tg.sceneScale, tg.perspectiveDistance), aspect,
      record.has_value() ? std::optional<TesseractRecordCamera>(record->camera) : std::nullopt);
  // Eye placement mirrors tesseractView, with a forward drift added so the
  // default view floats through the corridor instead of orbiting a static
  // object (Cooper floats through the tesseract rather than around it). A
  // recorded frame's camera is fixed, so its drift is the straight path; an
  // interactive frame adds its own drift along its own forward.
  const glm::dvec3 forward(glm::column(cameraBasis, 2));
  if (record.has_value()) {
    tg.driftOffset = forward * tg.driftDistance;
  } else {
    tg.driftOffset += forward * (tg.driftDistance - tg.driftApplied);
  }
  tg.driftApplied = tg.driftDistance;
  inputs.eye = -focusDirection * framing.viewDistance;
  inputs.drift = tg.driftOffset;
  inputs.cameraBasis = cameraBasis;
  inputs.fovScale = std::tan(glm::radians(framing.fovDeg) * 0.5f);
  inputs.rotation = tesseract::toColumnMajor(rotation);
  inputs.projectionMode = stereographic ? 1 : 0;
  inputs.perspectiveDistance = std::max(tg.perspectiveDistance, TESSERACT_MIN_PERSPECTIVE_DISTANCE);
  inputs.sceneScale = tg.sceneScale;
  inputs.corridorPeriod = tg.timeSpan;
  inputs.cellSize = tg.cellSize;
  inputs.nowDepth = tg.litMoment;
  inputs.nowWidth = std::max(tg.litWidth, 0.01f);
  inputs.pulseDepth = tg.pulseNow - tg.pulseTravel;
  inputs.pulseWidth = std::max(tg.pulseWidth, 0.01f);
  inputs.pulseEnabled = tg.pulseEnabled;
  inputs.strandGlow = std::max(tg.strandGlow, 0.0f);
  inputs.fogDensity = std::max(tg.fogDensity, 0.0f);
  inputs.qualityTier = static_cast<int>(tg.quality);
  inputs.emanationEnabled = tg.emanationEnabled;
  inputs.emanationStrut = tesseractEmanationStrut(tg.emanationRide, tg.emanationClock,
                                                  tg.emanationDwell, tg.emanationStrut);
  inputs.emanationGain = std::max(tg.emanationGain, 0.0f);
  inputs.emanationNesting = tg.emanationNesting;
  inputs.emanationWalk = tg.emanationWalk;
  const float walkPeriod = std::max(tg.emanationWalkPeriod, 0.05f);
  const double walkClock = std::max(tg.emanationClock, 0.0) / static_cast<double>(walkPeriod);
  inputs.emanationWalkStep = static_cast<int>(std::floor(walkClock));
  inputs.emanationWalkPhase = static_cast<float>(walkClock - std::floor(walkClock));
  inputs.emanationBakeBlocking = record.has_value();
  tg.renderer.render(inputs);
}

} // namespace blackhole
