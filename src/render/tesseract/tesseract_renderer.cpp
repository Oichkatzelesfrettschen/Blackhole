/**
 * @file tesseract_renderer.cpp
 * @brief Instanced-ribbon GL pass for the speculative tesseract scene.
 */

#include "render/tesseract/tesseract_renderer.h"

#include <algorithm>
#include <array>
#include <cstddef>
#include <iostream>
#include <numeric>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/boolean.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include <glm/ext/matrix_clip_space.hpp>
#include <glm/ext/matrix_float3x3.hpp>
#include <glm/ext/matrix_float4x4.hpp>
#include <glm/ext/matrix_transform.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/gtc/matrix_access.hpp>
#include <glm/gtc/type_ptr.hpp>
#include <glm/trigonometric.hpp>

#include "hud_overlay.h"
#include "render/render_state.h"
#include "render/tesseract/so4.h"
#include "render/tesseract/tesseract_geometry.h"
#include "shader.h"

using namespace gl;

namespace blackhole {
namespace {

// Pieces per tesseract edge; enough that stereographic arcs read as curves.
constexpr std::size_t EDGE_SUBDIVISIONS = 24;
// Points per world-tube polyline; the lit-moment Gaussian spans several.
constexpr std::size_t TUBE_SAMPLES = 96;
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
  }
};

} // namespace

TesseractRenderer::~TesseractRenderer() {
  shutdown();
}

void TesseractRenderer::shutdown() {
  if (program_ != 0) {
    glDeleteProgram(program_);
    program_ = 0;
  }
  if (vbo_ != 0) {
    glDeleteBuffers(1, &vbo_);
    vbo_ = 0;
  }
  if (vao_ != 0) {
    glDeleteVertexArrays(1, &vao_);
    vao_ = 0;
  }
  if (fbo_ != 0) {
    glDeleteFramebuffers(1, &fbo_);
    fbo_ = 0;
  }
  instanceCount_ = 0;
  builtTimeSpan_ = -1.0f;
}

bool TesseractRenderer::reloadShaders() {
  if (program_ == 0) {
    return true;
  }
  // createShaderProgram throws const char* on compile or link failure and
  // std::string when a source file cannot be read.
  try {
    const GLuint fresh = createShaderProgram(std::string("shader/tesseract.vert"),
                                             std::string("shader/tesseract.frag"));
    glDeleteProgram(program_);
    program_ = fresh;
    std::cout << "[HotReload] Reloaded shader/tesseract.{vert,frag}\n";
    return true;
  } catch (const char *error) {
    std::cerr << "[HotReload] tesseract shaders kept: " << error << '\n';
  } catch (const std::string &error) {
    std::cerr << "[HotReload] tesseract shaders kept: " << error << '\n';
  }
  return false;
}

void TesseractRenderer::ensureResources(float timeSpan) {
  if (program_ == 0) {
    program_ = createShaderProgram(std::string("shader/tesseract.vert"),
                                   std::string("shader/tesseract.frag"));
  }
  if (fbo_ == 0) {
    glCreateFramebuffers(1, &fbo_);
  }
  if (vao_ == 0) {
    glCreateVertexArrays(1, &vao_);
    glCreateBuffers(1, &vbo_);
    constexpr auto stride = static_cast<GLsizei>(sizeof(tesseract::SegmentInstance));
    glVertexArrayVertexBuffer(vao_, 0, vbo_, 0, stride);
    glVertexArrayBindingDivisor(vao_, 0, 1);
    // Attributes 0..2 are the a, b, and meta vec4 members, 16 bytes apart.
    for (GLuint attrib = 0; attrib < 3; ++attrib) {
      glEnableVertexArrayAttrib(vao_, attrib);
      glVertexArrayAttribFormat(vao_, attrib, 4, GL_FLOAT, GL_FALSE,
                                attrib * static_cast<GLuint>(4 * sizeof(float)));
      glVertexArrayAttribBinding(vao_, attrib, 0);
    }
  }
  // The world-tube layout maps library time through T, so a new T rebuilds it.
  if (timeSpan != builtTimeSpan_) {
    tesseract::SceneSegmentOptions options;
    options.timeSpan = timeSpan;
    options.tubeSamples = TUBE_SAMPLES;
    options.edgeSubdivisions = EDGE_SUBDIVISIONS;
    const std::vector<tesseract::SegmentInstance> segments = tesseract::buildSceneSegments(options);
    glNamedBufferData(vbo_,
                      static_cast<GLsizeiptr>(segments.size() * sizeof(tesseract::SegmentInstance)),
                      segments.data(), GL_STATIC_DRAW);
    instanceCount_ = static_cast<GLsizei>(segments.size());
    builtTimeSpan_ = timeSpan;
  }
}

void TesseractRenderer::render(const TesseractFrameInputs &inputs) {
  if (inputs.targetTexture == 0 || inputs.width <= 0 || inputs.height <= 0) {
    return;
  }
  ensureResources(inputs.timeSpan);

  SavedGlState saved;
  saved.capture();

  glNamedFramebufferTexture(fbo_, GL_COLOR_ATTACHMENT0, inputs.targetTexture, 0);
  glBindFramebuffer(GL_FRAMEBUFFER, fbo_);
  glViewport(0, 0, inputs.width, inputs.height);
  glDisable(GL_DEPTH_TEST);
  // Deep-space background; alpha 1 marks every pixel as far for the scene
  // target's depth-in-alpha convention.
  glClearColor(0.004f, 0.005f, 0.012f, 1.0f);
  glClear(GL_COLOR_BUFFER_BIT);

  // Ribbons are emissive: radiance adds, destination alpha stays 1.
  glEnable(GL_BLEND);
  glBlendEquationSeparate(GL_FUNC_ADD, GL_FUNC_ADD);
  glBlendFuncSeparate(GL_ONE, GL_ONE, GL_ZERO, GL_ONE);

  glUseProgram(program_);
  glUniformMatrix4fv(uniformLocation(program_, "rotation4"), 1, GL_FALSE, inputs.rotation.data());
  glUniformMatrix4fv(uniformLocation(program_, "viewProjection"), 1, GL_FALSE,
                     glm::value_ptr(inputs.viewProjection));
  glUniform2f(uniformLocation(program_, "resolution"), static_cast<float>(inputs.width),
              static_cast<float>(inputs.height));
  glUniform1i(uniformLocation(program_, "projectionMode"), inputs.projectionMode);
  glUniform1f(uniformLocation(program_, "perspectiveDistance"), inputs.perspectiveDistance);
  glUniform1f(uniformLocation(program_, "sceneScale"), inputs.sceneScale);
  glUniform1f(uniformLocation(program_, "timeSpan"), inputs.timeSpan);
  glUniform1f(uniformLocation(program_, "litMoment"), inputs.litMoment);
  glUniform1f(uniformLocation(program_, "lineWidthPx"), inputs.lineWidthPx);
  glUniform1f(uniformLocation(program_, "litWidth"), inputs.litWidth);
  glUniform1f(uniformLocation(program_, "pulseTime"), inputs.pulseTime);
  glUniform1f(uniformLocation(program_, "pulseWidth"), inputs.pulseWidth);
  glUniform1i(uniformLocation(program_, "pulseEnabled"), inputs.pulseEnabled ? 1 : 0);
  glUniform1i(uniformLocation(program_, "pulseStrand"), inputs.pulseStrand);
  glUniform1f(uniformLocation(program_, "edgeIntensity"), inputs.edgeIntensity);
  glUniform1f(uniformLocation(program_, "strandIntensity"), inputs.strandIntensity);
  glUniform1f(uniformLocation(program_, "sliceIntensity"), inputs.sliceIntensity);

  glBindVertexArray(vao_);
  glDrawArraysInstanced(GL_TRIANGLES, 0, 6, instanceCount_);

  saved.restore();
}

SpeculativeLabelLayout layoutSpeculativeLabel(int renderWidth) {
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

  const float available =
      std::max(static_cast<float>(renderWidth) - (2.0f * SPECULATIVE_LABEL_MARGIN), 1.0f);
  // A line of unit-scale width w occupies (w + 4) * scale with its background pad.
  const auto fitScale = [available](const std::vector<std::string> &lines) {
    const float widest = std::accumulate(
        lines.begin(), lines.end(), 0.0f, [](float acc, const std::string &line) {
          return std::max(acc, HudOverlay::measureText(line, 1.0f).x);
        });
    return std::min(available / (widest + 4.0f), SPECULATIVE_LABEL_MAX_SCALE);
  };
  for (const auto &lines : candidates) {
    const float scale = fitScale(lines);
    if (scale >= SPECULATIVE_LABEL_WRAP_SCALE) {
      return {.lines = lines, .scale = scale};
    }
  }
  if (fitScale(candidates.back()) >= SPECULATIVE_LABEL_MIN_SCALE) {
    return {.lines = candidates.back(), .scale = fitScale(candidates.back())};
  }
  // Below the three-line minimum, wrap word by word at HudOverlay's scale
  // floor so every line fits; only a single word wider than the target
  // (under ~60 px) can still overflow.
  const float unitBudget = (available / SPECULATIVE_LABEL_MIN_SCALE) - 4.0f;
  std::vector<std::string> wrapped;
  std::string current;
  std::size_t pos = 0;
  while (pos < label.size()) {
    const std::size_t next = std::min(label.find(' ', pos), label.size());
    const std::string word(label.substr(pos, next - pos));
    const std::string candidate = current.empty() ? word : current + " " + word;
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

glm::mat4 tesseractViewProjection(const glm::mat3 &cameraBasis, float viewDistance, float fovDeg,
                                  float aspect) {
  const glm::vec3 forward = glm::column(cameraBasis, 2);
  const glm::vec3 up = glm::column(cameraBasis, 1);
  const glm::vec3 eye = -forward * viewDistance;
  const glm::mat4 view = glm::lookAt(eye, glm::vec3(0.0f), up);
  const glm::mat4 projection =
      glm::perspective(glm::radians(fovDeg), aspect, 0.05f, viewDistance * 4.0f);
  return projection * view;
}

void renderTesseractScene(RenderState &rs, const glm::mat3 &cameraBasis, float deltaSeconds,
                          std::optional<double> outputClockSeconds) {
  auto &tg = rs.tesseract;
  tg.timeSpan = std::max(tg.timeSpan, 0.5f);
  tg.litMoment = std::clamp(tg.litMoment, 0.0f, tg.timeSpan);
  tg.pulseNow = std::clamp(tg.pulseNow, 0.0f, tg.timeSpan);
  tg.pulsePast = std::clamp(tg.pulsePast, 0.0f, tg.pulseNow);
  tg.pulseStrand =
      std::clamp(tg.pulseStrand, 0, static_cast<int>(tesseract::bedroomFeatures().size()) - 1);

  const float pulseSpan = tg.pulseNow - tg.pulsePast;
  if (outputClockSeconds.has_value()) {
    const double seconds = tg.animate ? *outputClockSeconds : 0.0;
    const tesseract::TesseractMotion motion = tesseract::tesseractMotionAt(
        tg.leftRate, tg.rightRate, static_cast<double>(tg.resetPhase),
        static_cast<double>(tg.rotationSpeed), tg.pulseSpeed, pulseSpan, seconds);
    tg.orientation = motion.orientation;
    tg.pulseTravel = motion.pulseTravel;
    tg.orientationInitialized = true;
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
  }
  const tesseract::Mat4<double> rotation = tesseract::so4FromPair(tg.orientation);

  const float aspect = static_cast<float>(std::max(rs.targets.renderWidth, 1)) /
                       static_cast<float>(std::max(rs.targets.renderHeight, 1));

  TesseractFrameInputs inputs;
  inputs.targetTexture = rs.targets.texBlackhole;
  inputs.width = rs.targets.renderWidth;
  inputs.height = rs.targets.renderHeight;
  inputs.viewProjection = tesseractViewProjection(cameraBasis, tg.viewDistance, tg.fovDeg, aspect);
  inputs.rotation = tesseract::toColumnMajor(rotation);
  inputs.projectionMode =
      tg.projection == RenderState::TesseractGroup::Projection::Stereographic ? 1 : 0;
  inputs.perspectiveDistance = std::max(tg.perspectiveDistance, 2.1f);
  inputs.sceneScale = tg.sceneScale;
  inputs.timeSpan = tg.timeSpan;
  inputs.litMoment = tg.litMoment;
  inputs.litWidth = std::max(tg.litWidth, 0.01f);
  inputs.pulseTime = tg.pulseNow - tg.pulseTravel;
  inputs.pulseWidth = std::max(tg.pulseWidth, 0.01f);
  inputs.pulseEnabled = tg.pulseEnabled;
  inputs.pulseStrand = tg.pulseStrand;
  inputs.lineWidthPx = std::max(tg.lineWidthPx, 1.0f);
  inputs.edgeIntensity = tg.edgeIntensity;
  inputs.strandIntensity = tg.strandIntensity;
  inputs.sliceIntensity = tg.sliceIntensity;
  tg.renderer.render(inputs);
}

} // namespace blackhole
