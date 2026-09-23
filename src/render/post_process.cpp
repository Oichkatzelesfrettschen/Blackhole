/**
 * @file post_process.cpp
 * @brief Fullscreen post-processing pass implementation.
 */

#include "post_process.h"

#include <string>

#include <GLFW/glfw3.h>
#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

#include "../render.h"
#include "../shader.h"

using namespace gl;

namespace blackhole {

PostProcessPass::PostProcessPass(const std::string &fragShader) {
  this->program_ = createShaderProgram(std::string("shader/simple.vert"), fragShader);

  glUseProgram(this->program_);
  glUniform1i(glGetUniformLocation(program_, "texture0"), 0);
  glUseProgram(0);
}

void PostProcessPass::render(GLuint inputColorTexture, int width, int height,
                             GLuint destFramebuffer) const {
  if (quadVao_ == 0) {
    quadVao_ = createQuadVAO();
  }

  glBindFramebuffer(GL_FRAMEBUFFER, destFramebuffer);

  glDisable(GL_DEPTH_TEST);

  glClearColor(1.0f, 0.0f, 0.0f, 1.0f);
  glClear(GL_COLOR_BUFFER_BIT);

  glUseProgram(this->program_);
  glBindVertexArray(quadVao_);

  glUniform2f(glGetUniformLocation(this->program_, "resolution"), static_cast<float>(width),
              static_cast<float>(height));

  glUniform1f(glGetUniformLocation(this->program_, "time"), static_cast<float>(glfwGetTime()));

  glActiveTexture(GL_TEXTURE0);
  glBindTexture(GL_TEXTURE_2D, inputColorTexture);

  glDrawArrays(GL_TRIANGLES, 0, 6);

  glUseProgram(0);
}

} // namespace blackhole
