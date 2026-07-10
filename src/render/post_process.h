/**
 * @file post_process.h
 * @brief Fullscreen post-processing pass: one fragment shader applied to
 *        an input color texture over a shared fullscreen-quad VAO.
 */

#ifndef BLACKHOLE_RENDER_POST_PROCESS_H
#define BLACKHOLE_RENDER_POST_PROCESS_H

#include <string>

#include <glbinding/gl/types.h>

namespace blackhole {

class PostProcessPass {
private:
  gl::GLuint program_;
  // Lazily created on first render() so construction needs no VAO support;
  // shared across draws of this pass.
  mutable gl::GLuint quadVao_ = 0;

public:
  explicit PostProcessPass(const std::string &fragShader);

  void render(gl::GLuint inputColorTexture, int width, int height,
              gl::GLuint destFramebuffer = 0) const;
};

} // namespace blackhole

#endif // BLACKHOLE_RENDER_POST_PROCESS_H
