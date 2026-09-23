/**
 * @file gl_capabilities.cpp
 * @brief Extension and version-gated OpenGL feature queries.
 */

#include "render/gl_capabilities.h"

#include <string>

#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>

using namespace gl;

namespace blackhole {

bool hasExtension(const char *name) {
  GLint count = 0;
  glGetIntegerv(GL_NUM_EXTENSIONS, &count);
  for (GLint i = 0; i < count; ++i) {
    const char *ext =
        reinterpret_cast<const char *>(glGetStringi(GL_EXTENSIONS, static_cast<GLuint>(i)));
    if (ext != nullptr && std::string(ext) == name) {
      return true;
    }
  }
  return false;
}

bool supportsDrawId() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_shader_draw_parameters");
}

bool supportsMultiDrawIndirect() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs43 = (major > 4) || (major == 4 && minor >= 3);
  return versionIs43 || hasExtension("GL_ARB_multi_draw_indirect");
}

bool supportsIndirectCount() {
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  bool const versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  return versionIs46 || hasExtension("GL_ARB_indirect_parameters");
}

} // namespace blackhole
