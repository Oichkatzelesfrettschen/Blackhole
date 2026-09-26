/**
 * @file gl_compute_harness.h
 * @brief Offscreen GL 4.6 compute dispatch for tests of shipped GLSL.
 *
 * Tests compile a compute shader that #includes production shader modules,
 * dispatch it on a hidden 1x1 GLFW window, and read results back from an
 * SSBO. GLSL has no native include directive, so expandShaderIncludes()
 * inlines line-leading `#include "path"` directives recursively, resolving
 * each path against shader/include (BH_SHADER_INCLUDE_DIR) and then shader/.
 * Commented include lines stay untouched. Include guards inside the modules
 * handle repeated inclusion.
 */

#ifndef BLACKHOLE_TESTS_SUPPORT_GL_COMPUTE_HARNESS_H
#define BLACKHOLE_TESTS_SUPPORT_GL_COMPUTE_HARNESS_H

#include <cstddef>
#include <fstream>
#include <regex>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

#include <GLFW/glfw3.h>
#include <glbinding/gl/bitfield.h>
#include <glbinding/gl/enum.h>
#include <glbinding/gl/functions.h>
#include <glbinding/gl/types.h>
#include <glbinding/glbinding.h>

#ifndef BH_SHADER_INCLUDE_DIR
#error "BH_SHADER_INCLUDE_DIR must point at shader/include"
#endif

namespace bhtest {

inline std::string readShaderInclude(const std::string &relative) {
  const std::string includeDir = BH_SHADER_INCLUDE_DIR;
  for (const std::string &base : {includeDir, includeDir + "/.."}) {
    const std::ifstream file(base + "/" + relative);
    if (file) {
      std::ostringstream content;
      content << file.rdbuf();
      return content.str();
    }
  }
  throw std::runtime_error("cannot open GLSL include: " + relative);
}

inline std::string expandShaderIncludes(const std::string &source, int depth = 0) {
  if (depth > 16) {
    throw std::runtime_error("GLSL include nesting exceeds 16 levels");
  }
  static const std::regex includeRe(R"~(^[ \t]*#include[ \t]+"([^"]+)")~",
                                    std::regex::multiline);
  std::string out;
  std::sregex_iterator it(source.begin(), source.end(), includeRe);
  const std::sregex_iterator end;
  std::size_t last = 0;
  for (; it != end; ++it) {
    out.append(source, last, static_cast<std::size_t>(it->position()) - last);
    out += expandShaderIncludes(readShaderInclude((*it)[1].str()), depth + 1);
    last = static_cast<std::size_t>(it->position() + it->length());
  }
  out.append(source, last);
  return out;
}

inline gl::GLuint createComputeProgram(const std::string &rawSource) {
  using namespace gl;
  const std::string source = expandShaderIncludes(rawSource);
  const GLuint shader = glCreateShader(GL_COMPUTE_SHADER);
  const char *srcPtr = source.c_str();
  glShaderSource(shader, 1, &srcPtr, nullptr);
  glCompileShader(shader);

  GLint status = 0;
  glGetShaderiv(shader, GL_COMPILE_STATUS, &status);
  if (status == 0) {
    GLint length = 0;
    glGetShaderiv(shader, GL_INFO_LOG_LENGTH, &length);
    std::string log(static_cast<std::size_t>(length), '\0');
    glGetShaderInfoLog(shader, length, nullptr, log.data());
    glDeleteShader(shader);
    throw std::runtime_error("compute shader compilation failed:\n" + log);
  }

  const GLuint program = glCreateProgram();
  glAttachShader(program, shader);
  glLinkProgram(program);
  glGetProgramiv(program, GL_LINK_STATUS, &status);
  if (status == 0) {
    GLint length = 0;
    glGetProgramiv(program, GL_INFO_LOG_LENGTH, &length);
    std::string log(static_cast<std::size_t>(length), '\0');
    glGetProgramInfoLog(program, length, nullptr, log.data());
    glDeleteProgram(program);
    glDeleteShader(shader);
    throw std::runtime_error("compute program linking failed:\n" + log);
  }
  glDeleteShader(shader);
  return program;
}

/// Dispatch `groups` x 1 x 1 work groups and read back `count` floats.
inline std::vector<float> runComputeProgram(gl::GLuint program, gl::GLuint outputBuffer,
                                            std::size_t count, gl::GLuint groups = 1) {
  using namespace gl;
  glUseProgram(program);
  glDispatchCompute(groups, 1, 1);
  glMemoryBarrier(GL_SHADER_STORAGE_BARRIER_BIT);
  auto *ptr = static_cast<float *>(glMapNamedBufferRange(
      outputBuffer, 0, static_cast<GLsizeiptr>(sizeof(float) * count), GL_MAP_READ_BIT));
  if (ptr == nullptr) {
    throw std::runtime_error("glMapNamedBufferRange returned null");
  }
  std::vector<float> result(ptr, ptr + count);
  glUnmapNamedBuffer(outputBuffer);
  return result;
}

/// Hidden GL 4.6 core context owned for a test suite. available() is false
/// when no context can be created (headless CI), and tests then skip.
class HiddenGlContext {
public:
  HiddenGlContext() {
    if (glfwInit() == 0) {
      return;
    }
    glfwWindowHint(GLFW_CONTEXT_VERSION_MAJOR, 4);
    glfwWindowHint(GLFW_CONTEXT_VERSION_MINOR, 6);
    glfwWindowHint(GLFW_OPENGL_PROFILE, GLFW_OPENGL_CORE_PROFILE);
    glfwWindowHint(GLFW_VISIBLE, GLFW_FALSE);
    window_ = glfwCreateWindow(1, 1, "Blackhole GL test", nullptr, nullptr);
    if (window_ == nullptr) {
      glfwTerminate();
      return;
    }
    glfwMakeContextCurrent(window_);
    glbinding::initialize(glfwGetProcAddress);
  }
  HiddenGlContext(const HiddenGlContext &) = delete;
  HiddenGlContext &operator=(const HiddenGlContext &) = delete;
  HiddenGlContext(HiddenGlContext &&) = delete;
  HiddenGlContext &operator=(HiddenGlContext &&) = delete;
  ~HiddenGlContext() {
    if (window_ != nullptr) {
      glfwDestroyWindow(window_);
      glfwTerminate();
    }
  }
  [[nodiscard]] bool available() const { return window_ != nullptr; }

private:
  GLFWwindow *window_ = nullptr;
};

} // namespace bhtest

#endif // BLACKHOLE_TESTS_SUPPORT_GL_COMPUTE_HARNESS_H
