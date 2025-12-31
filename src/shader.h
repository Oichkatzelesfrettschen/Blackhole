/**
 * @file shader.h
 * @brief Utilities for compiling and linking GLSL shader programs.
 *
 * Features:
 *  - Reads shader files and supports an `#include "file"` directive (processed
 *    relative to the shader file's directory by default).
 *  - Compiles vertex/fragment/compute shaders and links them into programs.
 *  - Prints compilation/link logs to stderr and throws on failures.
 *
 * Note: all functions expect a valid OpenGL context and an initialized GL loader
 * (see `gl_loader.h`). On failure, the implementation throws a `const char*`.
 */

#pragma once

#include <string>
#include <filesystem>

#include "gl_loader.h"

/**
 * Create and link a shader program from a vertex and fragment shader file.
 * The function processes `#include` directives inside the shader source.
 *
 * The function throws a `const char*` on error (file missing, compilation or
 * link failure). On success it returns the GL program object (non-zero).
 */
GLuint createShaderProgram(const std::string &vertexShaderFile,
                           const std::string &fragmentShaderFile);

/**
 * Convenience overload accepting a filesystem path.
 */
inline GLuint createShaderProgram(const std::filesystem::path &vert,
                                  const std::filesystem::path &frag) {
  return createShaderProgram(vert.string(), frag.string());
}

/**
 * Create and link a compute shader program from a compute shader file.
 * Throws a `const char*` on failure. Returns the GL program object on success.
 */
GLuint createComputeProgram(const std::string &computeShaderFile);

/**
 * Convenience overload accepting a filesystem path.
 */
inline GLuint createComputeProgram(const std::filesystem::path &comp) {
  return createComputeProgram(comp.string());
}

/**
 * Set the directory that is used as a fallback base when resolving includes
 * and loading shader files. By default the implementation uses "shader/".
 * This is useful when working with custom shader layouts or unit tests.
 */
void setShaderBaseDir(const std::string &baseDir);
inline void setShaderBaseDir(const std::filesystem::path &p) { setShaderBaseDir(p.string()); }

/**
 * Get the current shader base directory used for resolving relative includes.
 */
const std::string &getShaderBaseDir();

