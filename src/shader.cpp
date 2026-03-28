/**
 * @file shader.cpp
 * @brief Implementation of GLSL shader compilation and program linking utilities.
 *
 * Handles file reading, recursive #include expansion, per-shader compilation,
 * and GL program linking for both vertex/fragment and compute shader programs.
 */

#include "shader.h"

// C++ system headers
#include <cstddef>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <string_view>
#include <vector>

// Third-party library headers (glbinding sub-headers: clang-tidy misc-include-cleaner
// requires direct includes for the symbols used here rather than the umbrella gl.h)
#include <glbinding/gl/enum.h>     // GL_COMPILE_STATUS, GL_VERTEX_SHADER, etc.
#include <glbinding/gl/functions.h> // glCreateShader, glShaderSource, glCompileShader, ...
#include <glbinding/gl/types.h>    // GLuint, GLenum, GLint, GLchar
#include "gl_loader.h" // NOLINT(misc-include-cleaner) -- provides `using namespace gl;`

// Base directory for shader files (set during loading)
namespace {
// NOLINTNEXTLINE(bugprone-throwing-static-initialization) -- std::string ctor throws only on OOM; acceptable for a small one-time static literal
std::string shaderBaseDir = "shader/";
} // namespace

// Allow external code to override the base directory used when resolving
// relative includes (#include "...") and when loading shader files. This is
// useful for tests or custom project layouts.
void setShaderBaseDir(const std::string &baseDir) {
  shaderBaseDir = baseDir;
}

const std::string &getShaderBaseDir() {
  return shaderBaseDir;
}

namespace {

std::string readFile(const std::string &file) {
  std::filesystem::path resolved = file;
  if (!resolved.is_absolute()) {
    std::filesystem::path const base(shaderBaseDir);
    std::filesystem::path const rooted = base / resolved;
    std::error_code ec;
    if (std::filesystem::exists(rooted, ec)) {
      resolved = rooted;
    }
  }

  std::ifstream ifs(resolved, std::ios::in);
  if (ifs.is_open()) {
    std::stringstream ss;
    ss << ifs.rdbuf();
    return ss.str();
  }
  throw "Failed to open file: " + resolved.string();
}



/**
 * @brief Process #include directives in GLSL source.
 *
 * Supports: #include "filename.glsl"
 * Prevents circular includes by tracking already-included files.
 *
 * @param source The shader source code
 * @param basePath Base directory for relative includes
 * @param included Set of already-included files (for circular detection)
 * @return Processed source with includes expanded
 */
// NOLINTNEXTLINE(misc-no-recursion) -- intentional: GLSL #include files may themselves contain further #include directives (depth bounded by FS)
std::string processIncludes(const std::string &source,
                                   const std::string &basePath,
                                   std::set<std::string> &included) {
  std::string result;
  std::istringstream stream(source);
  std::string line;

  auto parseInclude = [](const std::string &input, std::string &includeFile) -> bool {
    std::size_t pos = input.find_first_not_of(" \t");
    if (pos == std::string::npos || input.at(pos) != '#') {
      return false;
    }

    pos = input.find_first_not_of(" \t", pos + 1);
    if (pos == std::string::npos) {
      return false;
    }

    static constexpr std::string_view kIncludeToken = "include";
    if (input.compare(pos, kIncludeToken.size(), kIncludeToken) != 0) {
      return false;
    }
    pos += kIncludeToken.size();

    pos = input.find_first_not_of(" \t", pos);
    if (pos == std::string::npos) {
      return false;
    }

    const char open = input.at(pos);
    char close = '\0';
    if (open == '"') { close = '"'; }
    else if (open == '<') { close = '>'; }
    if (close == '\0') {
      return false;
    }

    const std::size_t start = pos + 1;
    const std::size_t end = input.find(close, start);
    if (end == std::string::npos) {
      return false;
    }

    includeFile = input.substr(start, end - start);
    const std::size_t trailing = input.find_first_not_of(" \t", end + 1);
    return trailing == std::string::npos;
  };

  while (std::getline(stream, line)) {
    std::string includeFile;
    const std::size_t nonSpace = line.find_first_not_of(" \t");
    if (nonSpace != std::string::npos &&
        line.compare(nonSpace, 10, "#extension") == 0 &&
        line.find("GL_GOOGLE_include_directive", nonSpace) != std::string::npos) {
      continue;
    }
    if (parseInclude(line, includeFile)) {

      // Construct full path
      const std::string fullPath = basePath + includeFile;

      // Check for circular include
      if (included.contains(fullPath)) {
        result += "// Skipped circular include: " + includeFile + "\n";
        continue;
      }

      // Mark as included
      included.insert(fullPath);

      // Try to read and process the included file
      try {
        std::string const includeSource = readFile(fullPath);
        result += "// Begin include: " + includeFile + "\n";
        result += processIncludes(includeSource, basePath, included);
        result += "// End include: " + includeFile + "\n";
      } catch (...) {
        std::cerr << "Warning: Failed to include " << fullPath << '\n';
        result += "// Failed to include: " + includeFile + "\n";
      }
    } else {
      result += line + "\n";
    }
  }

  return result;
}

/**
 * @brief Read shader file with include processing.
 */
std::string readShaderWithIncludes(const std::string &file) {
  std::filesystem::path resolvedFile = file;
  if (!resolvedFile.is_absolute()) {
    std::filesystem::path const base(shaderBaseDir);
    std::filesystem::path const rooted = base / resolvedFile;
    std::error_code ec;
    if (std::filesystem::exists(rooted, ec)) {
      resolvedFile = rooted;
    }
  }

  // Extract base directory from file path
  std::string basePath = shaderBaseDir;
  std::string const resolvedFileString = resolvedFile.string();
  const size_t lastSlash = resolvedFileString.find_last_of("/\\");
  if (lastSlash != std::string::npos) {
    basePath = resolvedFileString.substr(0, lastSlash + 1);
  }

  std::string const source = readFile(resolvedFileString);
  std::set<std::string> included;
  included.insert(resolvedFileString); // Mark main file as included
  return processIncludes(source, basePath, included);
}

GLuint compileShader(const std::string &shaderSource, GLenum shaderType) {
  // Create shader
  const GLuint shader = glCreateShader(shaderType);
  if (shader == 0) {
    std::cerr << "Failed to create shader object.\n";
    throw "Failed to create the shader object.";
  }

  // Compile shader
  char const *pShaderSource = shaderSource.c_str();
  glShaderSource(shader, 1, &pShaderSource, nullptr);
  glCompileShader(shader);

  GLint success = 0;
  glGetShaderiv(shader, GL_COMPILE_STATUS, &success);
  GLint maxLength = 0;
  glGetShaderiv(shader, GL_INFO_LOG_LENGTH, &maxLength);
  if (maxLength > 1) {
    std::vector<GLchar> infoLog(static_cast<size_t>(maxLength));
    glGetShaderInfoLog(shader, maxLength, nullptr, infoLog.data());
    std::cerr << infoLog.data() << '\n';
  }
  if (success == 0) {
    glDeleteShader(shader);
    throw "Failed to compile the shader.";
  }

  return shader;
}

struct CompiledShader {
  GLuint id = 0;
};

CompiledShader compileShaderFromFile(const std::string &shaderFile, GLenum shaderType,
                                            const char *label) {
  std::cout << "Compiling " << label << " shader: " << shaderFile << '\n';
  return {compileShader(readShaderWithIncludes(shaderFile), shaderType)};
}

/**
 * @brief Creates and links an OpenGL shader program from vertex and fragment shader files.
 *
 * This function reads the specified shader source files, processes any includes within them,
 * compiles the vertex and fragment shaders, creates a shader program, attaches the compiled
 * shaders to it, and links the program. If linking fails, it outputs the error log and throws
 * an exception. After successful linking, it detaches and deletes the shaders to clean up resources.
 *
 * @param vertexShaderFile The file path to the vertex shader source code.
 * @param fragmentShaderFile The file path to the fragment shader source code.
 * @return The OpenGL shader program ID (GLuint) if linking succeeds.
 * @throws const char* If the shader program fails to link.
 *
 * @note This function assumes an active OpenGL context and relies on helper functions
 *       readShaderWithIncludes() and compileShader() for file reading and shader compilation.
 */
} // namespace

GLuint createShaderProgram(const std::string &vertexShaderFile,
                                  const std::string &fragmentShaderFile) {

  // Compile vertex and fragment shaders with include processing.
  const CompiledShader vertexShader =
      compileShaderFromFile(vertexShaderFile, GL_VERTEX_SHADER, "vertex");
  const CompiledShader fragmentShader =
      compileShaderFromFile(fragmentShaderFile, GL_FRAGMENT_SHADER, "fragment");

  // Create shader program.
  const GLuint program = glCreateProgram();
  glAttachShader(program, vertexShader.id);
  glAttachShader(program, fragmentShader.id);

  // Link the program.
  glLinkProgram(program);
  GLint isLinked = 0;
  glGetProgramiv(program, GL_LINK_STATUS, &isLinked);
  int maxLength = 0;
  glGetProgramiv(program, GL_INFO_LOG_LENGTH, &maxLength);
  if (maxLength > 1) {
    std::vector<GLchar> infoLog(static_cast<size_t>(maxLength));
    glGetProgramInfoLog(program, maxLength, nullptr, infoLog.data());
    std::cerr << infoLog.data() << '\n';
  }
  if (isLinked == 0) {
    throw "Failed to link the shader.";
  }

  // Detach shaders after a successful link.
  glDetachShader(program, vertexShader.id);
  glDetachShader(program, fragmentShader.id);

  glDeleteShader(vertexShader.id);
  glDeleteShader(fragmentShader.id);

  return program;
}

GLuint createComputeProgram(const std::string &computeShaderFile) {
  const CompiledShader computeShader =
      compileShaderFromFile(computeShaderFile, GL_COMPUTE_SHADER, "compute");

  const GLuint program = glCreateProgram();
  glAttachShader(program, computeShader.id);
  glLinkProgram(program);

  GLint isLinked = 0;
  glGetProgramiv(program, GL_LINK_STATUS, &isLinked);
  int maxLength = 0;
  glGetProgramiv(program, GL_INFO_LOG_LENGTH, &maxLength);
  if (maxLength > 1) {
    std::vector<GLchar> infoLog(static_cast<size_t>(maxLength));
    glGetProgramInfoLog(program, maxLength, nullptr, infoLog.data());
    std::cerr << infoLog.data() << '\n';
  }
  if (isLinked == 0) {
    throw "Failed to link the compute shader.";
  }

  glDetachShader(program, computeShader.id);
  glDeleteShader(computeShader.id);

  return program;
}
