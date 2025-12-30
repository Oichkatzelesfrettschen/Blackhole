#include "shader.h"

// C++ system headers
#include <fstream>
#include <iostream>
#include <regex>
#include <set>
#include <sstream>
#include <string>
#include <vector>

// Third-party library headers
#include "gl_loader.h"

// Base directory for shader files (set during loading)
static std::string shaderBaseDir = "shader/";

static std::string readFile(const std::string &file) {
  std::ifstream ifs(file, std::ios::in);
  if (ifs.is_open()) {
    std::stringstream ss;
    ss << ifs.rdbuf();
    return ss.str();
  } else {
    throw "Failed to open file: " + file;
  }
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
static std::string processIncludes(const std::string &source,
                                   const std::string &basePath,
                                   std::set<std::string> &included) {
  std::string result;
  std::istringstream stream(source);
  std::string line;

  // Regex to match #include "filename"
  std::regex includeRegex(R"(^\s*#\s*include\s*[\"<]([^\"<>]+)[\">]\s*$)");

  while (std::getline(stream, line)) {
    std::smatch match;
    if (std::regex_match(line, match, includeRegex)) {
      std::string includeFile = match[1].str();

      // Construct full path
      std::string fullPath = basePath + includeFile;

      // Check for circular include
      if (included.find(fullPath) != included.end()) {
        result += "// Skipped circular include: " + includeFile + "\n";
        continue;
      }

      // Mark as included
      included.insert(fullPath);

      // Try to read and process the included file
      try {
        std::string includeSource = readFile(fullPath);
        result += "// Begin include: " + includeFile + "\n";
        result += processIncludes(includeSource, basePath, included);
        result += "// End include: " + includeFile + "\n";
      } catch (...) {
        std::cerr << "Warning: Failed to include " << fullPath << std::endl;
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
static std::string readShaderWithIncludes(const std::string &file) {
  // Extract base directory from file path
  std::string basePath = shaderBaseDir;
  size_t lastSlash = file.find_last_of("/\\");
  if (lastSlash != std::string::npos) {
    basePath = file.substr(0, lastSlash + 1);
  }

  std::string source = readFile(file);
  std::set<std::string> included;
  included.insert(file); // Mark main file as included
  return processIncludes(source, basePath, included);
}

static GLuint compileShader(const std::string &shaderSource, GLenum shaderType) {
  // Create shader
  GLuint shader = glCreateShader(shaderType);

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
    std::cerr << infoLog.data() << std::endl;
  }
  if (success == 0) {
    glDeleteShader(shader);
    throw "Failed to compile the shader.";
  }

  return shader;
}

GLuint createShaderProgram(const std::string &vertexShaderFile,
                           const std::string &fragmentShaderFile) {

  // Compile vertex and fragment shaders with include processing.
  std::cout << "Compiling vertex shader: " << vertexShaderFile << std::endl;
  GLuint vertexShader =
      compileShader(readShaderWithIncludes(vertexShaderFile), GL_VERTEX_SHADER);

  std::cout << "Compiling fragment shader: " << fragmentShaderFile << std::endl;
  GLuint fragmentShader = compileShader(readShaderWithIncludes(fragmentShaderFile),
                                        GL_FRAGMENT_SHADER);

  // Create shader program.
  GLuint program = glCreateProgram();
  glAttachShader(program, vertexShader);
  glAttachShader(program, fragmentShader);

  // Link the program.
  glLinkProgram(program);
  GLint isLinked = 0;
  glGetProgramiv(program, GL_LINK_STATUS, &isLinked);
  int maxLength = 0;
  glGetProgramiv(program, GL_INFO_LOG_LENGTH, &maxLength);
  if (maxLength > 1) {
    std::vector<GLchar> infoLog(static_cast<size_t>(maxLength));
    glGetProgramInfoLog(program, maxLength, nullptr, infoLog.data());
    std::cerr << infoLog.data() << std::endl;
  }
  if (isLinked == 0) {
    throw "Failed to link the shader.";
  }

  // Detach shaders after a successful link.
  glDetachShader(program, vertexShader);
  glDetachShader(program, fragmentShader);

  glDeleteShader(vertexShader);
  glDeleteShader(fragmentShader);

  return program;
}

GLuint createComputeProgram(const std::string &computeShaderFile) {
  std::cout << "Compiling compute shader: " << computeShaderFile << std::endl;
  GLuint computeShader =
      compileShader(readShaderWithIncludes(computeShaderFile), GL_COMPUTE_SHADER);

  GLuint program = glCreateProgram();
  glAttachShader(program, computeShader);
  glLinkProgram(program);

  GLint isLinked = 0;
  glGetProgramiv(program, GL_LINK_STATUS, &isLinked);
  int maxLength = 0;
  glGetProgramiv(program, GL_INFO_LOG_LENGTH, &maxLength);
  if (maxLength > 1) {
    std::vector<GLchar> infoLog(static_cast<size_t>(maxLength));
    glGetProgramInfoLog(program, maxLength, nullptr, infoLog.data());
    std::cerr << infoLog.data() << std::endl;
  }
  if (isLinked == 0) {
    throw "Failed to link the compute shader.";
  }

  glDetachShader(program, computeShader);
  glDeleteShader(computeShader);

  return program;
}
