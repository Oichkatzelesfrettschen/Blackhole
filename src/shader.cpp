#include "shader.h"

// C++ system headers
#include <algorithm>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>
#include <string>
#include <vector>

// Third-party library headers
#include "gl_loader.h"

// Base directory for shader files (set during loading)
static std::string shaderBaseDir = "shader/";
static bool spirvRequested = false;
static bool spirvConfigInit = false;
static bool spirvSupportChecked = false;
static bool spirvSupported = false;
static bool spirvSupportLogged = false;

// Allow external code to override the base directory used when resolving
// relative includes (#include "...") and when loading shader files. This is
// useful for tests or custom project layouts.
void setShaderBaseDir(const std::string &baseDir) {
  shaderBaseDir = baseDir;
}

const std::string &getShaderBaseDir() {
  return shaderBaseDir;
}

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

static std::vector<char> readBinaryFile(const std::string &file) {
  std::ifstream ifs(file, std::ios::binary);
  if (!ifs.is_open()) {
    throw "Failed to open file: " + file;
  }
  ifs.seekg(0, std::ios::end);
  std::streamsize size = ifs.tellg();
  ifs.seekg(0, std::ios::beg);
  if (size <= 0) {
    return {};
  }
  std::vector<char> data(static_cast<std::size_t>(size));
  if (!ifs.read(data.data(), size)) {
    throw "Failed to read file: " + file;
  }
  return data;
}

static bool hasExtension(const char *name) {
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

static void initSpirvConfig() {
  if (spirvConfigInit) {
    return;
  }
  const char *env = std::getenv("BLACKHOLE_USE_SPIRV");
  spirvRequested = (env != nullptr && std::string(env) == "1");
  spirvConfigInit = true;
}

static bool supportsSpirv() {
  if (spirvSupportChecked) {
    return spirvSupported;
  }
  spirvSupportChecked = true;
  GLint major = 0;
  GLint minor = 0;
  glGetIntegerv(GL_MAJOR_VERSION, &major);
  glGetIntegerv(GL_MINOR_VERSION, &minor);
  const bool versionIs46 = (major > 4) || (major == 4 && minor >= 6);
  GLint count = 0;
  glGetIntegerv(GL_NUM_SHADER_BINARY_FORMATS, &count);
  if (count <= 0) {
    spirvSupported = false;
    return spirvSupported;
  }
  std::vector<GLint> formats(static_cast<std::size_t>(count));
  glGetIntegerv(GL_SHADER_BINARY_FORMATS, formats.data());
  const GLint spirvFormat = static_cast<GLint>(GL_SHADER_BINARY_FORMAT_SPIR_V);
  bool hasFormat =
      std::any_of(formats.begin(), formats.end(),
                  [spirvFormat](GLint format) { return format == spirvFormat; });
  spirvSupported = hasFormat && (versionIs46 || hasExtension("GL_ARB_gl_spirv"));
  return spirvSupported;
}

static bool loadSpirvShader(const std::string &path, GLenum shaderType, GLuint &shaderOut) {
  if (!supportsSpirv()) {
    if (spirvRequested && !spirvSupportLogged) {
      std::cout << "SPIR-V requested but not supported by the driver.\n";
      spirvSupportLogged = true;
    }
    return false;
  }
  if (!std::filesystem::exists(path)) {
    return false;
  }
  std::vector<char> spirv = readBinaryFile(path);
  if (spirv.empty()) {
    return false;
  }
  GLuint shader = glCreateShader(shaderType);
  if (shader == 0) {
    return false;
  }
  glShaderBinary(1, &shader, GL_SHADER_BINARY_FORMAT_SPIR_V,
                 spirv.data(), static_cast<GLsizei>(spirv.size()));
  glSpecializeShader(shader, "main", 0, nullptr, nullptr);

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
    return false;
  }
  shaderOut = shader;
  return true;
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

  auto parseInclude = [](const std::string &input, std::string &includeFile) -> bool {
    std::size_t pos = input.find_first_not_of(" \t");
    if (pos == std::string::npos || input[pos] != '#') {
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

    const char open = input[pos];
    const char close = (open == '"') ? '"' : ((open == '<') ? '>' : '\0');
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
    std::size_t nonSpace = line.find_first_not_of(" \t");
    if (nonSpace != std::string::npos &&
        line.compare(nonSpace, 10, "#extension") == 0 &&
        line.find("GL_GOOGLE_include_directive", nonSpace) != std::string::npos) {
      continue;
    }
    if (parseInclude(line, includeFile)) {

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
  if (shader == 0) {
    std::cerr << "Failed to create shader object." << std::endl;
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
    std::cerr << infoLog.data() << std::endl;
  }
  if (success == 0) {
    glDeleteShader(shader);
    throw "Failed to compile the shader.";
  }

  return shader;
}

struct CompiledShader {
  GLuint id = 0;
  bool fromSpirv = false;
};

static CompiledShader compileShaderFromFile(const std::string &shaderFile, GLenum shaderType,
                                            const char *label) {
  initSpirvConfig();
  if (spirvRequested) {
    const std::string spirvPath = shaderFile + ".spv";
    GLuint spirvShader = 0;
    if (loadSpirvShader(spirvPath, shaderType, spirvShader)) {
      std::cout << "Loading SPIR-V " << label << " shader: " << spirvPath << std::endl;
      return {spirvShader, true};
    }
  }
  std::cout << "Compiling " << label << " shader: " << shaderFile << std::endl;
  return {compileShader(readShaderWithIncludes(shaderFile), shaderType), false};
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
GLuint createShaderProgram(const std::string &vertexShaderFile,
                           const std::string &fragmentShaderFile) {

  // Compile vertex and fragment shaders with include processing.
  CompiledShader vertexShader =
      compileShaderFromFile(vertexShaderFile, GL_VERTEX_SHADER, "vertex");
  CompiledShader fragmentShader =
      compileShaderFromFile(fragmentShaderFile, GL_FRAGMENT_SHADER, "fragment");

  // Create shader program.
  GLuint program = glCreateProgram();
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
    std::cerr << infoLog.data() << std::endl;
  }
  if (isLinked == 0) {
    const bool usedSpirv = vertexShader.fromSpirv || fragmentShader.fromSpirv;
    if (!usedSpirv) {
      throw "Failed to link the shader.";
    }
    std::cout << "SPIR-V link failed; falling back to GLSL for " << vertexShaderFile
              << " + " << fragmentShaderFile << std::endl;
    glDeleteProgram(program);
    glDeleteShader(vertexShader.id);
    glDeleteShader(fragmentShader.id);
    GLuint vertexFallback =
        compileShader(readShaderWithIncludes(vertexShaderFile), GL_VERTEX_SHADER);
    GLuint fragmentFallback =
        compileShader(readShaderWithIncludes(fragmentShaderFile), GL_FRAGMENT_SHADER);
    program = glCreateProgram();
    glAttachShader(program, vertexFallback);
    glAttachShader(program, fragmentFallback);
    glLinkProgram(program);
    glGetProgramiv(program, GL_LINK_STATUS, &isLinked);
    glGetProgramiv(program, GL_INFO_LOG_LENGTH, &maxLength);
    if (maxLength > 1) {
      std::vector<GLchar> fallbackLog(static_cast<size_t>(maxLength));
      glGetProgramInfoLog(program, maxLength, nullptr, fallbackLog.data());
      std::cerr << fallbackLog.data() << std::endl;
    }
    if (isLinked == 0) {
      throw "Failed to link the shader.";
    }
    glDetachShader(program, vertexFallback);
    glDetachShader(program, fragmentFallback);
    glDeleteShader(vertexFallback);
    glDeleteShader(fragmentFallback);
    return program;
  }

  // Detach shaders after a successful link.
  glDetachShader(program, vertexShader.id);
  glDetachShader(program, fragmentShader.id);

  glDeleteShader(vertexShader.id);
  glDeleteShader(fragmentShader.id);

  return program;
}

GLuint createComputeProgram(const std::string &computeShaderFile) {
  CompiledShader computeShader =
      compileShaderFromFile(computeShaderFile, GL_COMPUTE_SHADER, "compute");

  GLuint program = glCreateProgram();
  glAttachShader(program, computeShader.id);
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
    if (!computeShader.fromSpirv) {
      throw "Failed to link the compute shader.";
    }
    std::cout << "SPIR-V link failed; falling back to GLSL for " << computeShaderFile
              << std::endl;
    glDeleteProgram(program);
    glDeleteShader(computeShader.id);
    GLuint computeFallback =
        compileShader(readShaderWithIncludes(computeShaderFile), GL_COMPUTE_SHADER);
    program = glCreateProgram();
    glAttachShader(program, computeFallback);
    glLinkProgram(program);
    glGetProgramiv(program, GL_LINK_STATUS, &isLinked);
    glGetProgramiv(program, GL_INFO_LOG_LENGTH, &maxLength);
    if (maxLength > 1) {
      std::vector<GLchar> fallbackLog(static_cast<size_t>(maxLength));
      glGetProgramInfoLog(program, maxLength, nullptr, fallbackLog.data());
      std::cerr << fallbackLog.data() << std::endl;
    }
    if (isLinked == 0) {
      throw "Failed to link the compute shader.";
    }
    glDetachShader(program, computeFallback);
    glDeleteShader(computeFallback);
    return program;
  }

  glDetachShader(program, computeShader.id);
  glDeleteShader(computeShader.id);

  return program;
}
