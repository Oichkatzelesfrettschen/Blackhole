#include "shader_manager.h"

#include <algorithm>
#include <cstdio>
#include <cstring>
#include <fstream>
#include <sstream>

ShaderManager &ShaderManager::instance() {
  static ShaderManager instance;
  return instance;
}

void ShaderManager::init() {
  if (initialized_) {
    return;
  }

  detectCapabilities();
  currentTier_ = determineTier();
  initialized_ = true;

  // Log detected capabilities
  std::printf("=== OpenGL Capabilities ===\n");
  std::printf("Vendor: %s\n", capabilities_.vendorString.c_str());
  std::printf("Renderer: %s\n", capabilities_.rendererString.c_str());
  std::printf("Version: %s\n", capabilities_.versionString.c_str());
  std::printf("GLSL Version: %s\n", capabilities_.glslVersionString.c_str());
  std::printf("Detected: OpenGL %d.%d (GLSL %d)\n", capabilities_.majorVersion,
              capabilities_.minorVersion, capabilities_.glslVersion);
  std::printf("Shader Tier: %s\n", shaderTierToString(currentTier_));
  std::printf("Features: Compute=%s Tessellation=%s DSA=%s Geometry=%s\n",
              capabilities_.hasComputeShaders ? "yes" : "no",
              capabilities_.hasTessellation ? "yes" : "no",
              capabilities_.hasDSA ? "yes" : "no",
              capabilities_.hasGeometryShaders ? "yes" : "no");
  std::printf("===========================\n");
}

void ShaderManager::shutdown() { initialized_ = false; }

void ShaderManager::detectCapabilities() {
  // Get version strings
  const char *vendor =
      reinterpret_cast<const char *>(glGetString(GL_VENDOR));
  const char *renderer =
      reinterpret_cast<const char *>(glGetString(GL_RENDERER));
  const char *version =
      reinterpret_cast<const char *>(glGetString(GL_VERSION));
  const char *glslVersion =
      reinterpret_cast<const char *>(glGetString(GL_SHADING_LANGUAGE_VERSION));

  capabilities_.vendorString = vendor ? vendor : "Unknown";
  capabilities_.rendererString = renderer ? renderer : "Unknown";
  capabilities_.versionString = version ? version : "Unknown";
  capabilities_.glslVersionString = glslVersion ? glslVersion : "Unknown";

  // Get numeric version (OpenGL 3.0+ method)
  glGetIntegerv(GL_MAJOR_VERSION, &capabilities_.majorVersion);
  glGetIntegerv(GL_MINOR_VERSION, &capabilities_.minorVersion);

  // Map GL version to GLSL version
  int major = capabilities_.majorVersion;
  int minor = capabilities_.minorVersion;

  if (major >= 4) {
    if (minor >= 6)
      capabilities_.glslVersion = 460;
    else if (minor >= 5)
      capabilities_.glslVersion = 450;
    else if (minor >= 4)
      capabilities_.glslVersion = 440;
    else if (minor >= 3)
      capabilities_.glslVersion = 430;
    else if (minor >= 2)
      capabilities_.glslVersion = 420;
    else if (minor >= 1)
      capabilities_.glslVersion = 410;
    else
      capabilities_.glslVersion = 400;
  } else if (major == 3) {
    if (minor >= 3)
      capabilities_.glslVersion = 330;
    else if (minor >= 2)
      capabilities_.glslVersion = 150;
    else if (minor >= 1)
      capabilities_.glslVersion = 140;
    else
      capabilities_.glslVersion = 130;
  } else {
    // OpenGL 2.x
    capabilities_.glslVersion = 120;
  }

  // Detect feature availability
  capabilities_.hasGeometryShaders = (major > 3 || (major == 3 && minor >= 2));
  capabilities_.hasExplicitLocations = (major > 3 || (major == 3 && minor >= 3));
  capabilities_.hasTessellation = (major >= 4);
  capabilities_.hasComputeShaders = (major > 4 || (major == 4 && minor >= 3));
  capabilities_.hasSSBO = capabilities_.hasComputeShaders;
  capabilities_.hasDSA = (major > 4 || (major == 4 && minor >= 5));
}

ShaderTier ShaderManager::determineTier() const {
  int glsl = capabilities_.glslVersion;

  if (glsl >= 460)
    return ShaderTier::GLSL_460;
  if (glsl >= 450)
    return ShaderTier::GLSL_450;
  if (glsl >= 410)
    return ShaderTier::GLSL_410;
  if (glsl >= 330)
    return ShaderTier::GLSL_330;
  if (glsl >= 120)
    return ShaderTier::GLSL_120;

  return ShaderTier::UNKNOWN;
}

std::string ShaderManager::getVersionDirective() const {
  char buffer[64];
  std::snprintf(buffer, sizeof(buffer), "#version %d core\n",
                capabilities_.glslVersion);
  return std::string(buffer);
}

bool ShaderManager::isApplePlatform() const {
#ifdef __APPLE__
  return true;
#else
  // Also check if vendor string contains Apple
  return capabilities_.vendorString.find("Apple") != std::string::npos;
#endif
}

std::string ShaderManager::preprocessShader(const std::string &source) const {
  std::stringstream ss;

  // Add version directive
  ss << "#version " << capabilities_.glslVersion << " core\n";

  // Add feature defines
  ss << "#define GLSL_VERSION " << capabilities_.glslVersion << "\n";
  ss << "#define GL_MAJOR_VERSION " << capabilities_.majorVersion << "\n";
  ss << "#define GL_MINOR_VERSION " << capabilities_.minorVersion << "\n";

  if (capabilities_.hasComputeShaders) {
    ss << "#define HAS_COMPUTE_SHADERS 1\n";
  }
  if (capabilities_.hasTessellation) {
    ss << "#define HAS_TESSELLATION 1\n";
  }
  if (capabilities_.hasDSA) {
    ss << "#define HAS_DSA 1\n";
  }
  if (capabilities_.hasGeometryShaders) {
    ss << "#define HAS_GEOMETRY_SHADERS 1\n";
  }
  if (capabilities_.hasExplicitLocations) {
    ss << "#define HAS_EXPLICIT_LOCATIONS 1\n";
  }

  // Add compatibility defines for older GLSL versions
  if (capabilities_.glslVersion < 330) {
    ss << "#define texture texture2D\n";
    ss << "#define in varying\n";
    ss << "#define out varying\n";
  }

  ss << "\n";

  // Find and remove existing #version directive from source
  std::string processedSource = source;
  size_t versionPos = processedSource.find("#version");
  if (versionPos != std::string::npos) {
    size_t endLine = processedSource.find('\n', versionPos);
    if (endLine != std::string::npos) {
      processedSource = processedSource.substr(endLine + 1);
    }
  }

  ss << processedSource;
  return ss.str();
}

std::string
ShaderManager::findBestShaderFile(const std::string &basePath) const {
  // Try version-specific files first
  std::vector<std::string> suffixes;

  switch (currentTier_) {
  case ShaderTier::GLSL_460:
    suffixes = {".460", ".450", ".410", ".330", ""};
    break;
  case ShaderTier::GLSL_450:
    suffixes = {".450", ".410", ".330", ""};
    break;
  case ShaderTier::GLSL_410:
    suffixes = {".410", ".330", ""};
    break;
  case ShaderTier::GLSL_330:
    suffixes = {".330", ""};
    break;
  case ShaderTier::GLSL_120:
    suffixes = {".120", ""};
    break;
  default:
    suffixes = {""};
    break;
  }

  for (const auto &suffix : suffixes) {
    std::string path = basePath + suffix;
    std::ifstream file(path);
    if (file.good()) {
      return path;
    }
  }

  // Return base path if no versioned file found
  return basePath;
}

std::string ShaderManager::loadShaderSource(const std::string &basePath) const {
  std::string actualPath = findBestShaderFile(basePath);

  std::ifstream file(actualPath);
  if (!file.is_open()) {
    std::fprintf(stderr, "Failed to open shader file: %s\n", actualPath.c_str());
    return "";
  }

  std::stringstream buffer;
  buffer << file.rdbuf();
  return preprocessShader(buffer.str());
}

GLuint ShaderManager::compileShader(const std::string &basePath,
                                    GLenum shaderType) const {
  std::string source = loadShaderSource(basePath);
  if (source.empty()) {
    return 0;
  }

  GLuint shader = glCreateShader(shaderType);
  const char *sourcePtr = source.c_str();
  glShaderSource(shader, 1, &sourcePtr, nullptr);
  glCompileShader(shader);

  // Check compilation status
  GLint success;
  glGetShaderiv(shader, GL_COMPILE_STATUS, &success);
  if (!success) {
    GLchar infoLog[1024];
    glGetShaderInfoLog(shader, sizeof(infoLog), nullptr, infoLog);
    std::fprintf(stderr, "Shader compilation failed (%s):\n%s\n",
                 basePath.c_str(), infoLog);
    glDeleteShader(shader);
    return 0;
  }

  return shader;
}

GLuint ShaderManager::createProgram(const std::string &vertPath,
                                    const std::string &fragPath) const {
  GLuint vertShader = compileShader(vertPath, GL_VERTEX_SHADER);
  if (vertShader == 0) {
    return 0;
  }

  GLuint fragShader = compileShader(fragPath, GL_FRAGMENT_SHADER);
  if (fragShader == 0) {
    glDeleteShader(vertShader);
    return 0;
  }

  GLuint program = glCreateProgram();
  glAttachShader(program, vertShader);
  glAttachShader(program, fragShader);
  glLinkProgram(program);

  // Check link status
  GLint success;
  glGetProgramiv(program, GL_LINK_STATUS, &success);
  if (!success) {
    GLchar infoLog[1024];
    glGetProgramInfoLog(program, sizeof(infoLog), nullptr, infoLog);
    std::fprintf(stderr, "Program linking failed:\n%s\n", infoLog);
    glDeleteProgram(program);
    glDeleteShader(vertShader);
    glDeleteShader(fragShader);
    return 0;
  }

  // Shaders can be deleted after linking
  glDeleteShader(vertShader);
  glDeleteShader(fragShader);

  return program;
}

const char *shaderTierToString(ShaderTier tier) {
  switch (tier) {
  case ShaderTier::GLSL_460:
    return "GLSL 4.60 (OpenGL 4.6)";
  case ShaderTier::GLSL_450:
    return "GLSL 4.50 (OpenGL 4.5)";
  case ShaderTier::GLSL_410:
    return "GLSL 4.10 (OpenGL 4.1)";
  case ShaderTier::GLSL_330:
    return "GLSL 3.30 (OpenGL 3.3)";
  case ShaderTier::GLSL_120:
    return "GLSL 1.20 (OpenGL 2.1)";
  default:
    return "Unknown";
  }
}

int shaderTierToGLSLVersion(ShaderTier tier) {
  switch (tier) {
  case ShaderTier::GLSL_460:
    return 460;
  case ShaderTier::GLSL_450:
    return 450;
  case ShaderTier::GLSL_410:
    return 410;
  case ShaderTier::GLSL_330:
    return 330;
  case ShaderTier::GLSL_120:
    return 120;
  default:
    return 330;
  }
}
