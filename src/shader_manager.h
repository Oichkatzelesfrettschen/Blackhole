#ifndef SHADER_MANAGER_H
#define SHADER_MANAGER_H

#include "gl_loader.h"
#include <map>
#include <string>
#include <vector>

// OpenGL version capabilities detected at runtime
struct GLCapabilities {
  int majorVersion = 0;
  int minorVersion = 0;
  int glslVersion = 0;  // e.g., 330, 410, 450

  bool hasComputeShaders = false;    // 4.3+
  bool hasTessellation = false;      // 4.0+
  bool hasSSBO = false;              // 4.3+
  bool hasDSA = false;               // 4.5+
  bool hasGeometryShaders = false;   // 3.2+
  bool hasExplicitLocations = false; // 3.3+

  std::string vendorString;
  std::string rendererString;
  std::string versionString;
  std::string glslVersionString;
};

// Shader version tiers
enum class ShaderTier {
  Glsl460, // OpenGL 4.6 - latest features
  Glsl450, // OpenGL 4.5 - DSA, SSBOs
  Glsl410, // OpenGL 4.1 - Apple max, tessellation
  Glsl330, // OpenGL 3.3 - Core profile baseline
  Glsl120, // OpenGL 2.1 - Legacy fallback
  UNKNOWN
};

class ShaderManager {
public:
  static ShaderManager &instance();

  // Initialize - must be called after OpenGL context is created
  void init();
  void shutdown();

  // Get detected capabilities
  [[nodiscard]] const GLCapabilities &getCapabilities() const { return capabilities_; }
  [[nodiscard]] ShaderTier getCurrentTier() const { return currentTier_; }

  // Get version string for shader preprocessor
  [[nodiscard]] std::string getVersionDirective() const;

  // Load shader with automatic version selection
  // Returns shader source with appropriate #version and defines
  [[nodiscard]] std::string loadShaderSource(const std::string &basePath) const;

  // Compile shader with automatic fallback
  [[nodiscard]] GLuint compileShader(const std::string &basePath, GLenum shaderType) const;

  // Create program from vertex and fragment shaders
  [[nodiscard]] GLuint createProgram(const std::string &vertPath,
                                     const std::string &fragPath) const;

  // Feature availability queries
  [[nodiscard]] bool canUseComputeShaders() const { return capabilities_.hasComputeShaders; }
  [[nodiscard]] bool canUseTessellation() const { return capabilities_.hasTessellation; }
  [[nodiscard]] bool canUseDSA() const { return capabilities_.hasDSA; }

  // Get GLSL version number (e.g., 330, 410, 450)
  [[nodiscard]] int getGLSLVersion() const { return capabilities_.glslVersion; }

  // Check if running on Apple (OpenGL 4.1 max)
  [[nodiscard]] bool isApplePlatform() const;

  ShaderManager(const ShaderManager &) = delete;
  ShaderManager &operator=(const ShaderManager &) = delete;

private:
  ShaderManager() = default;
  ~ShaderManager() = default;

  void detectCapabilities();
  [[nodiscard]] ShaderTier determineTier() const;

  // Prepend version and feature defines to shader source
  [[nodiscard]] std::string preprocessShader(const std::string &source) const;

  // Try to load shader file with version suffix fallback
  // e.g., "shader.frag" -> try "shader.frag.410", "shader.frag.330", etc.
  [[nodiscard]] std::string findBestShaderFile(const std::string &basePath) const;

  GLCapabilities capabilities_;
  ShaderTier currentTier_ = ShaderTier::UNKNOWN;
  bool initialized_ = false;
};

// Utility functions
const char *shaderTierToString(ShaderTier tier);
int shaderTierToGLSLVersion(ShaderTier tier);

#endif // SHADER_MANAGER_H
