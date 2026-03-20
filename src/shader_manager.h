/**
 * @file shader_manager.h
 * @brief Runtime OpenGL capability detection and GLSL version-tier selection.
 *
 * ShaderManager is a singleton that inspects the active OpenGL context on
 * startup, maps the GL/GLSL version to a ShaderTier, and exposes helpers for
 * loading, preprocessing, compiling, and linking shader programs with the
 * correct version directive and feature defines.
 */

#ifndef SHADER_MANAGER_H
#define SHADER_MANAGER_H

#include "gl_loader.h"
#include <map>
#include <string>
#include <vector>

/** @brief OpenGL version capabilities detected at runtime. */
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

/** @brief GLSL capability tier derived from the detected GL version. */
enum class ShaderTier {
  Glsl460, // OpenGL 4.6 - latest features
  Glsl450, // OpenGL 4.5 - DSA, SSBOs
  Glsl410, // OpenGL 4.1 - Apple max, tessellation
  Glsl330, // OpenGL 3.3 - Core profile baseline
  Glsl120, // OpenGL 2.1 - Legacy fallback
  UNKNOWN
};

/**
 * @brief Singleton manager for runtime OpenGL capability detection and shader loading.
 *
 * Call init() once after the GL context is created. All other methods are
 * valid only after a successful init().
 */
class ShaderManager {
public:
  /** @brief Returns the process-wide singleton instance. */
  static ShaderManager &instance();

  /**
   * @brief Detect GL capabilities and select the active ShaderTier.
   *
   * Must be called once after the OpenGL context is created. Subsequent
   * calls are no-ops.
   */
  void init();

  /** @brief Reset initialized state (call before destroying the GL context). */
  void shutdown();

  [[nodiscard]] const GLCapabilities &getCapabilities() const { return capabilities_; }
  [[nodiscard]] ShaderTier getCurrentTier() const { return currentTier_; }

  /**
   * @brief Return the GLSL #version directive string for the current tier.
   * @return String of the form "#version NNN core\n".
   */
  [[nodiscard]] std::string getVersionDirective() const;

  /**
   * @brief Load and preprocess a shader source file for the current tier.
   *
   * Finds the best-matching versioned file (e.g. "shader.frag.450") and
   * prepends the version directive plus feature defines.
   *
   * @param basePath Base file path without version suffix.
   * @return Preprocessed GLSL source, or an empty string on failure.
   */
  [[nodiscard]] std::string loadShaderSource(const std::string &basePath) const;

  /**
   * @brief Compile a single shader stage from file.
   *
   * @param basePath Base file path (version suffix resolved automatically).
   * @param shaderType GL shader stage constant (e.g. GL_VERTEX_SHADER).
   * @return Non-zero GL shader object on success, 0 on failure.
   */
  [[nodiscard]] GLuint compileShader(const std::string &basePath, GLenum shaderType) const;

  /**
   * @brief Compile and link a vertex+fragment program.
   *
   * @param vertPath Base path for the vertex shader.
   * @param fragPath Base path for the fragment shader.
   * @return Non-zero GL program object on success, 0 on failure.
   */
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

/**
 * @brief Return a human-readable string for a ShaderTier value.
 * @param tier The tier to describe.
 * @return Null-terminated string such as "GLSL 4.60 (OpenGL 4.6)".
 */
const char *shaderTierToString(ShaderTier tier);

/**
 * @brief Map a ShaderTier to its integer GLSL version number.
 * @param tier The tier to query.
 * @return Integer version (e.g. 460, 450, 330). Returns 330 for UNKNOWN.
 */
int shaderTierToGLSLVersion(ShaderTier tier);

#endif // SHADER_MANAGER_H
