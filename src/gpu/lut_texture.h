/**
 * @file lut_texture.h
 * @brief GPU texture memory infrastructure for 1D lookup tables.
 *
 * WHY: GLSL cannot call Boost special functions, so we precompute
 * physics LUTs (synchrotron G(x), absorption, emissivity) on the CPU
 * and upload as 1D GL textures with hardware linear interpolation.
 * arXiv:2505.08855 demonstrates 3-5x speedup from using texture memory
 * for radiation tables vs manual interpolation.
 *
 * WHAT: RAII wrapper for OpenGL 1D textures optimized for LUT access:
 *   - GL_TEXTURE_1D with GL_LINEAR filtering (free hardware interpolation)
 *   - GL_CLAMP_TO_EDGE for boundary behavior
 *   - GL_R32F internal format (single-channel float32)
 *   - Reusable for any 1D float LUT
 *
 * HOW: Call LutTexture1D::create() with CPU-side float array, then
 * bind to a texture unit and set the shader uniform. The GLSL shader
 * samples via texture(sampler1D, u) where u is in [0, 1].
 */

#ifndef GPU_LUT_TEXTURE_H
#define GPU_LUT_TEXTURE_H

#include <cmath>
#include <cstdint>
#include <vector>

// Forward-declare GL types to avoid pulling in the full GL header here.
// The implementation file (or user code) must include the GL loader.
// These match the OpenGL spec exactly.
#ifndef GL_TEXTURE_1D
using GLuint = unsigned int;
using GLsizei = int;
using GLint = int;
using GLenum = unsigned int;
constexpr GLenum GL_TEXTURE_1D = 0x0DE0;
constexpr GLenum GL_R32F = 0x822E;
constexpr GLenum GL_RED = 0x1903;
constexpr GLenum GL_FLOAT = 0x1406;
constexpr GLenum GL_LINEAR = 0x2601;
constexpr GLenum GL_CLAMP_TO_EDGE = 0x812F;
constexpr GLenum GL_TEXTURE_MIN_FILTER = 0x2801;
constexpr GLenum GL_TEXTURE_MAG_FILTER = 0x2800;
constexpr GLenum GL_TEXTURE_WRAP_S = 0x2802;
#define GPU_LUT_TEXTURE_NEEDS_GL_FUNCS
#endif

namespace gpu {

/**
 * @brief 1D OpenGL texture for lookup tables with hardware interpolation.
 *
 * Uses GL_LINEAR filtering so the GPU interpolates between LUT entries
 * for free. The texture coordinate u in [0, 1] maps to the full LUT range.
 *
 * For log-spaced LUTs (like synchrotron G(x)):
 *   u = log(x / x_min) / log(x_max / x_min)
 *
 * The shader samples: value = texture(lut_sampler, u).r
 */
struct LutTexture1D {
  GLuint texture_id = 0;
  GLsizei size = 0;
  bool valid = false;

  LutTexture1D() = default;

  // Non-copyable, movable
  LutTexture1D(const LutTexture1D&) = delete;
  LutTexture1D& operator=(const LutTexture1D&) = delete;

  LutTexture1D(LutTexture1D&& other) noexcept
      : texture_id(other.texture_id), size(other.size), valid(other.valid) {
    other.texture_id = 0;
    other.valid = false;
  }

  LutTexture1D& operator=(LutTexture1D&& other) noexcept {
    if (this != &other) {
      destroy();
      texture_id = other.texture_id;
      size = other.size;
      valid = other.valid;
      other.texture_id = 0;
      other.valid = false;
    }
    return *this;
  }

  ~LutTexture1D() { destroy(); }

  /**
   * @brief Create a 1D texture from CPU float data.
   *
   * Uploads the data as GL_R32F with GL_LINEAR filtering and
   * GL_CLAMP_TO_EDGE wrapping.
   *
   * @param data Pointer to float array
   * @param n Number of entries
   *
   * Requires OpenGL context to be current. Caller must include
   * their GL loader before calling this.
   */
  void create(const float* data, GLsizei n);

  /**
   * @brief Update existing texture with new data (same size).
   */
  void update(const float* data, GLsizei n);

  /**
   * @brief Bind this texture to a texture unit.
   *
   * @param unit Texture unit index (0 = GL_TEXTURE0, etc.)
   */
  void bind(int unit) const;

  /**
   * @brief Release the GL texture resource.
   */
  void destroy();
};

/**
 * @brief Parameters defining the domain of a log-spaced LUT.
 *
 * Used to compute the texture coordinate u from a physical value x:
 *   u = log(x / x_min) / log(x_max / x_min)
 *
 * These parameters must match between CPU generation and GPU sampling.
 */
struct LutDomain {
  float x_min;
  float x_max;
  int n_entries;

  /// Compute texture coordinate from physical value
  [[nodiscard]] float to_texcoord(float x) const {
    if (x <= x_min) return 0.0f;
    if (x >= x_max) return 1.0f;
    float log_ratio = std::log(x_max / x_min);
    return std::log(x / x_min) / log_ratio;
  }

  /// Compute physical value from texture coordinate
  [[nodiscard]] float from_texcoord(float u) const {
    float log_ratio = std::log(x_max / x_min);
    return x_min * std::exp(u * log_ratio);
  }
};

/// Standard domain for synchrotron G(x) LUT
inline constexpr LutDomain SYNCH_G_DOMAIN = {0.001f, 30.0f, 256};

} // namespace gpu

// ============================================================================
// Implementation (requires GL context and loader)
// ============================================================================
//
// Include this header and define GPU_LUT_TEXTURE_IMPL before including
// your GL loader to get the implementation. Alternatively, implement
// the methods in a .cpp file that includes the GL loader.
//
// Example:
//   #include "gl_loader.h"  // Your GL binding (glbinding, GLAD, etc.)
//   #define GPU_LUT_TEXTURE_IMPL
//   #include "gpu/lut_texture.h"
//

#ifdef GPU_LUT_TEXTURE_IMPL

#include <cmath>

namespace gpu {

void LutTexture1D::create(const float* data, GLsizei n) {
  if (valid) destroy();

  glGenTextures(1, &texture_id);
  glBindTexture(GL_TEXTURE_1D, texture_id);

  // Upload data as single-channel float32
  glTexImage1D(GL_TEXTURE_1D, 0, static_cast<GLint>(GL_R32F),
               n, 0, GL_RED, GL_FLOAT, data);

  // Hardware linear interpolation (the key optimization from arXiv:2505.08855)
  glTexParameteri(GL_TEXTURE_1D, GL_TEXTURE_MIN_FILTER, static_cast<GLint>(GL_LINEAR));
  glTexParameteri(GL_TEXTURE_1D, GL_TEXTURE_MAG_FILTER, static_cast<GLint>(GL_LINEAR));

  // Clamp to edge: values outside [0,1] return the boundary value
  glTexParameteri(GL_TEXTURE_1D, GL_TEXTURE_WRAP_S, static_cast<GLint>(GL_CLAMP_TO_EDGE));

  glBindTexture(GL_TEXTURE_1D, 0);

  size = n;
  valid = true;
}

void LutTexture1D::update(const float* data, GLsizei n) {
  if (!valid || n != size) {
    create(data, n);
    return;
  }
  glBindTexture(GL_TEXTURE_1D, texture_id);
  glTexSubImage1D(GL_TEXTURE_1D, 0, 0, n, GL_RED, GL_FLOAT, data);
  glBindTexture(GL_TEXTURE_1D, 0);
}

void LutTexture1D::bind(int unit) const {
  if (!valid) return;
  glActiveTexture(static_cast<GLenum>(0x84C0 + unit)); // GL_TEXTURE0 + unit
  glBindTexture(GL_TEXTURE_1D, texture_id);
}

void LutTexture1D::destroy() {
  if (valid && texture_id != 0) {
    glDeleteTextures(1, &texture_id);
    texture_id = 0;
    valid = false;
    size = 0;
  }
}

} // namespace gpu

#endif // GPU_LUT_TEXTURE_IMPL

#endif // GPU_LUT_TEXTURE_H
