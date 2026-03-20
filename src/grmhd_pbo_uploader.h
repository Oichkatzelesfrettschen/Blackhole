/**
 * @file grmhd_pbo_uploader.h
 * @brief Double-buffered PBO upload path for GRMHD 3D textures.
 *
 * WHY: glTexImage3D / glTexSubImage3D with a raw CPU pointer forces the GL
 *      driver to copy data to an internal staging buffer synchronously on the
 *      render thread before initiating the GPU DMA.  For large 3D datasets
 *      (64^3 to 256^3 RGBA32F = 4-256 MB) this stall can exceed 10 ms per
 *      seek event, which is unacceptable at 60 fps.
 *
 *      Using a GL_PIXEL_UNPACK_BUFFER eliminates the staging copy: the CPU
 *      writes directly into DMA-coherent memory (the mapped PBO), and the
 *      subsequent glTexSubImage3D with a bound PBO initiates an asynchronous
 *      GPU DMA without blocking the render thread.
 *
 * WHAT: GrmhdPBOUploader manages two PBOs for double-buffering:
 *
 *         Frame N:   CPU memcpy -> PBO[write]   (this frame's new data)
 *         Frame N:   GPU DMA   <- PBO[read]    (last frame's staged data)
 *         Swap write/read indices.
 *
 *       On the very first upload call the texture is primed synchronously so
 *       that it is never empty/black when the shader first samples it.
 *
 * HOW:
 *   1. Construct GrmhdPBOUploader (no GL state touched).
 *   2. Call init(w, h, d) once after obtaining an OpenGL 4.6 context.
 *   3. Call upload(data, nFloats) whenever new GRMHD data is available.
 *   4. Bind texture() in fragment / compute shaders as sampler3D.
 *   5. Call shutdown() before the GL context is destroyed.
 *
 * References:
 *   OpenGL 4.6 core spec, section 8.4.2 (Transfer from Buffer Objects)
 *   Porth et al. (2019) ApJS 243, 26 (GRMHD simulation conventions)
 */

#pragma once

#include <cstddef>

#include "gl_loader.h"

namespace blackhole {

class GrmhdPBOUploader {
public:
  GrmhdPBOUploader() = default;
  ~GrmhdPBOUploader();

  GrmhdPBOUploader(const GrmhdPBOUploader &) = delete;
  GrmhdPBOUploader &operator=(const GrmhdPBOUploader &) = delete;

  /**
   * @brief Allocate the 3D texture (RGBA32F, empty) and two PBOs.
   *
   * @param width  Voxel grid width
   * @param height Voxel grid height
   * @param depth  Voxel grid depth
   * @return true on success; false if already initialized or GL call fails
   */
  bool init(int width, int height, int depth);

  /**
   * @brief Stage new GRMHD data via PBO and initiate async GPU DMA.
   *
   * On the first call the texture is primed synchronously so that shaders
   * never sample an empty texture.  Subsequent calls use the double-buffered
   * PBO path: CPU fills write PBO while GPU DMAs from read PBO.
   *
   * @param data    Pointer to w*h*d*4 float values (RGBA32F, row-major Z-Y-X)
   * @param nFloats Number of floats (must equal width*height*depth*4)
   * @return true if upload was initiated; false if not initialized or size mismatch
   */
  bool upload(const float *data, std::size_t nFloats);

  /** @brief GLuint for binding as sampler3D in shaders. */
  [[nodiscard]] GLuint texture() const noexcept { return texture_; }

  /** @brief True once at least one upload has completed. */
  [[nodiscard]] bool ready() const noexcept { return uploadCount_ > 0; }

  /** @brief Width of the texture in voxels. */
  [[nodiscard]] int width() const noexcept { return width_; }

  /** @brief Height of the texture in voxels. */
  [[nodiscard]] int height() const noexcept { return height_; }

  /** @brief Depth of the texture in voxels. */
  [[nodiscard]] int depth() const noexcept { return depth_; }

  /** @brief Release all GL resources. Safe to call if not initialized. */
  void shutdown();

private:
  GLuint texture_{0};
  GLuint pbos_[2]{0, 0};
  int width_{0};
  int height_{0};
  int depth_{0};
  std::size_t nFloats_{0}; // width_*height_*depth_*4
  int writeIdx_{0};        // PBO index filled by CPU this frame
  int readIdx_{1};         // PBO index read by GPU this frame
  unsigned uploadCount_{0};
};

} // namespace blackhole
