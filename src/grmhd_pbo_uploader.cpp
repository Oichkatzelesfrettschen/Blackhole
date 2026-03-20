/**
 * @file grmhd_pbo_uploader.cpp
 * @brief Double-buffered PBO upload for GRMHD 3D textures -- implementation.
 *
 * WHY: See grmhd_pbo_uploader.h.  The key correctness points implemented here:
 *
 *   1. Buffer orphaning (glBufferData with nullptr) avoids an implicit GPU sync
 *      when overwriting a PBO that the driver may still be reading.  Requesting
 *      a fresh allocation with GL_STREAM_DRAW lets the driver give us new memory
 *      without waiting for the old DMA to complete.
 *
 *   2. The first upload primes the texture synchronously via glTexSubImage3D
 *      with a CPU pointer (no PBO bound).  This ensures the texture is never
 *      empty/black during the first render frame after a seek.  All subsequent
 *      uploads use the PBO path.
 *
 *   3. The read/write index swap is deferred until after both the CPU fill and
 *      the DMA initiation are complete, so the indices always refer to their
 *      correct roles within a single upload() call.
 *
 * HOW (double-buffer cycle after prime):
 *
 *   Call N (uploadCount_ >= 1):
 *     a. Bind PBO[writeIdx_], orphan, map, memcpy new data, unmap.
 *     b. Bind PBO[readIdx_] to GL_PIXEL_UNPACK_BUFFER.
 *     c. glTexSubImage3D with nullptr offset -> async DMA PBO[readIdx_]->texture.
 *     d. Unbind PBO, swap indices.
 *
 *   The CPU fill (a) and GPU DMA (c) reference different PBOs and can overlap
 *   on systems with a dedicated DMA engine (RTX 3xxx/4xxx, all Ampere/Ada).
 */

// NOLINTBEGIN(misc-include-cleaner)
// glbinding/gl/gl.h is the conventional umbrella header.
#include <glbinding/gl/gl.h>
// NOLINTEND(misc-include-cleaner)

#include <cstring>

#include "grmhd_pbo_uploader.h"

using namespace gl;

namespace blackhole {

// ---------------------------------------------------------------------------
// Destructor
// ---------------------------------------------------------------------------

GrmhdPBOUploader::~GrmhdPBOUploader() {
  shutdown();
}

// ---------------------------------------------------------------------------
// init
// ---------------------------------------------------------------------------

bool GrmhdPBOUploader::init(int width, int height, int depth) {
  if (texture_ != 0) {
    return false; // Already initialized -- caller must shutdown() first
  }
  if (width <= 0 || height <= 0 || depth <= 0) {
    return false;
  }

  width_   = width;
  height_  = height;
  depth_   = depth;
  nFloats_ = static_cast<std::size_t>(width) *
             static_cast<std::size_t>(height) *
             static_cast<std::size_t>(depth) * 4u;

  const std::size_t byteSize = nFloats_ * sizeof(float);

  // 1. Create RGBA32F 3D texture (storage allocated, data uninitialized).
  //    The first upload() call will prime it synchronously.
  glGenTextures(1, &texture_);
  glBindTexture(GL_TEXTURE_3D, texture_);
  glTexImage3D(GL_TEXTURE_3D, 0, GL_RGBA32F,
               width_, height_, depth_,
               0, GL_RGBA, GL_FLOAT, nullptr);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MIN_FILTER, GL_LINEAR);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_MAG_FILTER, GL_LINEAR);
  /* BL coordinate wrap semantics: S=r (clamp), T=theta (mirror), R=phi (repeat). */
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_S, GL_CLAMP_TO_EDGE);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_T, GL_MIRRORED_REPEAT);
  glTexParameteri(GL_TEXTURE_3D, GL_TEXTURE_WRAP_R, GL_REPEAT);
  glBindTexture(GL_TEXTURE_3D, 0);

  // 2. Pre-allocate both PBOs with GL_STREAM_DRAW (CPU-write, GPU-read once).
  glGenBuffers(2, pbos_);
  for (int i = 0; i < 2; ++i) {
    glBindBuffer(GL_PIXEL_UNPACK_BUFFER, pbos_[i]);
    glBufferData(GL_PIXEL_UNPACK_BUFFER,
                 static_cast<GLsizeiptr>(byteSize),
                 nullptr, GL_STREAM_DRAW);
  }
  glBindBuffer(GL_PIXEL_UNPACK_BUFFER, 0);

  writeIdx_ = 0;
  readIdx_  = 1;
  uploadCount_ = 0;
  return true;
}

// ---------------------------------------------------------------------------
// upload
// ---------------------------------------------------------------------------

bool GrmhdPBOUploader::upload(const float *data, std::size_t nFloats) {
  if (texture_ == 0 || data == nullptr) {
    return false;
  }
  if (nFloats != nFloats_) {
    return false; // Size mismatch -- likely wrong frame dimensions
  }

  const std::size_t byteSize = nFloats_ * sizeof(float);

  if (uploadCount_ == 0) {
    /* ----------------------------------------------------------------
     * First upload: prime the texture synchronously so it is never
     * empty when the shader first samples it.  Subsequent calls use
     * the async PBO path.
     * -------------------------------------------------------------- */
    glBindTexture(GL_TEXTURE_3D, texture_);
    glTexSubImage3D(GL_TEXTURE_3D, 0,
                    0, 0, 0,
                    width_, height_, depth_,
                    GL_RGBA, GL_FLOAT, data);
    glBindTexture(GL_TEXTURE_3D, 0);

    /* Also fill PBO[writeIdx_] so the second call has valid data in
     * the read slot (avoids one frame of stale data in the pipeline). */
    glBindBuffer(GL_PIXEL_UNPACK_BUFFER, pbos_[writeIdx_]);
    glBufferData(GL_PIXEL_UNPACK_BUFFER,
                 static_cast<GLsizeiptr>(byteSize),
                 nullptr, GL_STREAM_DRAW); // orphan
    void *ptr = glMapBuffer(GL_PIXEL_UNPACK_BUFFER, GL_WRITE_ONLY);
    if (ptr) {
      std::memcpy(ptr, data, byteSize);
      glUnmapBuffer(GL_PIXEL_UNPACK_BUFFER);
    }
    glBindBuffer(GL_PIXEL_UNPACK_BUFFER, 0);

    std::swap(writeIdx_, readIdx_);
    ++uploadCount_;
    return true;
  }

  /* ------------------------------------------------------------------
   * Steady-state double-buffered PBO path:
   *
   *   a. Orphan PBO[writeIdx_] and fill it from CPU.
   *   b. Bind PBO[readIdx_] and initiate async DMA to the texture.
   *   c. Unbind PBO, swap indices.
   * ---------------------------------------------------------------- */

  // a. Fill the write PBO (orphan to avoid sync on re-use)
  glBindBuffer(GL_PIXEL_UNPACK_BUFFER, pbos_[writeIdx_]);
  glBufferData(GL_PIXEL_UNPACK_BUFFER,
               static_cast<GLsizeiptr>(byteSize),
               nullptr, GL_STREAM_DRAW); // orphan -- new allocation, no stall
  void *ptr = glMapBuffer(GL_PIXEL_UNPACK_BUFFER, GL_WRITE_ONLY);
  if (ptr) {
    std::memcpy(ptr, data, byteSize);
    glUnmapBuffer(GL_PIXEL_UNPACK_BUFFER);
  }
  glBindBuffer(GL_PIXEL_UNPACK_BUFFER, 0);

  // b. Initiate async DMA from the read PBO (filled on the previous call)
  glBindBuffer(GL_PIXEL_UNPACK_BUFFER, pbos_[readIdx_]);
  glBindTexture(GL_TEXTURE_3D, texture_);
  glTexSubImage3D(GL_TEXTURE_3D, 0,
                  0, 0, 0,
                  width_, height_, depth_,
                  GL_RGBA, GL_FLOAT,
                  nullptr); // nullptr = use the bound PBO as source
  glBindTexture(GL_TEXTURE_3D, 0);

  // c. Unbind PBO and rotate indices
  glBindBuffer(GL_PIXEL_UNPACK_BUFFER, 0);
  std::swap(writeIdx_, readIdx_);
  ++uploadCount_;
  return true;
}

// ---------------------------------------------------------------------------
// shutdown
// ---------------------------------------------------------------------------

void GrmhdPBOUploader::shutdown() {
  if (pbos_[0] != 0 || pbos_[1] != 0) {
    glDeleteBuffers(2, pbos_);
    pbos_[0] = 0;
    pbos_[1] = 0;
  }
  if (texture_ != 0) {
    glDeleteTextures(1, &texture_);
    texture_ = 0;
  }
  width_       = 0;
  height_      = 0;
  depth_       = 0;
  nFloats_     = 0;
  writeIdx_    = 0;
  readIdx_     = 1;
  uploadCount_ = 0;
}

} // namespace blackhole
