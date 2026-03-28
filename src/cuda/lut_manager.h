/**
 * @file lut_manager.h
 * @brief Manages CUDA texture objects shared from OpenGL LUT textures.
 *
 * Registers GL textures as read-only CUDA texture objects so the tracing
 * kernels can sample physics LUTs (emissivity, redshift, spectral, GRB,
 * galaxy cubemap) without duplicating data on the device.
 */

#ifndef BLACKHOLE_CUDA_LUT_MANAGER_H
#define BLACKHOLE_CUDA_LUT_MANAGER_H

#include <driver_types.h>  /* cudaGraphicsResource_t */
#include <texture_types.h> /* cudaTextureObject_t */

/**
 * @brief LUT slot indices matching the GL texture binding order.
 *
 * Unscoped enum: the C API surface (bhCudaRegisterLut, lutRegister) takes an
 * int slot, so scoped enum values would require static_cast at every call site.
 */
enum BhLutSlot { // NOLINT(cppcoreguidelines-use-enum-class)
  BhLutEmissivity = 0, /**< @brief Accretion disk emissivity flux LUT. */
  BhLutRedshift   = 1, /**< @brief Gravitational redshift factor LUT. */
  BhLutSpectral   = 2, /**< @brief Spectral modulation LUT. */
  BhLutGrb        = 3, /**< @brief Gamma-ray burst overlay LUT. */
  BhLutGalaxy     = 4, /**< @brief Galaxy cubemap background texture. */
  BhLutGrmhd      = 5, /**< @brief GRMHD simulation volume left frame (RGBA32F 3D texture). */
  BhLutSynchG     = 6, /**< @brief Synchrotron G(x) = x*K_{2/3}(x) polarization LUT (R32F 2D, height=1). */
  BhLutGrmhdRight = 7, /**< @brief GRMHD simulation volume right frame for time interpolation (RGBA32F 3D). */
  BhLutCount      = 8  /**< @brief Sentinel: total number of LUT slots. */
};

/**
 * @brief Holds CUDA graphics resources and texture objects for all LUT slots.
 *
 * For 2D slots (emissivity, redshift, spectral, GRB) the texture object wraps
 * the mapped GL array directly.  For cubemap slots (galaxy, slot 4) the
 * registration path allocates a new 6-layer cudaArray owned by this struct;
 * @c layeredArrays holds that pointer and lutUnregister() frees it.
 *
 * Slots that have not been registered hold nullptr / 0 / false.
 */
struct LutManager {
  cudaGraphicsResource_t resources[BhLutCount]{};    /**< @brief Per-slot registered GL resources. */
  cudaTextureObject_t texObjects[BhLutCount]{};      /**< @brief Per-slot CUDA texture objects (0 = unregistered). */
  cudaArray_t layeredArrays[BhLutCount]{};           /**< @brief Owned 6-layer arrays for cubemap slots (null for 2D slots). */
  bool registered[BhLutCount]{};                     /**< @brief True when the slot holds a valid texture object. */
  cudaGraphicsResource_t backgroundResource{};       /**< @brief Optional standalone equirect background GL resource. */
  cudaTextureObject_t backgroundTexture{};           /**< @brief CUDA texture object for the standalone equirect background. */
  bool backgroundRegistered{};                       /**< @brief True when the standalone background texture is valid. */

  LutManager() {
    for (int i = 0; i < BhLutCount; ++i) {
      resources[i]     = nullptr;
      texObjects[i]    = 0;
      layeredArrays[i] = nullptr;
      registered[i]    = false;
    }
    backgroundResource = nullptr;
    backgroundTexture = 0;
    backgroundRegistered = false;
  }
};

/**
 * @brief Register a GL texture as a read-only CUDA texture object.
 *
 * If the slot was previously registered, it is unregistered first.
 * The GL texture remains mapped in CUDA read-only mode; the texture object
 * is valid for device sampling until lutUnregister() or lutShutdown() is called.
 *
 * @param mgr      LUT manager to update.
 * @param slot     BhLutSlot index.
 * @param glTex    GL texture ID.
 * @param glTarget GL texture target: GL_TEXTURE_2D or GL_TEXTURE_CUBE_MAP.
 * @return 0 on success, -1 on invalid slot or any CUDA error.
 */
int lutRegister(LutManager &mgr, int slot, unsigned int glTex, unsigned int glTarget);

/**
 * @brief Unregister a single LUT slot and destroy its texture object.
 *
 * @param mgr  LUT manager.
 * @param slot BhLutSlot index of the slot to release.
 */
void lutUnregister(LutManager &mgr, int slot);

/**
 * @brief Get the CUDA texture object for a slot.
 *
 * @param mgr  LUT manager.
 * @param slot BhLutSlot index.
 * @return cudaTextureObject_t for the slot, or 0 if not registered or out of range.
 */
cudaTextureObject_t lutGetTex(const LutManager &mgr, int slot);

/**
 * @brief Register a standalone GL_TEXTURE_2D background for layered equirect sampling.
 *
 * This is intentionally separate from the BhLutSlot table because the desktop
 * renderer already consumes all numbered LUT slots. The registered texture is
 * uploaded to the dedicated d_tex_background_equirect constant.
 *
 * @param mgr      LUT manager to update.
 * @param glTex    GL texture ID.
 * @param glTarget GL texture target (must be GL_TEXTURE_2D).
 * @return 0 on success, -1 on error.
 */
int lutRegisterBackground(LutManager &mgr, unsigned int glTex, unsigned int glTarget);

/**
 * @brief Unregister the standalone background texture.
 *
 * @param mgr LUT manager.
 */
void lutUnregisterBackground(LutManager &mgr);

/**
 * @brief Get the standalone background texture object, or 0 if unavailable.
 *
 * @param mgr LUT manager.
 * @return cudaTextureObject_t for the standalone background texture.
 */
cudaTextureObject_t lutGetBackgroundTex(const LutManager &mgr);

/**
 * @brief Unregister all slots and free all CUDA LUT resources.
 *
 * @param mgr LUT manager to shut down.
 */
void lutShutdown(LutManager &mgr);

#endif /* BLACKHOLE_CUDA_LUT_MANAGER_H */
