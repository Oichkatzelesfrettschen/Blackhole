/*
 * lut_manager.h
 * Manages CUDA texture objects shared from OpenGL LUT textures.
 *
 * Registers GL textures as read-only CUDA texture objects so the
 * tracing kernels can sample LUTs without duplicating data.
 */

#ifndef BLACKHOLE_CUDA_LUT_MANAGER_H
#define BLACKHOLE_CUDA_LUT_MANAGER_H

#include <driver_types.h>  /* cudaGraphicsResource_t */
#include <texture_types.h> /* cudaTextureObject_t */

/* LUT slot indices matching the GL texture binding order.
 * NOLINT(cppcoreguidelines-use-enum-class): unscoped enum intentional --
 * the C API surface (bhCudaRegisterLut, lutRegister) takes int slot, so
 * scoped enum values would require static_cast at every call site. */
enum BhLutSlot { // NOLINT(cppcoreguidelines-use-enum-class)
  BhLutEmissivity = 0,
  BhLutRedshift = 1,
  BhLutSpectral = 2,
  BhLutGrb = 3,
  BhLutGalaxy = 4, /* cubemap */
  BhLutCount = 5
};

struct LutManager {
  cudaGraphicsResource_t resources[BhLutCount]{};
  cudaTextureObject_t texObjects[BhLutCount]{};
  bool registered[BhLutCount]{};

  LutManager() {
    for (int i = 0; i < BhLutCount; ++i) {
      resources[i] = nullptr;
      texObjects[i] = 0;
      registered[i] = false;
    }
  }
};

/* Register a GL texture as a read-only CUDA texture object.
 * slot: BH_LutSlot index.
 * gl_tex: GL texture ID.
 * gl_target: GL_TEXTURE_2D or GL_TEXTURE_CUBE_MAP. */
int lutRegister(LutManager &mgr, int slot, unsigned int glTex, unsigned int glTarget);

/* Unregister a slot (e.g., when LUT is regenerated). */
void lutUnregister(LutManager &mgr, int slot);

/* Get the CUDA texture object for a slot (0 if not registered). */
cudaTextureObject_t lutGetTex(const LutManager &mgr, int slot);

/* Unregister all and cleanup. */
void lutShutdown(LutManager &mgr);

#endif /* BLACKHOLE_CUDA_LUT_MANAGER_H */
