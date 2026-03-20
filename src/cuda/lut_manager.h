/*
 * lut_manager.h
 * Manages CUDA texture objects shared from OpenGL LUT textures.
 *
 * Registers GL textures as read-only CUDA texture objects so the
 * tracing kernels can sample LUTs without duplicating data.
 */

#ifndef BLACKHOLE_CUDA_LUT_MANAGER_H
#define BLACKHOLE_CUDA_LUT_MANAGER_H

#include <cuda_runtime.h>

/* LUT slot indices matching the GL texture binding order */
enum BH_LutSlot {
    BH_LUT_EMISSIVITY = 0,
    BH_LUT_REDSHIFT   = 1,
    BH_LUT_SPECTRAL   = 2,
    BH_LUT_GRB        = 3,
    BH_LUT_GALAXY     = 4, /* cubemap */
    BH_LUT_COUNT       = 5
};

struct LutManager {
    cudaGraphicsResource_t resources[BH_LUT_COUNT];
    cudaTextureObject_t    tex_objects[BH_LUT_COUNT];
    bool                   registered[BH_LUT_COUNT];

    LutManager() {
        for (int i = 0; i < BH_LUT_COUNT; ++i) {
            resources[i] = nullptr;
            tex_objects[i] = 0;
            registered[i] = false;
        }
    }
};

/* Register a GL texture as a read-only CUDA texture object.
 * slot: BH_LutSlot index.
 * gl_tex: GL texture ID.
 * gl_target: GL_TEXTURE_2D or GL_TEXTURE_CUBE_MAP. */
int lut_register(LutManager& mgr, int slot, unsigned int gl_tex, unsigned int gl_target);

/* Unregister a slot (e.g., when LUT is regenerated). */
void lut_unregister(LutManager& mgr, int slot);

/* Get the CUDA texture object for a slot (0 if not registered). */
cudaTextureObject_t lut_get_tex(const LutManager& mgr, int slot);

/* Unregister all and cleanup. */
void lut_shutdown(LutManager& mgr);

#endif /* BLACKHOLE_CUDA_LUT_MANAGER_H */
