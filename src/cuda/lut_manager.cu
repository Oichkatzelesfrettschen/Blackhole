/*
 * lut_manager.cu
 * Implementation of GL-to-CUDA LUT texture object management.
 *
 * Registers GL textures as CUDA graphics resources, maps them to get
 * cudaArray_t, and creates cudaTextureObject_t for kernel sampling.
 * Texture objects are cached and only recreated when the LUT changes.
 */

#include "lut_manager.h"
#include <cuda_gl_interop.h>
#include <stdio.h>

int lut_register(LutManager& mgr, int slot, unsigned int gl_tex, unsigned int gl_target) {
    if (slot < 0 || slot >= BH_LUT_COUNT) return -1;

    /* Unregister previous if re-registering */
    if (mgr.registered[slot]) {
        lut_unregister(mgr, slot);
    }

    /* Register GL image as read-only CUDA resource */
    cudaError_t err = cudaGraphicsGLRegisterImage(
        &mgr.resources[slot], gl_tex, gl_target,
        cudaGraphicsRegisterFlagsReadOnly
    );
    if (err != cudaSuccess) {
        fprintf(stderr, "lut_register slot %d: cudaGraphicsGLRegisterImage failed: %s\n",
                slot, cudaGetErrorString(err));
        return -1;
    }

    /* Map to get the underlying CUDA array */
    err = cudaGraphicsMapResources(1, &mgr.resources[slot], 0);
    if (err != cudaSuccess) {
        fprintf(stderr, "lut_register slot %d: cudaGraphicsMapResources failed: %s\n",
                slot, cudaGetErrorString(err));
        cudaGraphicsUnregisterResource(mgr.resources[slot]);
        mgr.resources[slot] = nullptr;
        return -1;
    }

    cudaArray_t array;
    err = cudaGraphicsSubResourceGetMappedArray(&array, mgr.resources[slot], 0, 0);
    if (err != cudaSuccess) {
        fprintf(stderr, "lut_register slot %d: GetMappedArray failed: %s\n",
                slot, cudaGetErrorString(err));
        cudaGraphicsUnmapResources(1, &mgr.resources[slot], 0);
        cudaGraphicsUnregisterResource(mgr.resources[slot]);
        mgr.resources[slot] = nullptr;
        return -1;
    }

    /* Create texture object */
    cudaResourceDesc res_desc = {};
    res_desc.resType = cudaResourceTypeArray;
    res_desc.res.array.array = array;

    cudaTextureDesc tex_desc = {};
    tex_desc.addressMode[0] = cudaAddressModeClamp;
    tex_desc.addressMode[1] = cudaAddressModeClamp;
    tex_desc.filterMode = cudaFilterModeLinear;
    tex_desc.readMode = cudaReadModeElementType;
    tex_desc.normalizedCoords = 1;

    err = cudaCreateTextureObject(&mgr.tex_objects[slot], &res_desc, &tex_desc, nullptr);
    if (err != cudaSuccess) {
        fprintf(stderr, "lut_register slot %d: cudaCreateTextureObject failed: %s\n",
                slot, cudaGetErrorString(err));
        cudaGraphicsUnmapResources(1, &mgr.resources[slot], 0);
        cudaGraphicsUnregisterResource(mgr.resources[slot]);
        mgr.resources[slot] = nullptr;
        return -1;
    }

    /* Unmap -- texture object remains valid after unmap for read-only resources */
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], 0);

    mgr.registered[slot] = true;
    return 0;
}

void lut_unregister(LutManager& mgr, int slot) {
    if (slot < 0 || slot >= BH_LUT_COUNT) return;
    if (!mgr.registered[slot]) return;

    if (mgr.tex_objects[slot]) {
        cudaDestroyTextureObject(mgr.tex_objects[slot]);
        mgr.tex_objects[slot] = 0;
    }
    if (mgr.resources[slot]) {
        cudaGraphicsUnregisterResource(mgr.resources[slot]);
        mgr.resources[slot] = nullptr;
    }
    mgr.registered[slot] = false;
}

cudaTextureObject_t lut_get_tex(const LutManager& mgr, int slot) {
    if (slot < 0 || slot >= BH_LUT_COUNT) return 0;
    return mgr.tex_objects[slot];
}

void lut_shutdown(LutManager& mgr) {
    for (int i = 0; i < BH_LUT_COUNT; ++i) {
        lut_unregister(mgr, i);
    }
}
