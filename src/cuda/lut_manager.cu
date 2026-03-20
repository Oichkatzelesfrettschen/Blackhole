/**
 * @file lut_manager.cu
 * @brief Implementation of GL-to-CUDA LUT texture object management.
 *
 * Registers GL textures as CUDA graphics resources, maps them to obtain a
 * cudaArray_t, and creates a cudaTextureObject_t for kernel sampling.
 * Texture objects are cached per slot and only recreated when the LUT changes.
 */

#include <cstdio>

#include <cuda_gl_interop.h>
#include <cuda_runtime_api.h>
#include <driver_types.h>
#include <texture_types.h>

#include "lut_manager.h"

int lutRegister(LutManager &mgr, int slot, unsigned int glTex, unsigned int glTarget) {
  if (slot < 0 || slot >= BhLutCount) {
    return -1;
  }

  /* Unregister previous if re-registering */
  if (mgr.registered[slot]) {
    lutUnregister(mgr, slot);
  }

  /* Register GL image as read-only CUDA resource */
  cudaError_t err = cudaGraphicsGLRegisterImage(&mgr.resources[slot], glTex, glTarget,
                                                cudaGraphicsRegisterFlagsReadOnly);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister slot %d: cudaGraphicsGLRegisterImage failed: %s\n", slot,
                  cudaGetErrorString(err));
    return -1;
  }

  /* Map to get the underlying CUDA array */
  err = cudaGraphicsMapResources(1, &mgr.resources[slot], nullptr);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister slot %d: cudaGraphicsMapResources failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  cudaArray_t array;
  err = cudaGraphicsSubResourceGetMappedArray(&array, mgr.resources[slot], 0, 0);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister slot %d: GetMappedArray failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  /* Create texture object */
  cudaResourceDesc resDesc = {};
  resDesc.resType = cudaResourceTypeArray;
  resDesc.res.array.array = array;

  cudaTextureDesc texDesc = {};
  texDesc.addressMode[0] = cudaAddressModeClamp;
  texDesc.addressMode[1] = cudaAddressModeClamp;
  texDesc.filterMode = cudaFilterModeLinear;
  texDesc.readMode = cudaReadModeElementType;
  texDesc.normalizedCoords = 1;

  err = cudaCreateTextureObject(&mgr.texObjects[slot], &resDesc, &texDesc, nullptr);
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "lutRegister slot %d: cudaCreateTextureObject failed: %s\n", slot,
                  cudaGetErrorString(err));
    cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
    return -1;
  }

  /* Unmap -- texture object remains valid after unmap for read-only resources */
  cudaGraphicsUnmapResources(1, &mgr.resources[slot], nullptr);

  mgr.registered[slot] = true;
  return 0;
}

void lutUnregister(LutManager &mgr, int slot) {
  if (slot < 0 || slot >= BhLutCount) {
    return;
  }
  if (!mgr.registered[slot]) {
    return;
  }

  if (mgr.texObjects[slot] != 0u) {
    cudaDestroyTextureObject(mgr.texObjects[slot]);
    mgr.texObjects[slot] = 0;
  }
  if (mgr.resources[slot] != nullptr) {
    cudaGraphicsUnregisterResource(mgr.resources[slot]);
    mgr.resources[slot] = nullptr;
  }
  mgr.registered[slot] = false;
}

cudaTextureObject_t lutGetTex(const LutManager &mgr, int slot) {
  if (slot < 0 || slot >= BhLutCount) {
    return 0;
  }
  return mgr.texObjects[slot];
}

void lutShutdown(LutManager &mgr) {
  for (int i = 0; i < BhLutCount; ++i) {
    lutUnregister(mgr, i);
  }
}
