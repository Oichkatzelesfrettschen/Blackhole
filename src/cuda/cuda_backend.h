/*
 * cuda_backend.h
 * High-level CUDA backend API for the Blackhole renderer.
 *
 * FIREWALL: This header is included by C++23 host code (main.cpp) but must
 * NOT include any CUDA runtime headers. It only declares opaque types and
 * POD-parameter functions that the .cu translation units implement.
 */

#ifndef BLACKHOLE_CUDA_BACKEND_H
#define BLACKHOLE_CUDA_BACKEND_H

#include "kernel_launch.h"

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque handle to the CUDA backend state (interop + LUT manager). */
using BH_CudaBackend = struct BhCudaBackend;

/* Initialize the CUDA backend. Selects the GL-compatible CUDA device,
 * creates streams, allocates the linear framebuffer.
 * gl_texture: the GL texture ID for texBlackhole (RGBA32F).
 * width, height: initial framebuffer dimensions.
 * Returns NULL on failure. */
BH_CudaBackend *bhCudaInit(unsigned int glTexture, int width, int height);

/* Render a frame: upload params, launch kernel, blit result to GL texture.
 * Returns 0 on success. */
int bhCudaRenderFrame(BH_CudaBackend *backend, const struct BH_LaunchParams *params);

/* Handle window resize: reallocate framebuffer, re-register GL texture.
 * gl_texture: the new GL texture ID (may differ after recreation).
 * Returns 0 on success. */
int bhCudaResize(BH_CudaBackend *backend, unsigned int glTexture, int width, int height);

/* Register a GL LUT texture for sampling in CUDA kernels.
 * slot: LUT index (0=emissivity, 1=redshift, 2=spectral, 3=grb, 4=galaxy cubemap).
 * gl_texture: GL texture ID.
 * target: GL_TEXTURE_2D or GL_TEXTURE_CUBE_MAP.
 * Returns 0 on success. */
int bhCudaRegisterLut(BH_CudaBackend *backend, int slot, unsigned int glTexture,
                      unsigned int target);

/* Set the active kernel variant. Pass -1 for auto-selection.
 * Returns the variant actually selected (may differ if requested is unsupported). */
int bhCudaSetVariant(BH_CudaBackend *backend, int variant);

/* Get the currently active kernel variant. */
int bhCudaGetVariant(BH_CudaBackend *backend);

/* Shutdown: free all CUDA resources. */
void bhCudaShutdown(BH_CudaBackend *backend);

#ifdef __cplusplus
}

/* CUDA backend lifecycle state: bundles the 4 per-render-session variables
 * that belong together as a single object rather than separate static locals.
 * Initialize as: static BhCudaState cudaState = {nullptr, -1, false, false}; */
struct BhCudaState {
  BH_CudaBackend *backend; /* NULL when not initialized */
  int kernelVariant;       /* -1 = auto-select; >= 0 = explicit variant */
  bool initAttempted;      /* true after first init attempt (success or fail) */
  bool enabled;            /* user UI toggle: use CUDA render path */
};
#endif /* __cplusplus */

#endif /* BLACKHOLE_CUDA_BACKEND_H */
