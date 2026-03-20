/**
 * @file cuda_backend.h
 * @brief High-level CUDA backend API for the Blackhole renderer.
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

/** @brief Opaque handle to the CUDA backend state (interop + LUT manager). */
using BH_CudaBackend = struct BhCudaBackend;

/**
 * @brief Initialize the CUDA backend.
 *
 * Selects the GL-compatible CUDA device, creates streams, and allocates
 * the linear framebuffer.
 *
 * @param glTexture GL texture ID for texBlackhole (RGBA32F).
 * @param width     Initial framebuffer width in pixels.
 * @param height    Initial framebuffer height in pixels.
 * @return Pointer to the allocated backend, or NULL on failure.
 */
BH_CudaBackend *bhCudaInit(unsigned int glTexture, int width, int height);

/**
 * @brief Render a frame: upload params, launch kernel, blit result to GL texture.
 *
 * @param backend Non-null backend handle.
 * @param params  Launch parameters describing scene and camera state.
 * @return 0 on success, non-zero on error.
 */
int bhCudaRenderFrame(BH_CudaBackend *backend, const struct BH_LaunchParams *params);

/**
 * @brief Handle window resize: reallocate framebuffer and re-register GL texture.
 *
 * @param backend   Non-null backend handle.
 * @param glTexture New GL texture ID (may differ from the original after recreation).
 * @param width     New framebuffer width in pixels.
 * @param height    New framebuffer height in pixels.
 * @return 0 on success, non-zero on error.
 */
int bhCudaResize(BH_CudaBackend *backend, unsigned int glTexture, int width, int height);

/**
 * @brief Register a GL LUT texture for sampling in CUDA kernels.
 *
 * @param backend   Non-null backend handle.
 * @param slot      LUT index (0=emissivity, 1=redshift, 2=spectral, 3=grb, 4=galaxy cubemap).
 * @param glTexture GL texture ID.
 * @param target    GL texture target: GL_TEXTURE_2D or GL_TEXTURE_CUBE_MAP.
 * @return 0 on success, non-zero on error.
 */
int bhCudaRegisterLut(BH_CudaBackend *backend, int slot, unsigned int glTexture,
                      unsigned int target);

/**
 * @brief Set the active kernel variant.
 *
 * @param backend Non-null backend handle.
 * @param variant Desired BH_KernelVariant value, or -1 for auto-selection.
 * @return The variant actually selected (may differ if the requested variant is unsupported).
 */
int bhCudaSetVariant(BH_CudaBackend *backend, int variant);

/**
 * @brief Get the currently active kernel variant index.
 *
 * @param backend Non-null backend handle.
 * @return Active BH_KernelVariant value, or -1 if backend is null.
 */
int bhCudaGetVariant(BH_CudaBackend *backend);

/**
 * @brief Shutdown: free all CUDA resources held by the backend.
 *
 * @param backend Backend handle to destroy. Safe to call with NULL.
 */
void bhCudaShutdown(BH_CudaBackend *backend);

#ifdef __cplusplus
}

/**
 * @brief CUDA backend lifecycle state.
 *
 * Bundles the four per-render-session variables that belong together as a
 * single object rather than separate static locals.
 * Initialize as: static BhCudaState cudaState = {nullptr, -1, false, false};
 */
struct BhCudaState {
  BH_CudaBackend *backend; /**< @brief Opaque backend handle; NULL when not initialized. */
  int kernelVariant;       /**< @brief -1 = auto-select; >= 0 = explicit BH_KernelVariant. */
  bool initAttempted;      /**< @brief True after the first init attempt (success or failure). */
  bool enabled;            /**< @brief User UI toggle: use CUDA render path. */
};
#endif /* __cplusplus */

#endif /* BLACKHOLE_CUDA_BACKEND_H */
