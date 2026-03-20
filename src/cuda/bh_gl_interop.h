/**
 * @file bh_gl_interop.h
 * @brief CUDA-OpenGL interop: linear device framebuffer + async blit to GL texture.
 *
 * The physics kernel writes to a linear float4* device buffer (perfectly
 * coalesced). A separate blit step copies to the GL texture's tiled memory,
 * keeping the map/unmap window to ~0.1 ms (vs 2-10 ms for the kernel).
 *
 * Named bh_gl_interop.h (not cuda_gl_interop.h) to avoid shadowing the CUDA
 * toolkit's own <cuda_gl_interop.h> under -I src/cuda.
 */

#ifndef BLACKHOLE_BH_GL_INTEROP_H
#define BLACKHOLE_BH_GL_INTEROP_H

#include <cuda_runtime.h>
#include <cuda_gl_interop.h>

/**
 * @brief CUDA-GL interop context holding all resources for one render target.
 *
 * The linear framebuffer receives kernel output; the GL resource and blit
 * stream are used exclusively by interopBlitToGl() to minimize the map/unmap
 * window on the OpenGL side.
 */
struct CudaGLInterop {
  float4 *dFramebuffer;              /**< @brief Linear device memory; kernel writes output here. */
  cudaGraphicsResource_t glResource; /**< @brief Registered GL texture for blit destination. */
  cudaStream_t blitStream;           /**< @brief Dedicated non-blocking stream for async blit. */
  int width;                         /**< @brief Framebuffer width in pixels. */
  int height;                        /**< @brief Framebuffer height in pixels. */
  bool initialized;                  /**< @brief True after a successful interopInit() call. */

  CudaGLInterop()
      : dFramebuffer(nullptr), glResource(nullptr), blitStream(nullptr), width(0), height(0),
        initialized(false) {}
};

/**
 * @brief Initialize CUDA device (GL-compatible) and create the blit stream.
 * @param ctx Context to initialize.
 * @return 0 on success, -1 on error.
 */
int interopInit(CudaGLInterop &ctx);

/**
 * @brief Register a GL texture and allocate the linear device framebuffer.
 * @param ctx   Initialized interop context.
 * @param glTex GL texture ID (GL_RGBA32F).
 * @param w     Width in pixels.
 * @param h     Height in pixels.
 * @return 0 on success, -1 on error.
 */
int interopRegister(CudaGLInterop &ctx, unsigned int glTex, int w, int h);

/**
 * @brief Return the linear device framebuffer pointer for kernel writes.
 * @param ctx Interop context.
 * @return Device pointer to float4[width*height].
 */
float4 *interopFramebuffer(CudaGLInterop &ctx);

/**
 * @brief Blit the linear framebuffer to the registered GL texture.
 *
 * Maps GL texture, copies via cudaMemcpy2DToArrayAsync, unmaps, and syncs.
 *
 * @param ctx Interop context with a populated framebuffer.
 * @return 0 on success, -1 on error.
 */
int interopBlitToGl(CudaGLInterop &ctx);

/**
 * @brief Handle window resize: free old resources and re-register at new dimensions.
 * @param ctx   Interop context to resize.
 * @param glTex New GL texture ID.
 * @param w     New width in pixels.
 * @param h     New height in pixels.
 * @return 0 on success, -1 on error.
 */
int interopResize(CudaGLInterop &ctx, unsigned int glTex, int w, int h);

/**
 * @brief Free all CUDA resources held by the interop context.
 * @param ctx Context to shut down.
 */
void interopShutdown(CudaGLInterop &ctx);

#endif /* BLACKHOLE_BH_GL_INTEROP_H */
