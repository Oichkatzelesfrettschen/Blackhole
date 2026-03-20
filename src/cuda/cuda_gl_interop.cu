/**
 * @file cuda_gl_interop.cu
 * @brief CUDA-OpenGL interop: linear framebuffer + async blit to GL texture.
 *
 * Architecture:
 *   [Kernel] -> d_framebuffer (linear, coalesced) -> [Blit] -> GL texture (tiled)
 *
 * The physics kernel never writes to a surface object. Only the blit step
 * touches GL-registered resources, keeping the map/unmap window to ~0.1 ms.
 */

#include <cstdio>

#include <GL/gl.h>
#include <cuda_runtime.h>
#include <cuda_runtime_api.h>
#include <driver_types.h>
#include <vector_types.h>

#include "bh_gl_interop.h"

// NOLINTNEXTLINE(cppcoreguidelines-macro-usage) -- standard CUDA error-check pattern
#define CUDA_CHECK(call)                                                                           \
  do {                              /* NOLINT(cppcoreguidelines-avoid-do-while) */                 \
    cudaError_t const err = (call); /* NOLINT(misc-const-correctness) */                           \
    if (err != cudaSuccess) {                                                                      \
      (void)fprintf(stderr, "CUDA error at %s:%d: %s\n", __FILE__, __LINE__,                       \
                    cudaGetErrorString(err)); /* NOLINT(cert-err33-c) */                           \
      return -1;                                                                                   \
    }                                                                                              \
  } while (0) /* NOLINT(cppcoreguidelines-avoid-do-while) */

/**
 * @brief Initialize the CUDA-GL interop context.
 *
 * Enumerates CUDA devices compatible with the current OpenGL context, sets
 * the first matching device as active, and creates a non-blocking blit stream.
 *
 * @param ctx Reference to the interop context to initialize.
 * @return 0 on success, -1 if no compatible CUDA device is found or stream creation fails.
 */
int interopInit(CudaGLInterop &ctx) {
  /* Find a CUDA device compatible with the current OpenGL context */
  unsigned int glDeviceCount = 0;
  int glDevices[4];
  cudaError_t const err = cudaGLGetDevices(&glDeviceCount, glDevices, 4, cudaGLDeviceListAll);
  if (err != cudaSuccess || glDeviceCount == 0) {
    (void)fprintf(stderr, "No CUDA device compatible with OpenGL context\n");
    return -1;
  }

  CUDA_CHECK(cudaSetDevice(glDevices[0]));
  CUDA_CHECK(cudaStreamCreateWithFlags(&ctx.blitStream, cudaStreamNonBlocking));

  ctx.initialized = true;
  return 0;
}

/**
 * @brief Register a GL texture and allocate the linear device framebuffer.
 *
 * Allocates a float4[w*h] device buffer for kernel output and registers the
 * GL texture as a writable CUDA graphics resource.
 *
 * @param ctx   Initialized interop context.
 * @param glTex GL texture ID (GL_RGBA32F) to register.
 * @param w     Framebuffer width in pixels.
 * @param h     Framebuffer height in pixels.
 * @return 0 on success, -1 on any CUDA error.
 */
int interopRegister(CudaGLInterop &ctx, unsigned int glTex, int w, int h) {
  if (!ctx.initialized) {
    return -1;
  }

  /* Allocate linear framebuffer */
  size_t const fbSize = static_cast<size_t>(w) * h * sizeof(float4);
  CUDA_CHECK(cudaMalloc(&ctx.dFramebuffer, fbSize));
  CUDA_CHECK(cudaMemset(ctx.dFramebuffer, 0, fbSize));

  /* Register GL texture for CUDA access */
  CUDA_CHECK(cudaGraphicsGLRegisterImage(&ctx.glResource, glTex, GL_TEXTURE_2D,
                                         cudaGraphicsRegisterFlagsWriteDiscard));

  ctx.width = w;
  ctx.height = h;
  return 0;
}

/**
 * @brief Return the linear device framebuffer pointer for kernel writes.
 *
 * @param ctx Interop context holding the allocated framebuffer.
 * @return Device pointer to float4[width*height], or nullptr if not allocated.
 */
float4 *interopFramebuffer(CudaGLInterop &ctx) {
  return ctx.dFramebuffer;
}

/**
 * @brief Blit the linear device framebuffer to the registered GL texture.
 *
 * Maps the GL texture, copies via cudaMemcpy2DToArrayAsync on the blit stream,
 * unmaps, then synchronizes the blit stream so GL can use the texture immediately.
 *
 * @param ctx Interop context with a populated linear framebuffer.
 * @return 0 on success, -1 if framebuffer or resource pointers are null, or on CUDA error.
 */
int interopBlitToGl(CudaGLInterop &ctx) {
  if ((ctx.dFramebuffer == nullptr) || (ctx.glResource == nullptr)) {
    return -1;
  }

  /* Map GL texture for writing */
  CUDA_CHECK(cudaGraphicsMapResources(1, &ctx.glResource, ctx.blitStream));

  cudaArray_t mappedArray;
  CUDA_CHECK(cudaGraphicsSubResourceGetMappedArray(&mappedArray, ctx.glResource, 0, 0));

  /* Copy linear framebuffer to GL texture array.
   * src pitch = width * sizeof(float4) = width * 16 bytes.
   * This is the only place GL resources are touched -- minimal map/unmap window. */
  size_t const srcPitch = static_cast<size_t>(ctx.width) * sizeof(float4);
  CUDA_CHECK(cudaMemcpy2DToArrayAsync(mappedArray,      /* dst: mapped GL texture array */
                                      0, 0,             /* dst offset */
                                      ctx.dFramebuffer, /* src: linear device memory */
                                      srcPitch,         /* src pitch */
                                      srcPitch,         /* width in bytes */
                                      ctx.height,       /* height in rows */
                                      cudaMemcpyDeviceToDevice, ctx.blitStream));

  CUDA_CHECK(cudaGraphicsUnmapResources(1, &ctx.glResource, ctx.blitStream));

  /* Sync the blit stream so GL can use the texture immediately */
  CUDA_CHECK(cudaStreamSynchronize(ctx.blitStream));

  return 0;
}

/**
 * @brief Handle a window resize: free old resources and re-register at new dimensions.
 *
 * @param ctx   Interop context to resize.
 * @param glTex New GL texture ID (may differ from the original after recreation).
 * @param w     New framebuffer width in pixels.
 * @param h     New framebuffer height in pixels.
 * @return 0 on success, -1 if context is not initialized or re-registration fails.
 */
int interopResize(CudaGLInterop &ctx, unsigned int glTex, int w, int h) {
  if (!ctx.initialized) {
    return -1;
  }

  /* Unregister old GL resource if present */
  if (ctx.glResource != nullptr) {
    cudaGraphicsUnregisterResource(ctx.glResource);
    ctx.glResource = nullptr;
  }

  /* Free old framebuffer */
  if (ctx.dFramebuffer != nullptr) {
    cudaFree(ctx.dFramebuffer);
    ctx.dFramebuffer = nullptr;
  }

  /* Re-register with new dimensions */
  return interopRegister(ctx, glTex, w, h);
}

/**
 * @brief Free all CUDA resources held by the interop context.
 *
 * Unregisters the GL resource, frees device framebuffer memory, destroys the
 * blit stream, and resets the initialized flag.
 *
 * @param ctx Interop context to shut down.
 */
void interopShutdown(CudaGLInterop &ctx) {
  if (ctx.glResource != nullptr) {
    cudaGraphicsUnregisterResource(ctx.glResource);
    ctx.glResource = nullptr;
  }
  if (ctx.dFramebuffer != nullptr) {
    cudaFree(ctx.dFramebuffer);
    ctx.dFramebuffer = nullptr;
  }
  if (ctx.blitStream != nullptr) {
    cudaStreamDestroy(ctx.blitStream);
    ctx.blitStream = nullptr;
  }
  ctx.initialized = false;
}
