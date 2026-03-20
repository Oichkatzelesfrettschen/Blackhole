/*
 * cuda_gl_interop.cu
 * Implementation of CUDA-OpenGL interop with linear framebuffer + async blit.
 *
 * Architecture:
 *   [Kernel] -> d_framebuffer (linear, coalesced) -> [Blit] -> GL texture (tiled)
 *
 * The physics kernel NEVER writes to a surface object. Only the blit touches
 * GL resources, keeping the map/unmap window minimal.
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

float4 *interopFramebuffer(CudaGLInterop &ctx) {
  return ctx.dFramebuffer;
}

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
