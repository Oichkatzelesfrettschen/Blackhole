/*
 * bh_gl_interop.h
 * CUDA-OpenGL interop: linear framebuffer + async blit to GL texture.
 *
 * The physics kernel writes to a linear float4* device buffer (perfectly
 * coalesced). A separate blit step copies to the GL texture's tiled memory.
 * This keeps the map/unmap window minimal (~0.1ms blit vs 2-10ms kernel).
 *
 * NOTE: Named bh_gl_interop.h (not cuda_gl_interop.h) to avoid shadowing the
 * CUDA toolkit's own <cuda_gl_interop.h> under -I src/cuda.
 */

#ifndef BLACKHOLE_BH_GL_INTEROP_H
#define BLACKHOLE_BH_GL_INTEROP_H

#include <cuda_runtime.h>
#include <cuda_gl_interop.h>

struct CudaGLInterop {
    float4* d_framebuffer;              /* Linear device memory for kernel output */
    cudaGraphicsResource_t gl_resource; /* Registered GL texture */
    cudaStream_t blit_stream;           /* Dedicated stream for async blit */
    int width;
    int height;
    bool initialized;

    CudaGLInterop()
        : d_framebuffer(nullptr), gl_resource(nullptr),
          blit_stream(nullptr), width(0), height(0), initialized(false) {}
};

/* Initialize CUDA device (GL-compatible), create blit stream. */
int interop_init(CudaGLInterop& ctx);

/* Register a GL texture and allocate the linear framebuffer.
 * gl_tex: GL texture ID (GL_RGBA32F).
 * w, h: dimensions. */
int interop_register(CudaGLInterop& ctx, unsigned int gl_tex, int w, int h);

/* Returns the linear device framebuffer pointer for kernel writes. */
float4* interop_framebuffer(CudaGLInterop& ctx);

/* Blit linear framebuffer to the registered GL texture.
 * Maps GL texture, copies via cudaMemcpy2DToArrayAsync, unmaps. */
int interop_blit_to_gl(CudaGLInterop& ctx);

/* Handle resize: free old framebuffer, re-register new GL texture. */
int interop_resize(CudaGLInterop& ctx, unsigned int gl_tex, int w, int h);

/* Free all CUDA resources. */
void interop_shutdown(CudaGLInterop& ctx);

#endif /* BLACKHOLE_BH_GL_INTEROP_H */
