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

#include "bh_gl_interop.h"
#include <stdio.h>

#define CUDA_CHECK(call)                                                       \
    do {                                                                        \
        cudaError_t err = (call);                                               \
        if (err != cudaSuccess) {                                               \
            fprintf(stderr, "CUDA error at %s:%d: %s\n", __FILE__, __LINE__,    \
                    cudaGetErrorString(err));                                    \
            return -1;                                                          \
        }                                                                       \
    } while (0)

int interop_init(CudaGLInterop& ctx) {
    /* Find a CUDA device compatible with the current OpenGL context */
    unsigned int gl_device_count = 0;
    int gl_devices[4];
    cudaError_t err = cudaGLGetDevices(&gl_device_count, gl_devices, 4,
                                        cudaGLDeviceListAll);
    if (err != cudaSuccess || gl_device_count == 0) {
        fprintf(stderr, "No CUDA device compatible with OpenGL context\n");
        return -1;
    }

    CUDA_CHECK(cudaSetDevice(gl_devices[0]));
    CUDA_CHECK(cudaStreamCreateWithFlags(&ctx.blit_stream, cudaStreamNonBlocking));

    ctx.initialized = true;
    return 0;
}

int interop_register(CudaGLInterop& ctx, unsigned int gl_tex, int w, int h) {
    if (!ctx.initialized) return -1;

    /* Allocate linear framebuffer */
    size_t fb_size = (size_t)w * h * sizeof(float4);
    CUDA_CHECK(cudaMalloc(&ctx.d_framebuffer, fb_size));
    CUDA_CHECK(cudaMemset(ctx.d_framebuffer, 0, fb_size));

    /* Register GL texture for CUDA access */
    CUDA_CHECK(cudaGraphicsGLRegisterImage(&ctx.gl_resource, gl_tex,
                                            GL_TEXTURE_2D,
                                            cudaGraphicsRegisterFlagsWriteDiscard));

    ctx.width = w;
    ctx.height = h;
    return 0;
}

float4* interop_framebuffer(CudaGLInterop& ctx) {
    return ctx.d_framebuffer;
}

int interop_blit_to_gl(CudaGLInterop& ctx) {
    if (!ctx.d_framebuffer || !ctx.gl_resource) return -1;

    /* Map GL texture for writing */
    CUDA_CHECK(cudaGraphicsMapResources(1, &ctx.gl_resource, ctx.blit_stream));

    cudaArray_t mapped_array;
    CUDA_CHECK(cudaGraphicsSubResourceGetMappedArray(&mapped_array, ctx.gl_resource,
                                                      0, 0));

    /* Copy linear framebuffer to GL texture array.
     * src pitch = width * sizeof(float4) = width * 16 bytes.
     * This is the only place GL resources are touched -- minimal map/unmap window. */
    size_t src_pitch = (size_t)ctx.width * sizeof(float4);
    CUDA_CHECK(cudaMemcpy2DToArrayAsync(
        mapped_array,       /* dst: mapped GL texture array */
        0, 0,               /* dst offset */
        ctx.d_framebuffer,  /* src: linear device memory */
        src_pitch,          /* src pitch */
        src_pitch,          /* width in bytes */
        ctx.height,         /* height in rows */
        cudaMemcpyDeviceToDevice,
        ctx.blit_stream
    ));

    CUDA_CHECK(cudaGraphicsUnmapResources(1, &ctx.gl_resource, ctx.blit_stream));

    /* Sync the blit stream so GL can use the texture immediately */
    CUDA_CHECK(cudaStreamSynchronize(ctx.blit_stream));

    return 0;
}

int interop_resize(CudaGLInterop& ctx, unsigned int gl_tex, int w, int h) {
    if (!ctx.initialized) return -1;

    /* Unregister old GL resource if present */
    if (ctx.gl_resource) {
        cudaGraphicsUnregisterResource(ctx.gl_resource);
        ctx.gl_resource = nullptr;
    }

    /* Free old framebuffer */
    if (ctx.d_framebuffer) {
        cudaFree(ctx.d_framebuffer);
        ctx.d_framebuffer = nullptr;
    }

    /* Re-register with new dimensions */
    return interop_register(ctx, gl_tex, w, h);
}

void interop_shutdown(CudaGLInterop& ctx) {
    if (ctx.gl_resource) {
        cudaGraphicsUnregisterResource(ctx.gl_resource);
        ctx.gl_resource = nullptr;
    }
    if (ctx.d_framebuffer) {
        cudaFree(ctx.d_framebuffer);
        ctx.d_framebuffer = nullptr;
    }
    if (ctx.blit_stream) {
        cudaStreamDestroy(ctx.blit_stream);
        ctx.blit_stream = nullptr;
    }
    ctx.initialized = false;
}
