/*
 * cuda_backend.cu
 * High-level CUDA backend: wraps interop + LUT manager + kernel dispatch.
 *
 * Provides the C API declared in cuda_backend.h for use by main.cpp.
 */

#include "cuda_backend.h"
#include "bh_gl_interop.h"
#include "lut_manager.h"
#include "kernel_registry.h"
#include <stdio.h>
#include <stdlib.h>

struct BH_CudaBackend {
    CudaGLInterop interop;
    LutManager luts;
    int active_variant;
    cudaStream_t compute_stream;
};

extern "C" BH_CudaBackend* bh_cuda_init(unsigned int gl_texture, int width, int height) {
    BH_CudaBackend* b = (BH_CudaBackend*)calloc(1, sizeof(BH_CudaBackend));
    if (!b) return nullptr;

    b->active_variant = -1; /* auto */

    if (interop_init(b->interop) != 0) {
        fprintf(stderr, "bh_cuda_init: interop_init failed\n");
        free(b);
        return nullptr;
    }

    cudaError_t err = cudaStreamCreateWithFlags(&b->compute_stream, cudaStreamNonBlocking);
    if (err != cudaSuccess) {
        fprintf(stderr, "bh_cuda_init: cudaStreamCreate failed: %s\n",
                cudaGetErrorString(err));
        interop_shutdown(b->interop);
        free(b);
        return nullptr;
    }

    if (interop_register(b->interop, gl_texture, width, height) != 0) {
        fprintf(stderr, "bh_cuda_init: interop_register failed\n");
        cudaStreamDestroy(b->compute_stream);
        interop_shutdown(b->interop);
        free(b);
        return nullptr;
    }

    b->active_variant = registry_select_variant();
    const RtKernelInfo* info = registry_get_info(b->active_variant);
    if (info) {
        fprintf(stderr, "CUDA backend: auto-selected variant %d (%s)\n",
                b->active_variant, info->name);
    }

    return b;
}

extern "C" int bh_cuda_render_frame(BH_CudaBackend* backend,
                                     const struct BH_LaunchParams* params) {
    if (!backend || !params) return -1;

    float4* fb = interop_framebuffer(backend->interop);
    if (!fb) return -1;

    int variant = backend->active_variant;
    if (variant < 0) variant = registry_select_variant();

    int rc = bh_launch_geodesic_kernel(fb, params, variant, backend->compute_stream);
    if (rc != 0) return rc;

    /* Sync compute before blit */
    cudaStreamSynchronize(backend->compute_stream);

    return interop_blit_to_gl(backend->interop);
}

extern "C" int bh_cuda_resize(BH_CudaBackend* backend,
                               unsigned int gl_texture, int width, int height) {
    if (!backend) return -1;
    return interop_resize(backend->interop, gl_texture, width, height);
}

extern "C" int bh_cuda_register_lut(BH_CudaBackend* backend,
                                     int slot, unsigned int gl_texture,
                                     unsigned int target) {
    if (!backend) return -1;
    return lut_register(backend->luts, slot, gl_texture, target);
}

extern "C" int bh_cuda_set_variant(BH_CudaBackend* backend, int variant) {
    if (!backend) return -1;
    if (variant < 0) {
        variant = registry_select_variant();
    }
    if (variant >= BH_KERNEL_COUNT) {
        variant = BH_KERNEL_FP32_BASELINE;
    }
    backend->active_variant = variant;
    return variant;
}

extern "C" int bh_cuda_get_variant(BH_CudaBackend* backend) {
    if (!backend) return -1;
    return backend->active_variant;
}

extern "C" void bh_cuda_shutdown(BH_CudaBackend* backend) {
    if (!backend) return;
    lut_shutdown(backend->luts);
    interop_shutdown(backend->interop);
    if (backend->compute_stream) {
        cudaStreamDestroy(backend->compute_stream);
    }
    free(backend);
}
