/**
 * @file cuda_backend.cu
 * @brief High-level CUDA backend: wraps interop + LUT manager + kernel dispatch.
 *
 * Provides the C API declared in cuda_backend.h for use by main.cpp.
 */

#include "cuda_backend.h"
#include "bh_gl_interop.h"
#include "lut_manager.h"
#include "kernel_launch.h"
#include "kernel_registry.h"
#include <stdio.h>
#include <stdlib.h>

/**
 * @brief Upload all LUT texture objects to __constant__ memory.
 *
 * Pushes handles for all BhLutSlot entries so device kernels can sample any
 * registered LUT without a separate upload step.  Unregistered slots produce
 * 0; device code guards on 0 before sampling.
 *
 * @param luts Reference to the LUT manager holding registered texture objects.
 */
static void sync_lut_constants(const LutManager& luts) {
    bh_upload_lut_textures(
        (unsigned long long)lutGetTex(luts, BhLutEmissivity),
        (unsigned long long)lutGetTex(luts, BhLutRedshift),
        (unsigned long long)lutGetTex(luts, BhLutSpectral),
        (unsigned long long)lutGetTex(luts, BhLutGrb),
        (unsigned long long)lutGetTex(luts, BhLutGalaxy),
        (unsigned long long)lutGetTex(luts, BhLutGrmhd),
        (unsigned long long)lutGetTex(luts, BhLutSynchG),
        (unsigned long long)lutGetTex(luts, BhLutGrmhdRight)
    );
}

/**
 * @brief Internal implementation of the opaque BH_CudaBackend handle.
 *
 * Aggregates all per-session CUDA state: GL interop context, LUT texture
 * manager, the selected kernel variant index, and the dedicated compute stream.
 */
struct BhCudaBackend {
    CudaGLInterop interop;       /**< @brief GL-CUDA interop context and framebuffer. */
    LutManager luts;             /**< @brief Registered GL LUT texture objects. */
    int active_variant;          /**< @brief Active BH_KernelVariant index (-1 = auto). */
    cudaStream_t compute_stream; /**< @brief Non-blocking stream for geodesic kernel launches. */
};

extern "C" BH_CudaBackend* bhCudaInit(unsigned int gl_texture, int width, int height) {
    BH_CudaBackend* b = (BH_CudaBackend*)calloc(1, sizeof(BH_CudaBackend));
    if (!b) return nullptr;

    b->active_variant = -1; /* auto */

    if (interopInit(b->interop) != 0) {
        fprintf(stderr, "bh_cuda_init: interop_init failed\n");
        free(b);
        return nullptr;
    }

    cudaError_t err = cudaStreamCreateWithFlags(&b->compute_stream, cudaStreamNonBlocking);
    if (err != cudaSuccess) {
        fprintf(stderr, "bh_cuda_init: cudaStreamCreate failed: %s\n",
                cudaGetErrorString(err));
        interopShutdown(b->interop);
        free(b);
        return nullptr;
    }

    if (interopRegister(b->interop, gl_texture, width, height) != 0) {
        fprintf(stderr, "bh_cuda_init: interop_register failed\n");
        cudaStreamDestroy(b->compute_stream);
        interopShutdown(b->interop);
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

extern "C" int bhCudaRenderFrame(BH_CudaBackend* backend,
                                     const struct BH_LaunchParams* params) {
    if (!backend || !params) return -1;

    float4* fb = interopFramebuffer(backend->interop);
    if (!fb) return -1;

    int variant = backend->active_variant;
    if (variant < 0) variant = registry_select_variant();

    /* Refresh LUT texture object handles in case they changed since last frame */
    sync_lut_constants(backend->luts);

    int rc = bh_launch_geodesic_kernel(fb, params, variant, backend->compute_stream);
    if (rc != 0) return rc;

    /* Sync compute before blit */
    cudaStreamSynchronize(backend->compute_stream);

    return interopBlitToGl(backend->interop);
}

extern "C" int bhCudaResize(BH_CudaBackend* backend,
                               unsigned int gl_texture, int width, int height) {
    if (!backend) return -1;
    return interopResize(backend->interop, gl_texture, width, height);
}

extern "C" int bhCudaRegisterLut(BH_CudaBackend* backend,
                                     int slot, unsigned int gl_texture,
                                     unsigned int target) {
    if (!backend) return -1;
    int rc = lutRegister(backend->luts, slot, gl_texture, target);
    if (rc == 0) {
        /* Keep __constant__ in sync so next frame picks up the new texture */
        sync_lut_constants(backend->luts);
    }
    return rc;
}

extern "C" int bhCudaSetVariant(BH_CudaBackend* backend, int variant) {
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

extern "C" int bhCudaGetVariant(BH_CudaBackend* backend) {
    if (!backend) return -1;
    return backend->active_variant;
}

extern "C" void bhCudaShutdown(BH_CudaBackend* backend) {
    if (!backend) return;
    lutShutdown(backend->luts);
    interopShutdown(backend->interop);
    if (backend->compute_stream) {
        cudaStreamDestroy(backend->compute_stream);
    }
    free(backend);
}
