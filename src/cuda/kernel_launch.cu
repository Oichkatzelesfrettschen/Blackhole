/*
 * kernel_launch.cu
 * Host dispatch: copies LaunchParams to __constant__ memory and launches
 * the selected kernel variant.
 */

#include "kernel_launch.h"
#include "kernel_registry.h"
#include "device_physics.cuh"
#include <cuda_runtime.h>
#include <stdio.h>

/* __constant__ memory: declared extern in device_physics.cuh, defined here.
 * Only ONE translation unit may define each __constant__ symbol under
 * separable compilation -- nvlink enforces this at link time. */
__constant__ float d_rs;
__constant__ float d_spin;
__constant__ float d_isco;
__constant__ float d_step_size;
__constant__ float d_fov_scale;
__constant__ float d_max_dist;
__constant__ float d_cam_pos[3];
__constant__ float d_cam_basis[9];
__constant__ int   d_max_steps;
__constant__ int   d_width;
__constant__ int   d_height;
__constant__ int   d_adisk_enabled;
__constant__ int   d_redshift_enabled;
__constant__ int   d_kerr_enabled;
__constant__ int   d_use_luts;
__constant__ float d_lut_radius_min;
__constant__ float d_lut_radius_max;
__constant__ float d_redshift_radius_min;
__constant__ float d_redshift_radius_max;
__constant__ float d_spectral_radius_min;
__constant__ float d_spectral_radius_max;
__constant__ float d_time_sec;
__constant__ float d_doppler_strength;
__constant__ float d_background_intensity;
__constant__ int   d_background_enabled;

/* External launch wrappers from each kernel file */
extern "C" void launch_fp32_baseline(float4* fb, int w, int h, cudaStream_t s);
extern "C" void launch_fp32_coarsened(float4* fb, int w, int h, cudaStream_t s);
extern "C" void launch_fp16_storage(float4* fb, int w, int h, cudaStream_t s);
extern "C" void launch_fp16_h2_ilp(float4* fb, int w, int h, cudaStream_t s);

/* Upload LaunchParams to __constant__ memory defined above */
static int upload_constants(const struct BH_LaunchParams* p) {
#define COPY_CONST(sym, val)                                                    \
    do {                                                                         \
        auto _v = (val);                                                         \
        cudaError_t err = cudaMemcpyToSymbol(sym, &_v, sizeof(_v));              \
        if (err != cudaSuccess) {                                                \
            fprintf(stderr, "cudaMemcpyToSymbol(%s) failed: %s\n",               \
                    #sym, cudaGetErrorString(err));                               \
            return -1;                                                           \
        }                                                                        \
    } while (0)

    COPY_CONST(d_rs, p->rs);
    COPY_CONST(d_spin, p->spin);
    COPY_CONST(d_isco, p->isco);
    COPY_CONST(d_step_size, p->step_size);
    COPY_CONST(d_fov_scale, p->fov_scale);
    COPY_CONST(d_max_dist, p->max_dist);
    COPY_CONST(d_max_steps, p->max_steps);
    COPY_CONST(d_width, p->width);
    COPY_CONST(d_height, p->height);
    COPY_CONST(d_adisk_enabled, p->adisk_enabled);
    COPY_CONST(d_redshift_enabled, p->redshift_enabled);
    COPY_CONST(d_kerr_enabled, p->kerr_enabled);
    COPY_CONST(d_use_luts, p->use_luts);
    COPY_CONST(d_lut_radius_min, p->lut_radius_min);
    COPY_CONST(d_lut_radius_max, p->lut_radius_max);
    COPY_CONST(d_redshift_radius_min, p->redshift_radius_min);
    COPY_CONST(d_redshift_radius_max, p->redshift_radius_max);
    COPY_CONST(d_spectral_radius_min, p->spectral_radius_min);
    COPY_CONST(d_spectral_radius_max, p->spectral_radius_max);
    COPY_CONST(d_time_sec, p->time_sec);
    COPY_CONST(d_doppler_strength, p->doppler_strength);
    COPY_CONST(d_background_intensity, p->background_intensity);
    COPY_CONST(d_background_enabled, p->background_enabled);

    /* Array copies */
    cudaError_t err;
    err = cudaMemcpyToSymbol(d_cam_pos, p->cam_pos, sizeof(p->cam_pos));
    if (err != cudaSuccess) return -1;
    err = cudaMemcpyToSymbol(d_cam_basis, p->cam_basis, sizeof(p->cam_basis));
    if (err != cudaSuccess) return -1;

#undef COPY_CONST
    return 0;
}

extern "C" int bh_launch_geodesic_kernel(void* framebuffer,
                                          const struct BH_LaunchParams* params,
                                          int variant,
                                          void* stream) {
    if (!framebuffer || !params) return -1;

    /* Auto-select if variant is negative */
    if (variant < 0) {
        variant = registry_select_variant();
    }
    if (variant < 0 || variant >= BH_KERNEL_COUNT) {
        variant = BH_KERNEL_FP32_BASELINE;
    }

    /* Upload parameters to constant memory */
    if (upload_constants(params) != 0) return -1;

    float4* fb = (float4*)framebuffer;
    cudaStream_t s = (cudaStream_t)stream;
    int w = params->width;
    int h = params->height;

    switch (variant) {
        case BH_KERNEL_FP32_BASELINE:
            launch_fp32_baseline(fb, w, h, s);
            break;
        case BH_KERNEL_FP32_COARSENED:
            launch_fp32_coarsened(fb, w, h, s);
            break;
        case BH_KERNEL_FP16_STORAGE:
            launch_fp16_storage(fb, w, h, s);
            break;
        case BH_KERNEL_FP16_H2_ILP:
            launch_fp16_h2_ilp(fb, w, h, s);
            break;
        default:
            launch_fp32_baseline(fb, w, h, s);
            break;
    }

    cudaError_t err = cudaGetLastError();
    if (err != cudaSuccess) {
        fprintf(stderr, "Kernel launch failed: %s\n", cudaGetErrorString(err));
        return -1;
    }

    return 0;
}

extern "C" int bh_select_kernel_variant(void) {
    return registry_select_variant();
}
