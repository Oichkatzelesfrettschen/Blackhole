/*
 * kernel_launch.h
 * POD-only C-compatible interface between C++23 host code and C++17 CUDA code.
 *
 * FIREWALL: This header must compile with a plain C compiler.
 * NO std:: types, NO glm::, NO templates, NO C++ containers.
 * Only plain C structs, fixed-size arrays, and function declarations.
 */

#ifndef BLACKHOLE_CUDA_KERNEL_LAUNCH_H
#define BLACKHOLE_CUDA_KERNEL_LAUNCH_H

#ifdef __cplusplus
extern "C" {
#endif

/* All parameters needed by the geodesic tracing kernel.
 * Filled by main.cpp from its C++23 InteropUniforms / glm types. */
struct BH_LaunchParams {
    /* Black hole parameters */
    float rs;           /* Schwarzschild radius */
    float spin;         /* Kerr spin parameter a/M (dimensionless, 0..1) */
    float isco;         /* ISCO radius */
    float step_size;    /* Integration step size */
    float fov_scale;    /* Field of view scale factor */
    float max_dist;     /* Maximum ray travel distance */

    /* Camera */
    float cam_pos[3];       /* Camera position (x,y,z) */
    float cam_basis[9];     /* Camera basis matrix (3x3, column-major like glm) */

    /* Integration */
    int max_steps;      /* Maximum integration steps per ray */
    int width;          /* Framebuffer width */
    int height;         /* Framebuffer height */

    /* Feature flags (int for C compat, 0=off, 1=on) */
    int adisk_enabled;
    int redshift_enabled;
    int kerr_enabled;
    int use_luts;

    /* LUT domain bounds */
    float lut_radius_min;
    float lut_radius_max;
    float redshift_radius_min;
    float redshift_radius_max;
    float spectral_radius_min;
    float spectral_radius_max;

    /* Time */
    float time_sec;

    /* Doppler / beaming */
    float doppler_strength;

    /* Background */
    float background_intensity;
    int background_enabled;
};

/* Kernel variant selection */
enum BH_KernelVariant {
    BH_KERNEL_FP32_BASELINE = 0,
    BH_KERNEL_FP32_COARSENED = 1,
    BH_KERNEL_FP16_STORAGE = 2,
    BH_KERNEL_FP16_H2_ILP = 3,
    BH_KERNEL_COUNT = 4
};

/* Launch a geodesic tracing kernel into the given linear framebuffer.
 * framebuffer: device pointer to float4[width*height] (linear memory).
 * params: launch parameters (will be copied to __constant__ memory).
 * variant: which kernel to run (auto-selected if negative).
 * stream: CUDA stream handle (pass NULL/0 for default stream). */
int bh_launch_geodesic_kernel(void* framebuffer,
                              const struct BH_LaunchParams* params,
                              int variant,
                              void* stream);

/* Query the recommended kernel variant for the current device.
 * Returns a BH_KernelVariant value. */
int bh_select_kernel_variant(void);

/* Upload LUT CUDA texture object handles to __constant__ memory.
 * emissivity, redshift, spectral: cudaTextureObject_t values cast to
 * unsigned long long (use 0 for unregistered slots).
 * Called by the backend after bh_cuda_register_lut and before each frame. */
void bh_upload_lut_textures(unsigned long long emissivity,
                             unsigned long long redshift,
                             unsigned long long spectral);

#ifdef __cplusplus
}
#endif

#endif /* BLACKHOLE_CUDA_KERNEL_LAUNCH_H */
