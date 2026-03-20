/**
 * @file kernel_launch.h
 * @brief POD-only C-compatible interface between C++23 host code and C++17 CUDA code.
 *
 * FIREWALL: This header must compile with a plain C compiler.
 * NO std:: types, NO glm::, NO templates, NO C++ containers.
 * Only plain C structs, fixed-size arrays, and function declarations.
 */

#ifndef BLACKHOLE_CUDA_KERNEL_LAUNCH_H
#define BLACKHOLE_CUDA_KERNEL_LAUNCH_H

/* NOLINTBEGIN(readability-identifier-naming,cppcoreguidelines-use-enum-class,modernize-redundant-void-arg)
 * WHY: This is a C-compatible POD firewall header. All naming follows C
 * conventions intentionally (BH_ prefix, snake_case members, plain enum).
 * nvcc C++17 cannot see C++23 STL; no std:: types, no enum class, no (). */

#ifdef __cplusplus
extern "C" {
#endif

/**
 * @brief All parameters needed by the geodesic tracing kernel.
 *
 * Filled by main.cpp from its C++23 InteropUniforms / glm types and passed
 * to bh_launch_geodesic_kernel(), which copies each field into __constant__ memory.
 */
struct BH_LaunchParams {
    /* Black hole parameters */
    float rs;           /**< @brief Schwarzschild radius (geometric units). */
    float spin;         /**< @brief Kerr spin parameter a/M (dimensionless, 0..1). */
    float isco;         /**< @brief ISCO radius. */
    float step_size;    /**< @brief Integration step size (affine parameter increment). */
    float fov_scale;    /**< @brief Field of view scale factor. */
    float max_dist;     /**< @brief Maximum ray travel distance before declaring escape. */

    /* Camera */
    float cam_pos[3];   /**< @brief Camera position (x, y, z) in world space. */
    float cam_basis[9]; /**< @brief Camera basis matrix (3x3, column-major, matching glm). */

    /* Integration */
    int max_steps;      /**< @brief Maximum integration steps per ray. */
    int width;          /**< @brief Framebuffer width in pixels. */
    int height;         /**< @brief Framebuffer height in pixels. */

    /* Feature flags (int for C compat, 0=off, 1=on) */
    int adisk_enabled;      /**< @brief Enable accretion disk intersection. */
    int redshift_enabled;   /**< @brief Enable gravitational redshift dimming. */
    int kerr_enabled;       /**< @brief Use Kerr (vs Schwarzschild) metric. */
    int use_luts;           /**< @brief Sample physics LUT textures when available. */

    /* LUT domain bounds */
    float lut_radius_min;       /**< @brief Minimum normalized radius for emissivity LUT. */
    float lut_radius_max;       /**< @brief Maximum normalized radius for emissivity LUT. */
    float redshift_radius_min;  /**< @brief Minimum normalized radius for redshift LUT. */
    float redshift_radius_max;  /**< @brief Maximum normalized radius for redshift LUT. */
    float spectral_radius_min;  /**< @brief Minimum normalized radius for spectral LUT. */
    float spectral_radius_max;  /**< @brief Maximum normalized radius for spectral LUT. */

    /* Time */
    float time_sec;             /**< @brief Elapsed simulation time in seconds. */

    /* Doppler / beaming */
    float doppler_strength;     /**< @brief Doppler beaming strength multiplier (0=off). */

    /* Background */
    float background_intensity; /**< @brief Background sky intensity scale. */
    int background_enabled;     /**< @brief Enable procedural star-field background. */

    /* Wiregrid BL-coordinate overlay (task A4) */
    int   wiregrid_enabled;    /**< @brief 1 = apply Boyer-Lindquist coordinate overlay. */
    float wiregrid_show_ergo;  /**< @brief 1.0 = render ergosphere boundary + glow. */
    float wiregrid_grid_scale; /**< @brief Grid density multiplier (1.0 = pi/6 spacing). */

    /* GRMHD volume bounds (task C1l) */
    float grmhd_r_min; /**< @brief Inner radial bound of GRMHD grid (geometric units). */
    float grmhd_r_max; /**< @brief Outer radial bound of GRMHD grid (geometric units). */
};

/**
 * @brief Kernel variant selection.
 *
 * Variants are ordered from least to most capable. The registry auto-selects
 * the highest variant supported by the current device's SM version and
 * register budget.
 */
enum BH_KernelVariant {
    BH_KERNEL_FP32_BASELINE  = 0, /**< @brief FP32, 1 ray/thread, SM5.0+. Safe default. */
    BH_KERNEL_FP32_COARSENED = 1, /**< @brief FP32, 2 rays/thread with per-step ILP, SM7.5+. */
    BH_KERNEL_FP16_STORAGE   = 2, /**< @brief FP16 ray state storage, FP32 compute, SM8.0+. */
    BH_KERNEL_FP16_H2_ILP    = 3, /**< @brief __half2 packed 2-ray ILP, Ada/Hopper SM8.9+. */
    BH_KERNEL_COUNT          = 4  /**< @brief Sentinel: number of defined variants. */
};

/**
 * @brief Launch a geodesic tracing kernel into the given linear framebuffer.
 *
 * Copies all fields from @p params into __constant__ memory, then dispatches
 * the selected kernel variant.
 *
 * @param framebuffer Device pointer to float4[width*height] (linear memory).
 * @param params      Launch parameters; copied to __constant__ memory before launch.
 * @param variant     BH_KernelVariant to run; auto-selected when negative.
 * @param stream      CUDA stream handle (cast from cudaStream_t); NULL for default stream.
 * @return 0 on success, non-zero if constant upload or kernel launch fails.
 */
int bh_launch_geodesic_kernel(void* framebuffer,
                              const struct BH_LaunchParams* params,
                              int variant,
                              void* stream);

/**
 * @brief Query the recommended kernel variant for the current CUDA device.
 *
 * Inspects SM version and per-SM register budget to pick the highest variant
 * that achieves at least 2 concurrent blocks per SM.
 *
 * @return BH_KernelVariant value best suited for the active device.
 */
int bh_select_kernel_variant(void);

/**
 * @brief Upload all six LUT CUDA texture object handles to __constant__ memory.
 *
 * Must be called after bhCudaRegisterLut() and before each frame render so
 * device kernels see up-to-date texture object handles.  Pass 0 for any slot
 * that has not been registered; device code checks for zero before sampling.
 *
 * @param emissivity cudaTextureObject_t for slot 0 (accretion emissivity LUT).
 * @param redshift   cudaTextureObject_t for slot 1 (gravitational redshift LUT).
 * @param spectral   cudaTextureObject_t for slot 2 (spectral modulation LUT).
 * @param grb        cudaTextureObject_t for slot 3 (GRB overlay LUT).
 * @param galaxy     cudaTextureObject_t for slot 4 (galaxy cubemap background).
 * @param grmhd      cudaTextureObject_t for slot 5 (GRMHD simulation volume).
 */
void bh_upload_lut_textures(unsigned long long emissivity,
                             unsigned long long redshift,
                             unsigned long long spectral,
                             unsigned long long grb,
                             unsigned long long galaxy,
                             unsigned long long grmhd);

#ifdef __cplusplus
}
#endif

// NOLINTEND(readability-identifier-naming,cppcoreguidelines-use-enum-class,modernize-redundant-void-arg)

#endif /* BLACKHOLE_CUDA_KERNEL_LAUNCH_H */
