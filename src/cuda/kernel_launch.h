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
    float frame_shift_x; /**< @brief Image-plane horizontal shift in local camera space. */
    float frame_shift_y; /**< @brief Image-plane vertical shift in local camera space. */

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
    float photon_glow_strength; /**< @brief Photon-ring glow multiplier for escaped rays. */
    int debug_pre_redshift_background; /**< @brief 1 = export escaped background before redshift and near-hole shaping. */
    int debug_pre_shaping_background; /**< @brief 1 = export escaped background after redshift but before near-hole shaping. */
    int debug_post_shaping_background; /**< @brief 1 = export escaped background after near-hole shaping but before photon-ring glow. */
    int debug_shaper_inputs; /**< @brief 1 = export packed shaper inputs (minRadius, alignedFlow, nearHoleWeight). */
    int debug_closest_approach_direction; /**< @brief 1 = export encoded normalize(closest_approach_point). */
    int debug_escaped_direction; /**< @brief 1 = export encoded escaped direction. */
    float background_yaw_rad;   /**< @brief Skybox yaw rotation around the spin axis [rad]. */
    float background_pitch_rad; /**< @brief Skybox pitch rotation around the camera-right axis [rad]. */
    float background_filter_radius; /**< @brief Skybox angular prefilter radius in direction-space units. */
    float background_layer_params[12]; /**< @brief Three vec4 layer params: offset_x, offset_y, scale, weight. */
    float background_layer_lod_bias[3]; /**< @brief Three non-negative layer LOD biases. */

    /* Wiregrid BL-coordinate overlay (task A4) */
    int   wiregrid_enabled;    /**< @brief 1 = apply Boyer-Lindquist coordinate overlay. */
    float wiregrid_show_ergo;  /**< @brief 1.0 = render ergosphere boundary + glow. */
    float wiregrid_grid_scale; /**< @brief Grid density multiplier (1.0 = pi/6 spacing). */
    float wiregrid_motion_scale; /**< @brief Frame-dragging azimuth advection strength. */
    float wiregrid_infall_scale; /**< @brief Inward radial-shell advection strength. */
    float wiregrid_strength; /**< @brief Post-attenuation alpha multiplier for the overlay. */
    float wiregrid_scene_preserve; /**< @brief 1 = yield to scene luminance, 0 = diagnostic. */
    float wiregrid_color[4]; /**< @brief Base RGBA for the coordinate grid overlay. */

    /* GRMHD volume bounds (task C1l) */
    float grmhd_r_min; /**< @brief Inner radial bound of GRMHD grid (geometric units). */
    float grmhd_r_max; /**< @brief Outer radial bound of GRMHD grid (geometric units). */

    /* Volumetric RTE (D3) */
    int   rte_enabled;       /**< @brief 1 = use front-to-back volumetric RTE instead of single-scatter. */
    float rte_opacity_scale; /**< @brief alpha_nu = rte_opacity_scale * j_nu; tune in ImGui. */

    /* GRMHD temporal interpolation (C1d) */
    float grmhd_alpha; /**< @brief Blend [0,1] between left (slot 5) and right (slot 7) GRMHD frames. */

    /* Polarized Stokes IQUV transport (D4) */
    int   stokes_enabled;     /**< @brief 1 = track Stokes Q,U,V alongside intensity (D4). */
    float stokes_b_field_angle; /**< @brief EVPA of projected B field on sky [rad] (D4). */
    float stokes_ne_scale;    /**< @brief Faraday rotation strength multiplier (0=no Faraday) (D4). */

    /* Disk brightness (matches GLSL adiskLit uniform).
     * WHY: GLSL interop_trace.glsl uses flux*2.0 as base; adisk_lit multiplies that.
     * 1.0 = GLSL default brightness (flux*2.0). 0.35 = cinematic record setting. */
    float adisk_lit;
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
 * @brief Upload all seven LUT CUDA texture object handles to __constant__ memory.
 *
 * Must be called after bhCudaRegisterLut() and before each frame render so
 * device kernels see up-to-date texture object handles.  Pass 0 for any slot
 * that has not been registered; device code checks for zero before sampling.
 *
 * @param emissivity  cudaTextureObject_t for slot 0 (accretion emissivity LUT).
 * @param redshift    cudaTextureObject_t for slot 1 (gravitational redshift LUT).
 * @param spectral    cudaTextureObject_t for slot 2 (spectral modulation LUT).
 * @param grb         cudaTextureObject_t for slot 3 (GRB overlay LUT).
 * @param galaxy      cudaTextureObject_t for slot 4 (galaxy cubemap background).
 * @param grmhd       cudaTextureObject_t for slot 5 (GRMHD left frame).
 * @param synch_g     cudaTextureObject_t for slot 6 (synchrotron G(x)=x*K_{2/3}(x) LUT).
 * @param grmhd_right cudaTextureObject_t for slot 7 (GRMHD right frame; 0 = no interpolation).
 */
void bh_upload_lut_textures(unsigned long long emissivity,
                             unsigned long long redshift,
                             unsigned long long spectral,
                             unsigned long long grb,
                             unsigned long long galaxy,
                             unsigned long long grmhd,
                             unsigned long long synch_g,
                             unsigned long long grmhd_right);

/**
 * @brief Upload the optional equirectangular bridge background texture handle.
 *
 * @param background_equirect cudaTextureObject_t for a 2D equirectangular background.
 */
void bh_upload_bridge_background_texture(unsigned long long background_equirect);

#ifdef __cplusplus
}
#endif

// NOLINTEND(readability-identifier-naming,cppcoreguidelines-use-enum-class,modernize-redundant-void-arg)

#endif /* BLACKHOLE_CUDA_KERNEL_LAUNCH_H */
