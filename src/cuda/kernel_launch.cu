/**
 * @file kernel_launch.cu
 * @brief Host dispatch: copies LaunchParams to __constant__ memory and launches
 *        the selected kernel variant.
 */

#include <cstdio>

#include <cuda_runtime.h>
#include <cuda_runtime_api.h>
#include <driver_types.h>
#include <vector_types.h>

#include "kernel_launch.h"
#include "kernel_registry.h"

#include "device_physics.cuh"

/**
 * @brief __constant__ memory definitions for all per-frame physics parameters.
 *
 * Declared extern in device_physics.cuh; defined exactly once here.
 * Under separable compilation nvlink enforces single-definition per symbol.
 */
__constant__ float d_rs;
__constant__ float d_spin;
__constant__ float d_isco;
__constant__ float d_step_size;
__constant__ float d_fov_scale;
__constant__ float d_max_dist;
__constant__ float d_cam_pos[3];
__constant__ float d_cam_basis[9];
__constant__ float d_frame_shift_x;
__constant__ float d_frame_shift_y;
__constant__ int d_max_steps;
__constant__ int d_width;
__constant__ int d_height;
__constant__ int d_adisk_enabled;
__constant__ int d_redshift_enabled;
__constant__ int d_kerr_enabled;
__constant__ int d_use_luts;
__constant__ float d_lut_radius_min;
__constant__ float d_lut_radius_max;
__constant__ float d_redshift_radius_min;
__constant__ float d_redshift_radius_max;
__constant__ float d_spectral_radius_min;
__constant__ float d_spectral_radius_max;
__constant__ float d_time_sec;
/* LUT texture objects (cudaTextureObject_t = unsigned long long, 0 = not registered).
 * All six BhLutSlot entries are mirrored here so bh_upload_lut_textures() can push
 * any combination of registered textures to the device in a single call. */
__constant__ unsigned long long d_tex_emissivity; /**< @brief Accretion disk emissivity LUT. */
__constant__ unsigned long long d_tex_redshift;   /**< @brief Gravitational redshift LUT. */
__constant__ unsigned long long d_tex_spectral;   /**< @brief Spectral modulation LUT. */
__constant__ unsigned long long d_tex_grb;        /**< @brief Gamma-ray burst overlay LUT. */
__constant__ unsigned long long d_tex_galaxy;     /**< @brief Galaxy cubemap background. */
__constant__ unsigned long long d_tex_grmhd;       /**< @brief GRMHD left frame (RGBA32F 3D). */
__constant__ unsigned long long d_tex_synch_g;     /**< @brief Synchrotron G(x)=x*K_{2/3}(x) LUT (R32F 2D, height=1). */
__constant__ unsigned long long d_tex_grmhd_right; /**< @brief GRMHD right frame for time interpolation (RGBA32F 3D). */
__constant__ unsigned long long d_tex_background_equirect; /**< @brief Optional bridge 2D equirectangular background. */
__constant__ float d_grmhd_alpha;                  /**< @brief Blend [0,1] between left and right GRMHD frames (C1d). */
__constant__ float d_doppler_strength;
__constant__ float d_background_intensity;
__constant__ int d_background_enabled;
__constant__ float d_photon_glow_strength;
__constant__ int d_debug_pre_redshift_background;
__constant__ int d_debug_pre_shaping_background;
__constant__ float d_background_yaw_rad;
__constant__ float d_background_pitch_rad;
__constant__ float d_background_filter_radius;
__constant__ float d_background_layer_params[12];
__constant__ float d_background_layer_lod_bias[3];
__constant__ int   d_wiregrid_enabled;     /**< @brief BL-coord wiregrid overlay flag. */
__constant__ float d_wiregrid_show_ergo;   /**< @brief Show ergosphere boundary+glow. */
__constant__ float d_wiregrid_grid_scale;  /**< @brief Grid density multiplier. */
__constant__ float d_wiregrid_motion_scale; /**< @brief Frame-dragging azimuth advection strength. */
__constant__ float d_wiregrid_infall_scale; /**< @brief Inward radial-shell advection strength. */
__constant__ float d_wiregrid_strength;     /**< @brief Post-attenuation alpha multiplier. */
__constant__ float d_wiregrid_scene_preserve; /**< @brief 1 = yield to scene luminance. */
__constant__ float d_wiregrid_color[4];     /**< @brief Base RGBA for the coordinate grid overlay. */
__constant__ float d_grmhd_r_min;          /**< @brief Inner radial bound of GRMHD grid. */
__constant__ float d_grmhd_r_max;          /**< @brief Outer radial bound of GRMHD grid. */
__constant__ int   d_rte_enabled;          /**< @brief 1 = volumetric RTE path (D3). */
__constant__ float d_rte_opacity_scale;    /**< @brief alpha_nu = rte_opacity_scale * j_nu. */
__constant__ int   d_stokes_enabled;       /**< @brief 1 = polarized Stokes IQUV transport (D4). */
__constant__ float d_stokes_b_angle;       /**< @brief EVPA of projected B field on sky [rad] (D4). */
__constant__ float d_stokes_ne_scale;      /**< @brief Faraday rotation strength multiplier (D4). */
__constant__ float d_adisk_lit;            /**< @brief Disk luminosity scale (1.0 = GLSL flux*2 level). */

/* External launch wrappers from each kernel file */
extern "C" void launchFp32Baseline(float4 *fb, int w, int h, cudaStream_t s);
extern "C" void launchFp32Coarsened(float4 *fb, int w, int h, cudaStream_t s);
extern "C" void launchFp16Storage(float4 *fb, int w, int h, cudaStream_t s);
extern "C" void launchFp16H2Ilp(float4 *fb, int w, int h, cudaStream_t s);

namespace {

/* NOLINT(cppcoreguidelines-macro-usage) -- standard CUDA symbol-upload pattern */
#define COPY_CONST(sym, val)                                                                       \
  do { /* NOLINT(cppcoreguidelines-avoid-do-while) */                                              \
    auto const _v = (val);                                                                         \
    cudaError_t const _err = cudaMemcpyToSymbol(sym, &_v, sizeof(_v));                             \
    if (_err != cudaSuccess) {                                                                     \
      (void)fprintf(stderr, "cudaMemcpyToSymbol(%s) failed: %s\n", #sym,                           \
                    cudaGetErrorString(_err)); /* NOLINT(cert-err33-c) */                          \
      return -1;                                                                                   \
    }                                                                                              \
  } while (0) /* NOLINT(cppcoreguidelines-avoid-do-while) */

/**
 * @brief Upload all fields of BH_LaunchParams to __constant__ memory.
 *
 * Each field is uploaded as a separate scalar via cudaMemcpyToSymbol to avoid
 * struct-layout ABI mismatch between host C++23 and device C++17.
 * Each COPY_CONST call costs approximately 1 us on a typical system.
 *
 * @param p Pointer to the launch parameters to upload.
 * @return 0 on success, -1 if any cudaMemcpyToSymbol call fails.
 */
// NOLINT(readability-function-cognitive-complexity) -- 23 scalar uploads, each identical
int uploadConstants(
    const struct BH_LaunchParams *p) { // NOLINT(readability-function-cognitive-complexity)
  COPY_CONST(d_rs, p->rs);
  COPY_CONST(d_spin, p->spin);
  COPY_CONST(d_isco, p->isco);
  COPY_CONST(d_step_size, p->step_size);
  COPY_CONST(d_fov_scale, p->fov_scale);
  COPY_CONST(d_max_dist, p->max_dist);
  COPY_CONST(d_frame_shift_x, p->frame_shift_x);
  COPY_CONST(d_frame_shift_y, p->frame_shift_y);
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
  COPY_CONST(d_photon_glow_strength, p->photon_glow_strength);
  COPY_CONST(d_debug_pre_redshift_background, p->debug_pre_redshift_background);
  COPY_CONST(d_debug_pre_shaping_background, p->debug_pre_shaping_background);
  COPY_CONST(d_background_yaw_rad, p->background_yaw_rad);
  COPY_CONST(d_background_pitch_rad, p->background_pitch_rad);
  COPY_CONST(d_background_filter_radius, p->background_filter_radius);
  COPY_CONST(d_wiregrid_enabled, p->wiregrid_enabled);
  COPY_CONST(d_wiregrid_show_ergo, p->wiregrid_show_ergo);
  COPY_CONST(d_wiregrid_grid_scale, p->wiregrid_grid_scale);
  COPY_CONST(d_wiregrid_motion_scale, p->wiregrid_motion_scale);
  COPY_CONST(d_wiregrid_infall_scale, p->wiregrid_infall_scale);
  COPY_CONST(d_wiregrid_strength, p->wiregrid_strength);
  COPY_CONST(d_wiregrid_scene_preserve, p->wiregrid_scene_preserve);
  {
    cudaError_t const _err =
        cudaMemcpyToSymbol(d_wiregrid_color, p->wiregrid_color, sizeof(p->wiregrid_color));
    if (_err != cudaSuccess) {
      (void)fprintf(stderr, "cudaMemcpyToSymbol(%s) failed: %s\n", "d_wiregrid_color",
                    cudaGetErrorString(_err));
      return -1;
    }
  }
  COPY_CONST(d_grmhd_r_min, p->grmhd_r_min);
  COPY_CONST(d_grmhd_r_max, p->grmhd_r_max);
  COPY_CONST(d_rte_enabled, p->rte_enabled);
  COPY_CONST(d_rte_opacity_scale, p->rte_opacity_scale);
  COPY_CONST(d_grmhd_alpha, p->grmhd_alpha);
  COPY_CONST(d_stokes_enabled, p->stokes_enabled);
  COPY_CONST(d_stokes_b_angle, p->stokes_b_field_angle);
  COPY_CONST(d_stokes_ne_scale, p->stokes_ne_scale);
  COPY_CONST(d_adisk_lit, p->adisk_lit);

  /* Array copies */
  cudaError_t const errPos = cudaMemcpyToSymbol(d_cam_pos, p->cam_pos, sizeof(p->cam_pos));
  if (errPos != cudaSuccess) {
    return -1;
  }
  cudaError_t const errBasis = cudaMemcpyToSymbol(d_cam_basis, p->cam_basis, sizeof(p->cam_basis));
  if (errBasis != cudaSuccess) {
    return -1;
  }
  cudaError_t const errLayerParams =
      cudaMemcpyToSymbol(d_background_layer_params, p->background_layer_params,
                         sizeof(p->background_layer_params));
  if (errLayerParams != cudaSuccess) {
    return -1;
  }
  cudaError_t const errLayerLod =
      cudaMemcpyToSymbol(d_background_layer_lod_bias, p->background_layer_lod_bias,
                         sizeof(p->background_layer_lod_bias));
  if (errLayerLod != cudaSuccess) {
    return -1;
  }

#undef COPY_CONST
  return 0;
}

} // namespace

extern "C" int bh_launch_geodesic_kernel(void *framebuffer, const struct BH_LaunchParams *params,
                                         int variant, void *stream) {
  if ((framebuffer == nullptr) || (params == nullptr)) {
    return -1;
  }

  /* Auto-select if variant is negative */
  if (variant < 0) {
    variant = registry_select_variant();
  }
  if (variant < 0 || variant >= BH_KERNEL_COUNT) {
    variant = BH_KERNEL_FP32_BASELINE;
  }

  /* Upload parameters to constant memory */
  if (uploadConstants(params) != 0) {
    return -1;
  }

  auto *fb = static_cast<float4 *>(framebuffer);
  auto *s = static_cast<cudaStream_t>(stream);
  int const w = params->width;
  int const h = params->height;

  switch (variant) {
  case BH_KERNEL_FP32_BASELINE:
    launchFp32Baseline(fb, w, h, s);
    break;
  case BH_KERNEL_FP32_COARSENED:
    launchFp32Coarsened(fb, w, h, s);
    break;
  case BH_KERNEL_FP16_STORAGE:
    launchFp16Storage(fb, w, h, s);
    break;
  case BH_KERNEL_FP16_H2_ILP:
    launchFp16H2Ilp(fb, w, h, s);
    break;
  default:
    launchFp32Baseline(fb, w, h, s);
    break;
  }

  cudaError_t const err = cudaGetLastError();
  if (err != cudaSuccess) {
    (void)fprintf(stderr, "Kernel launch failed: %s\n", cudaGetErrorString(err));
    return -1;
  }

  return 0;
}

extern "C" int bh_select_kernel_variant(void) {
  return registry_select_variant();
}

/**
 * @brief Upload all seven LUT texture object handles to __constant__ memory.
 *
 * Called by cuda_backend.cu::sync_lut_constants() after any lut_register() call
 * and at the start of every frame render so that device kernels see up-to-date
 * handles.  A value of 0 means the slot is not yet registered; device code
 * guards on zero before sampling.
 *
 * cudaMemcpyToSymbol errors are non-fatal: a failed upload leaves the old
 * constant value in place and the kernel simply falls back to analytic paths.
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
extern "C" void bh_upload_lut_textures(unsigned long long emissivity,
                                       unsigned long long redshift,
                                       unsigned long long spectral,
                                       unsigned long long grb,
                                       unsigned long long galaxy,
                                       unsigned long long grmhd,
                                       unsigned long long synch_g,
                                       unsigned long long grmhd_right) {
  (void)cudaMemcpyToSymbol(d_tex_emissivity,   &emissivity,   sizeof(emissivity));
  (void)cudaMemcpyToSymbol(d_tex_redshift,     &redshift,     sizeof(redshift));
  (void)cudaMemcpyToSymbol(d_tex_spectral,     &spectral,     sizeof(spectral));
  (void)cudaMemcpyToSymbol(d_tex_grb,          &grb,          sizeof(grb));
  (void)cudaMemcpyToSymbol(d_tex_galaxy,       &galaxy,       sizeof(galaxy));
  (void)cudaMemcpyToSymbol(d_tex_grmhd,        &grmhd,        sizeof(grmhd));
  (void)cudaMemcpyToSymbol(d_tex_synch_g,      &synch_g,      sizeof(synch_g));
  (void)cudaMemcpyToSymbol(d_tex_grmhd_right,  &grmhd_right,  sizeof(grmhd_right));
}

extern "C" void bh_upload_bridge_background_texture(unsigned long long background_equirect) {
  (void)cudaMemcpyToSymbol(d_tex_background_equirect, &background_equirect,
                           sizeof(background_equirect));
}
