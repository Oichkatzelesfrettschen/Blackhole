/*
 * kernel_launch.cu
 * Host dispatch: copies LaunchParams to __constant__ memory and launches
 * the selected kernel variant.
 */

#include <cstdio>

#include <cuda_runtime.h>
#include <cuda_runtime_api.h>
#include <driver_types.h>
#include <vector_types.h>

#include "kernel_launch.h"
#include "kernel_registry.h"

#include "device_physics.cuh"

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
/* LUT texture objects (cudaTextureObject_t = unsigned long long, 0 = not registered) */
__constant__ unsigned long long d_tex_emissivity;
__constant__ unsigned long long d_tex_redshift;
__constant__ unsigned long long d_tex_spectral;
__constant__ float d_doppler_strength;
__constant__ float d_background_intensity;
__constant__ int d_background_enabled;

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

/* Upload LaunchParams to __constant__ memory defined above.
 * WHY: Flat scalar upload avoids struct-layout ABI mismatch between host C++23
 * and device C++17. Each COPY_CONST is one cudaMemcpyToSymbol call (~1 us). */
// NOLINT(readability-function-cognitive-complexity) -- 23 scalar uploads, each identical
int uploadConstants(
    const struct BH_LaunchParams *p) { // NOLINT(readability-function-cognitive-complexity)
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
  cudaError_t const errPos = cudaMemcpyToSymbol(d_cam_pos, p->cam_pos, sizeof(p->cam_pos));
  if (errPos != cudaSuccess) {
    return -1;
  }
  cudaError_t const errBasis = cudaMemcpyToSymbol(d_cam_basis, p->cam_basis, sizeof(p->cam_basis));
  if (errBasis != cudaSuccess) {
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

/* Upload LUT texture object handles to __constant__ memory.
 * Called by cuda_backend.cu after lut_register and before each render frame.
 * emissivity/redshift/spectral are cudaTextureObject_t cast to unsigned long long
 * (0 = not registered; device code checks before sampling). */
extern "C" void bh_upload_lut_textures(unsigned long long emissivity, unsigned long long redshift,
                                       unsigned long long spectral) {
  (void)cudaMemcpyToSymbol(d_tex_emissivity, &emissivity, sizeof(emissivity));
  (void)cudaMemcpyToSymbol(d_tex_redshift, &redshift, sizeof(redshift));
  (void)cudaMemcpyToSymbol(d_tex_spectral, &spectral, sizeof(spectral));
}
