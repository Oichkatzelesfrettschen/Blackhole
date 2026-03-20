/*
 * kernels_fp16.cu
 * FP16 storage / FP32 compute geodesic tracing kernel.
 *
 * Following YSU-engine kernels_fp16_soa.cu pattern:
 * - Load ray state as __half, promote to float for metric computation
 * - Demote accumulation results back to __half for intermediate storage
 * - Benefit: reduced register pressure, potential for FP16 texture fetches
 *
 * Core Kerr metric math stays FP32 for precision.
 */

#include <cuda_fp16.h>
#include <driver_types.h>     /* cudaStream_t */
#include <math.h>             // NOLINT(modernize-deprecated-headers) -- CUDA device code
#include <vector_functions.h> /* make_float3 */
#include <vector_types.h>     /* float3, float4, dim3 */

#include "device_physics.cuh"

/* ========================================================================
 * FP16 storage helpers (internal linkage via anonymous namespace)
 * ======================================================================== */

namespace {

/* phi and t are kept in FP32: phi can grow by ~1e5 radians/step near the
 * Kerr horizon (delta -> 0, delta_safe = 1e-6), far exceeding FP16 max 65504.
 * Only r, theta, and sign fields (bounded, slow-varying) use FP16. */
struct HalfRayState {
  __half r;
  __half theta;
  float phi; /* FP32: avoids Inf -> sincosf NaN near horizon */
  float t;   /* FP32: avoids Inf -> sincosf NaN near horizon */
  __half signR;
  __half signTheta;
};

__device__ __forceinline__ HalfRayState kerrRayToHalf(const KerrRay &kr) {
  HalfRayState h{};
  h.r = __float2half(kr.r);
  h.theta = __float2half(kr.theta);
  h.phi = kr.phi; /* keep FP32 */
  h.t = kr.t;     /* keep FP32 */
  h.signR = __float2half(kr.sign_r);
  h.signTheta = __float2half(kr.sign_theta);
  return h;
}

__device__ __forceinline__ KerrRay halfToKerrRay(const HalfRayState &h) {
  KerrRay kr{};
  kr.r = __half2float(h.r);
  kr.theta = __half2float(h.theta);
  kr.phi = h.phi; /* keep FP32 */
  kr.t = h.t;     /* keep FP32 */
  kr.sign_r = __half2float(h.signR);
  kr.sign_theta = __half2float(h.signTheta);
  return kr;
}

} // namespace

/* ========================================================================
 * FP16 Storage Kernel
 *
 * Trace geodesic with FP16 intermediate storage of ray state.
 * All Kerr metric arithmetic is FP32; only the ray state between
 * integration steps is stored in FP16 to reduce register pressure.
 * ======================================================================== */

__launch_bounds__(256, 4)
    // NOLINTNEXTLINE(misc-use-internal-linkage) -- __global__ cannot be static or in anonymous
    // namespace
    __global__ void geodesicTraceFp16Storage(float4 *__restrict__ dFramebuffer) {
  int const px = static_cast<int>((blockIdx.x * blockDim.x) + threadIdx.x);
  int const py = static_cast<int>((blockIdx.y * blockDim.y) + threadIdx.y);
  if (px >= d_width || py >= d_height) {
    return;
  }

  float3 const cam = make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]);
  float3 const dir = d_ray_dir(px, py);

  float const rs = d_rs;
  float const a = 0.5f * d_spin * rs;
  float const dt = d_step_size;
  int const maxSteps = d_max_steps;
  float const maxDist = d_max_dist;

  HitResult result{};
  result.hit_disk = false;
  result.hit_horizon = false;
  result.escaped = false;
  result.hit_point = make_f3(0.0f, 0.0f, 0.0f);
  result.phi = 0.0f;
  result.redshift = 1.0f;
  result.min_radius = d_length(cam);

  if ((d_kerr_enabled != 0) && fabsf(a) > D_EPSILON) {
    float rHorizon = d_kerr_outer_horizon(rs, a);
    if (rHorizon <= D_EPSILON) {
      rHorizon = rs;
    }
    float const rDiskIn = d_isco;
    float const rDiskOut = 100.0f * rs;

    KerrConsts const c = d_kerr_init_consts(cam, dir);
    KerrRay kr = d_kerr_init_ray(cam, dir);

    /* Store initial state in FP16 */
    HalfRayState hs = kerrRayToHalf(kr);

    for (int step = 0; step < maxSteps; ++step) {
      /* Promote to FP32 for computation */
      kr = halfToKerrRay(hs);

      float3 const oldPos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
      result.min_radius = fminf(result.min_radius, kr.r);

      if (kr.r <= rHorizon) {
        result.hit_horizon = true;
        result.hit_point = oldPos;
        goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
      }

      /* Kerr step in full FP32 precision */
      d_kerr_step(kr, rs, a, c, dt);

      /* Demote back to FP16 for storage */
      hs = kerrRayToHalf(kr);

      {
        float3 const newPos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);

        if (d_adisk_enabled != 0) {
          float3 diskHit;
          if (d_check_disk(oldPos, newPos, rDiskIn, rDiskOut, diskHit)) {
            result.hit_disk = true;
            result.hit_point = diskHit;
            result.phi = atan2f(diskHit.y, diskHit.x);
            result.redshift = d_redshift_factor(d_length(diskHit), rs);
            goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
          }
        }

        if (kr.r > maxDist) {
          result.escaped = true;
          result.hit_point = newPos;
          goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
        }
      }
    }
    result.escaped = true;
    kr = halfToKerrRay(hs);
    result.hit_point = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
  } else {
    /* Schwarzschild path */
    float3 pos = cam;
    float3 vel = dir;
    float const rDiskIn = d_isco;
    float const rDiskOut = 100.0f * rs;

    for (int step = 0; step < maxSteps; ++step) {
      float3 const oldPos = pos;
      d_step_rk4(pos, vel, rs, dt);

      float const r = d_length(pos);
      result.min_radius = fminf(result.min_radius, r);

      if (r <= rs) {
        result.hit_horizon = true;
        result.hit_point = pos;
        goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
      }

      if (d_adisk_enabled != 0) {
        float3 diskHit;
        if (d_check_disk(oldPos, pos, rDiskIn, rDiskOut, diskHit)) {
          result.hit_disk = true;
          result.hit_point = diskHit;
          result.phi = atan2f(diskHit.y, diskHit.x);
          result.redshift = d_redshift_factor(d_length(diskHit), rs);
          goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
        }
      }

      if (r > maxDist) {
        result.escaped = true;
        result.hit_point = pos;
        goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
      }
    }
    result.escaped = true;
    result.hit_point = pos;
  }

shade:
  dFramebuffer[(py * d_width) + px] = d_shade_hit(result, cam);
}

/* Host wrapper */
extern "C" void launchFp16Storage(float4 *dFramebuffer, int width, int height,
                                  cudaStream_t stream) {
  dim3 const block(16, 16);
  dim3 const grid(static_cast<unsigned int>((width + 15) / 16),
                  static_cast<unsigned int>((height + 15) / 16));
  geodesicTraceFp16Storage<<<grid, block, 0, stream>>>(dFramebuffer);
}
