/**
 * @file kernels_fp16.cu
 * @brief FP16 storage / FP32 compute geodesic tracing kernel.
 *
 * Following the YSU-engine kernels_fp16_soa.cu pattern:
 * - Ray state (r, theta, sign fields) stored as __half between steps to reduce
 *   register pressure; phi and t remain FP32 to avoid overflow near the horizon.
 * - All Kerr metric arithmetic is promoted to FP32 before each step.
 * - Requires SM8.0+ (Ampere) for native FP16 storage throughput.
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

/**
 * @brief Compact ray state with FP16-compressed bounded fields.
 *
 * phi and t are kept in FP32 because phi can grow by ~1e5 rad/step near the
 * Kerr horizon (delta -> 0, delta_safe = 1e-6), exceeding FP16 max 65504.
 * The Mino velocities and accelerations stay FP32 as well: vr scales as r^2
 * and passes through zero at turning points, where FP16 would lose the sign
 * of small values. Only r and theta (bounded and slow-varying) use FP16.
 */
struct HalfRayState {
  __half r;          /**< @brief Radial coordinate stored as FP16. */
  __half theta;      /**< @brief Polar angle stored as FP16. */
  float phi;         /**< @brief Azimuthal angle kept FP32 to avoid Inf near horizon. */
  float t;           /**< @brief Coordinate time kept FP32 to avoid Inf near horizon. */
  float vr;          /**< @brief dr/dlambda (FP32). */
  float mu;          /**< @brief cos(theta), the polar state variable (FP32). */
  float vmu;         /**< @brief dmu/dlambda (FP32). */
  float accR;        /**< @brief R'(r)/2 carried between leapfrog steps (FP32). */
  float accMu;       /**< @brief Theta_mu'(mu)/2 carried between leapfrog steps (FP32). */
};

/**
 * @brief Compress a full-precision KerrRay into a HalfRayState.
 *
 * @param kr Source FP32 ray state.
 * @return Compressed HalfRayState with r and theta in FP16.
 */
__device__ __forceinline__ HalfRayState kerrRayToHalf(const KerrRay &kr) {
  HalfRayState h{};
  h.r = __float2half(kr.r);
  h.theta = __float2half(kr.theta);
  h.phi = kr.phi; /* keep FP32 */
  h.t = kr.t;     /* keep FP32 */
  h.vr = kr.vr;
  h.mu = kr.mu;
  h.vmu = kr.vmu;
  h.accR = kr.acc_r;
  h.accMu = kr.acc_mu;
  return h;
}

/**
 * @brief Promote a HalfRayState back to a full-precision KerrRay for computation.
 *
 * @param h Compressed FP16 ray state.
 * @return Full FP32 KerrRay suitable for metric integration.
 */
__device__ __forceinline__ KerrRay halfToKerrRay(const HalfRayState &h) {
  KerrRay kr{};
  kr.r = __half2float(h.r);
  kr.theta = __half2float(h.theta);
  kr.phi = h.phi; /* keep FP32 */
  kr.t = h.t;     /* keep FP32 */
  kr.vr = h.vr;
  kr.mu = h.mu;
  kr.vmu = h.vmu;
  kr.acc_r = h.accR;
  kr.acc_mu = h.accMu;
  return kr;
}

} // namespace

/* ========================================================================
 * FP16 Storage Kernel
 * ======================================================================== */

/**
 * @brief FP16 storage / FP32 compute geodesic tracing kernel (1 ray per thread).
 *
 * Traces a Kerr or Schwarzschild geodesic. Ray state is stored in HalfRayState
 * (FP16 for r, theta, sign fields) between integration steps to reduce register
 * pressure. All Kerr metric arithmetic is promoted to FP32 before each step.
 *
 * @param dFramebuffer Device pointer to float4[d_width * d_height]; output RGBA pixels.
 */
__launch_bounds__(256, 4)
    // NOLINTNEXTLINE(misc-use-internal-linkage) -- __global__ cannot be static or in anonymous
    // namespace
    __global__ void geodesicTraceFp16Storage(float4 *__restrict__ dFramebuffer) {
  int const px = static_cast<int>((blockIdx.x * blockDim.x) + threadIdx.x);
  int const py = static_cast<int>((blockIdx.y * blockDim.y) + threadIdx.y);
  if (px >= d_width || py >= d_height) {
    return;
  }

  /* Physics frame (spin along +z); see d_world_to_physics. */
  float3 const cam = d_world_to_physics(make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]));
  float3 const dir = d_world_to_physics(d_ray_dir(px, py));

  float const rs = d_rs;
  float const a = 0.5f * d_spin * rs;
  float const dt = d_step_size;
  int const maxSteps = d_max_steps;
  /* Escape only outside both the scene radius and the camera's own radius while
   * moving outward (bhEscapeRadius in interop_trace.glsl). */
  float const maxDist = fmaxf(d_max_dist, 1.01f * d_length(cam));

  HitResult result{};
  result.hit_disk = false;
  result.hit_horizon = false;
  result.escaped = false;
  result.max_steps = false;
  result.hit_point = make_f3(0.0f, 0.0f, 0.0f);
  result.closest_approach_point = cam;
  result.phi = 0.0f;
  result.redshift = 1.0f;
  result.min_radius = d_length(cam);
  result.closest_approach_update_count = 0;
  result.first_closest_approach_step = -1;
  result.last_closest_approach_step = -1;

  if (d_kerr_enabled != 0) {
    float rHorizon = d_kerr_outer_horizon(rs, a);
    if (rHorizon <= D_EPSILON) {
      rHorizon = rs;
    }
    float const rDiskIn = d_isco;
    float const rDiskOut = 100.0f * rs;

    float const aTrace = d_kerr_trace_spin(a);
    KerrConsts c;
    KerrRay kr;
    d_kerr_init_geodesic(cam, dir, rs, aTrace, c, kr);

    /* Store initial state in FP16 */
    HalfRayState hs = kerrRayToHalf(kr);

    for (int step = 0; step < maxSteps; ++step) {
      /* Promote to FP32 for computation */
      kr = halfToKerrRay(hs);

      float3 const oldPos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
      d_record_closest_approach(result, kr.r, oldPos, step);

      if (kr.r <= rHorizon) {
        result.hit_horizon = true;
        result.hit_point = oldPos;
        goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
      }

      /* Kerr step in full FP32 precision */
      d_kerr_step(kr, rs, aTrace, c, dt);

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

        if (kr.r > maxDist && kr.vr > 0.0f) {
          result.escaped = true;
          result.hit_point = newPos;
          goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
        }
      }
    }
    result.escaped = true;
    result.max_steps = true;
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
      d_record_closest_approach(result, r, pos, step);

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

      if (r > maxDist && d_dot(pos, vel) > 0.0f) {
        result.escaped = true;
        result.hit_point = pos;
        goto shade; // NOLINT(cppcoreguidelines-avoid-goto) -- early-exit from CUDA kernel loop
      }
    }
    result.escaped = true;
    result.max_steps = true;
    result.hit_point = pos;
  }

shade:;
  float4 color16 = d_shade_hit(result, cam);
  if (d_wiregrid_enabled != 0) {
    float3 const hp = result.hit_point;
    float const r_bl = sqrtf(hp.x*hp.x + hp.y*hp.y + hp.z*hp.z);
    if (r_bl > 1e-5f) {
      float const theta_bl = acosf(fmaxf(-1.0f, fminf(hp.z / r_bl, 1.0f)));
      float const phi_bl   = atan2f(hp.y, hp.x);
      float4 const wg = d_wiregrid_overlay(r_bl, theta_bl, phi_bl,
                                            d_spin, d_wiregrid_show_ergo != 0.0f,
                                            d_wiregrid_grid_scale);
      float const alpha = d_wg_overlay_blend_alpha(wg, make_f3(color16.x, color16.y, color16.z));
      float const inv_a = 1.0f - alpha;
      color16 = make_float4(color16.x*inv_a + wg.x*alpha,
                             color16.y*inv_a + wg.y*alpha,
                             color16.z*inv_a + wg.z*alpha, color16.w);
    }
  }
  dFramebuffer[(py * d_width) + px] = color16;
}

/**
 * @brief Launch the FP16 storage kernel (1 ray/thread, 16x16 blocks).
 *
 * @param dFramebuffer Device framebuffer pointer (float4[width*height]).
 * @param width        Framebuffer width in pixels.
 * @param height       Framebuffer height in pixels.
 * @param stream       CUDA stream to launch on.
 */
extern "C" void launchFp16Storage(float4 *dFramebuffer, int width, int height,
                                  cudaStream_t stream) {
  dim3 const block(16, 16);
  dim3 const grid(static_cast<unsigned int>((width + 15) / 16),
                  static_cast<unsigned int>((height + 15) / 16));
  geodesicTraceFp16Storage<<<grid, block, 0, stream>>>(dFramebuffer);
}
