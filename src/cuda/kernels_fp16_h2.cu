/**
 * @file kernels_fp16_h2.cu
 * @brief H2 ILP variant: 2 rays per thread with __half2 packed intermediate storage.
 *
 * Following the YSU-engine kernels_fp16_soa_half2.cu pattern:
 * - Thread k processes pixels (2k, 2k+1) in a linearized grid.
 * - Two independent geodesic chains interleave on Ada dual-issue FP32 pipelines.
 * - __half2 packs both rays' bounded radius r into
 *   one 32-bit register each; min_radius is tracked via __hmin2 (one HMNMX2
 *   SASS instruction per step instead of two fminf calls).
 *   phi and t remain FP32 per ray to avoid overflow near the horizon.
 * - Core Kerr metric FMA stays FP32 for numerical precision.
 * - __half2 promote/demote cost is amortized over max_steps iterations.
 *
 * Register pressure: if spill is detected via
 *   ncu --metrics l1tex__t_sectors_pipe_lsu_mem_local_op_ld
 * reduce max_steps or fall back to FP16_STORAGE. The registry gates this
 * variant at SM8.9+ to ensure Ada dual-issue FP16 pipelines are present.
 * __launch_bounds__(128, 4) limits active blocks to 4/SM for the register budget.
 */

#include <cuda_fp16.h>
#include <driver_types.h>     /* cudaStream_t */
#include <math.h>             // NOLINT(modernize-deprecated-headers) -- CUDA device code
#include <vector_functions.h> /* make_float3 */
#include <vector_types.h>     /* float2, float3, float4, dim3 */

#include "device_physics.cuh"

/* ========================================================================
 * HalfRayPair: packed __half2 intermediate storage for 2-ray threads.
 * ======================================================================== */

namespace {

/**
 * @brief Packed __half2 intermediate storage for a pair of Kerr rays.
 *
 * The bounded radius is stored as an __half2 pair to halve its register
 * cost. The Mino velocity and acceleration, coordinate time, and the angular
 * state (unit direction n and tangent velocity w) stay FP32.
 */
struct HalfRayPair {
  __half2 hR;      /**< @brief (kr0.r, kr1.r) */
  float2 vr;       /**< @brief (kr0.vr, kr1.vr) */
  float2 accR;     /**< @brief (kr0.acc_r, kr1.acc_r) */
  float2 t;        /**< @brief (kr0.t, kr1.t) */
  float3 n0;       /**< @brief Ray 0 unit direction. */
  float3 n1;       /**< @brief Ray 1 unit direction. */
  float3 w0;       /**< @brief Ray 0 tangent angular velocity. */
  float3 w1;       /**< @brief Ray 1 tangent angular velocity. */
};

/**
 * @brief Pack two FP32 KerrRay states into a HalfRayPair.
 *
 * @param a First ray (maps to .x of each __half2 field).
 * @param b Second ray (maps to .y of each __half2 field).
 * @return Packed HalfRayPair.
 */
__device__ __forceinline__ HalfRayPair raysToPair(const KerrRay &a, const KerrRay &b) {
  HalfRayPair h{};
  h.hR = __floats2half2_rn(a.r, b.r);
  h.vr = make_float2(a.vr, b.vr);
  h.accR = make_float2(a.acc_r, b.acc_r);
  h.t = make_float2(a.t, b.t);
  h.n0 = a.n;
  h.n1 = b.n;
  h.w0 = a.w;
  h.w1 = b.w;
  return h;
}

/**
 * @brief Unpack a HalfRayPair into two full-precision KerrRay states.
 *
 * @param h   Packed ray pair.
 * @param[out] a  First ray (unpacked from .x fields).
 * @param[out] b  Second ray (unpacked from .y fields).
 */
__device__ __forceinline__ void pairToRays(const HalfRayPair &h, KerrRay &a, KerrRay &b) {
  float2 const r = __half22float2(h.hR);
  a.r = r.x;
  b.r = r.y;
  a.vr = h.vr.x;
  b.vr = h.vr.y;
  a.acc_r = h.accR.x;
  b.acc_r = h.accR.y;
  a.t = h.t.x;
  b.t = h.t.y;
  a.n = h.n0;
  b.n = h.n1;
  a.w = h.w0;
  b.w = h.w1;
}

} // namespace

/* ========================================================================
 * H2 ILP Kernel: 2 rays/thread, __half2 accumulation
 * ======================================================================== */

/**
 * @brief H2 ILP geodesic tracing kernel (2 rays/thread, __half2 packed storage).
 *
 * Each thread handles linearized pixel pair (2*tid, 2*tid+1). Both geodesic
 * chains advance one integration step per loop iteration with FP32 metric
 * math, enabling the Ada dual-issue scheduler to overlap independent FMA
 * chains. Bounded ray state fields are kept in packed __half2 registers
 * between steps; min_radius is updated via __hmin2.
 * Requires SM8.9+ (Ada/Hopper). __launch_bounds__(128, 4) caps active
 * blocks per SM to respect the elevated register budget.
 *
 * @param dFramebuffer Device pointer to float4[d_width * d_height]; output RGBA pixels.
 */
__launch_bounds__(128, 4)
    // NOLINTNEXTLINE(misc-use-internal-linkage,readability-function-cognitive-complexity)
    __global__ void geodesicTraceFp16H2(float4 *__restrict__ dFramebuffer) {
  /* Linearize thread index, each thread owns 2 adjacent pixels */
  int const tid = static_cast<int>((blockIdx.x * blockDim.x) + threadIdx.x);
  int const totalPixels = d_width * d_height;
  int const idx0 = 2 * tid;
  int const idx1 = idx0 + 1;

  if (idx0 >= totalPixels) {
    return;
  }

  /* Physics frame (spin along +z); see d_world_to_physics. */
  float3 const cam = d_world_to_physics(make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]));
  float const rs = d_rs;
  float const aSpin = 0.5f * d_spin * rs;
  float const dt = d_step_size;
  int const maxSteps = d_max_steps;
  /* Escape only outside both the scene radius and the camera's own radius while
   * moving outward (bhEscapeRadius in interop_trace.glsl). */
  float const maxDist = fmaxf(d_max_dist, 1.01f * d_length(cam));
  bool const doKerr = (d_kerr_enabled != 0);

  /* Compute ray directions for both pixels */
  int const px0 = idx0 % d_width;
  int const py0 = idx0 / d_width;
  float3 const dir0 = d_world_to_physics(d_ray_dir(px0, py0));

  bool const hasRay1 = (idx1 < totalPixels);
  int px1 = 0;
  int py1 = 0;
  float3 dir1 = make_f3(0.0f, 0.0f, -1.0f);
  if (hasRay1) {
    px1 = idx1 % d_width;
    py1 = idx1 / d_width;
    dir1 = d_world_to_physics(d_ray_dir(px1, py1));
  }

  /* Initialize hit results */
  HitResult hit0{};
  hit0.hit_disk = hit0.hit_horizon = hit0.escaped = hit0.max_steps = false;
  hit0.hit_point = make_f3(0.0f, 0.0f, 0.0f);
  hit0.origin = cam;
  hit0.closest_approach_point = cam;
  hit0.phi = 0.0f;
  hit0.photon_lambda = 0.0f;
  hit0.min_radius = d_length(cam);
  hit0.closest_approach_update_count = 0;
  hit0.first_closest_approach_step = -1;
  hit0.last_closest_approach_step = -1;
  HitResult hit1 = hit0;

  if (doKerr) {
    float rHorizon = d_kerr_outer_horizon(rs, aSpin);
    if (rHorizon <= D_EPSILON) {
      rHorizon = rs;
    }
    float const rDiskIn = d_isco;
    float const rDiskOut = 100.0f * rs;

    float const aTrace = d_kerr_trace_spin(aSpin);
    KerrConsts c0;
    KerrRay kr0;
    d_kerr_init_geodesic(cam, dir0, rs, aTrace, c0, kr0);
    KerrConsts c1;
    KerrRay kr1;
    d_kerr_init_geodesic(cam, dir1, rs, aTrace, c1, kr1);
    hit0.origin = d_kerr_chart_position(cam, rs, aTrace);
    hit0.closest_approach_point = hit0.origin;
    hit1.origin = hit0.origin;
    hit1.closest_approach_point = hit0.origin;

    /* Pack initial ray state into __half2 pairs.
     * hMinr tracks min(r0, r1) across steps via __hmin2 (one HMNMX2 SASS
     * instruction per step instead of two fminf -- 2x FP16 throughput). */
    HalfRayPair hp = raysToPair(kr0, kr1);
    __half2 hMinr = __floats2half2_rn(hit0.min_radius, hit1.min_radius);

    bool done0 = false;
    bool done1 = !hasRay1;

    for (int step = 0; step < maxSteps; ++step) {
      if (done0 && done1) {
        break;
      }

      /* Promote both rays from packed storage to FP32 for this step:
       * pairToRays unpacks hR and copies the FP32 fields in one pass. */
      pairToRays(hp, kr0, kr1);

      /* Update min-radius pair before any horizon check so the packed
       * __hmin2 runs on fresh values. */
      hMinr = __hmin2(hMinr, hp.hR);

      /* --- Ray 0 step --- */
      if (!done0) {
        float3 const old0 = d_kerr_ray_position(kr0);
        d_record_closest_approach(hit0, kr0.r, old0, step);

        if (kr0.r <= rHorizon) {
          hit0.hit_horizon = true;
          hit0.hit_point = old0;
          done0 = true;
        } else {
          /* D10: adaptive step near horizon -- matches FP32_COARSENED quality */
          float const sdt0 = d_adaptive_step(kr0.r, rs, rHorizon, dt);
          d_kerr_step(kr0, rs, aTrace, c0, sdt0);
          float3 const new0 = d_kerr_ray_position(kr0);

          if (d_adisk_enabled != 0) {
            float3 dh;
            if (d_check_disk(old0, new0, rDiskIn, rDiskOut, dh)) {
              hit0.hit_disk = true;
              hit0.hit_point = dh;
              hit0.phi = atan2f(dh.y, dh.x);
              hit0.photon_lambda = -c0.Lz;
              done0 = true;
            }
          }
          if (!done0 && kr0.r > maxDist && kr0.vr > 0.0f) {
            hit0.escaped = true;
            hit0.hit_point = new0;
            done0 = true;
          }
        }
      }

      /* --- Ray 1 step (interleaved for dual-issue ILP) --- */
      if (!done1) {
        float3 const old1 = d_kerr_ray_position(kr1);
        d_record_closest_approach(hit1, kr1.r, old1, step);

        if (kr1.r <= rHorizon) {
          hit1.hit_horizon = true;
          hit1.hit_point = old1;
          done1 = true;
        } else {
          float const sdt1 = d_adaptive_step(kr1.r, rs, rHorizon, dt);
          d_kerr_step(kr1, rs, aTrace, c1, sdt1);
          float3 const new1 = d_kerr_ray_position(kr1);

          if (d_adisk_enabled != 0) {
            float3 dh;
            if (d_check_disk(old1, new1, rDiskIn, rDiskOut, dh)) {
              hit1.hit_disk = true;
              hit1.hit_point = dh;
              hit1.phi = atan2f(dh.y, dh.x);
              hit1.photon_lambda = -c1.Lz;
              done1 = true;
            }
          }
          if (!done1 && kr1.r > maxDist && kr1.vr > 0.0f) {
            hit1.escaped = true;
            hit1.hit_point = new1;
            done1 = true;
          }
        }
      }

      /* Demote updated FP32 state back to packed FP16 for next step.
       * raysToPair emits F2FP2 SASS for each __floats2half2_rn call. */
      hp = raysToPair(kr0, kr1);
    }

    /* Extract packed min_radius values */
    float2 const mr = __half22float2(hMinr);
    hit0.min_radius = mr.x;
    hit1.min_radius = mr.y;

    /* Handle rays that ran out of steps */
    pairToRays(hp, kr0, kr1);
    if (!done0) {
      hit0.escaped = true;
      hit0.max_steps = true;
      hit0.hit_point = d_kerr_ray_position(kr0);
    }
    if (!done1 && hasRay1) {
      hit1.escaped = true;
      hit1.max_steps = true;
      hit1.hit_point = d_kerr_ray_position(kr1);
    }
  } else {
    /* Schwarzschild: interleaved RK4 */
    float3 pos0 = cam;
    float3 vel0 = dir0;
    float3 pos1 = cam;
    float3 vel1 = dir1;
    float const rDiskIn = d_isco;
    float const rDiskOut = 100.0f * rs;
    bool done0 = false;
    bool done1 = !hasRay1;

    for (int step = 0; step < maxSteps; ++step) {
      if (done0 && done1) {
        break;
      }

      if (!done0) {
        float3 const old0 = pos0;
        d_step_rk4(pos0, vel0, rs, dt);
        float const r = d_length(pos0);
        d_record_closest_approach(hit0, r, pos0, step);
        if (r <= rs) {
          hit0.hit_horizon = true;
          hit0.hit_point = pos0;
          done0 = true;
        } else if (d_adisk_enabled != 0) {
          float3 dh;
          if (d_check_disk(old0, pos0, rDiskIn, rDiskOut, dh)) {
            hit0.hit_disk = true;
            hit0.hit_point = dh;
            hit0.phi = atan2f(dh.y, dh.x);
            hit0.photon_lambda = d_schwarzschild_photon_lambda(cam, dir0, rs);
            done0 = true;
          }
        }
        if (!done0 && r > maxDist && d_dot(pos0, vel0) > 0.0f) {
          hit0.escaped = true;
          hit0.hit_point = pos0;
          done0 = true;
        }
      }

      if (!done1) {
        float3 const old1 = pos1;
        d_step_rk4(pos1, vel1, rs, dt);
        float const r = d_length(pos1);
        d_record_closest_approach(hit1, r, pos1, step);
        if (r <= rs) {
          hit1.hit_horizon = true;
          hit1.hit_point = pos1;
          done1 = true;
        } else if (d_adisk_enabled != 0) {
          float3 dh;
          if (d_check_disk(old1, pos1, rDiskIn, rDiskOut, dh)) {
            hit1.hit_disk = true;
            hit1.hit_point = dh;
            hit1.phi = atan2f(dh.y, dh.x);
            hit1.photon_lambda = d_schwarzschild_photon_lambda(cam, dir1, rs);
            done1 = true;
          }
        }
        if (!done1 && r > maxDist && d_dot(pos1, vel1) > 0.0f) {
          hit1.escaped = true;
          hit1.hit_point = pos1;
          done1 = true;
        }
      }
    }

    if (!done0) {
      hit0.escaped = true;
      hit0.max_steps = true;
      hit0.hit_point = pos0;
    }
    if (!done1 && hasRay1) {
      hit1.escaped = true;
      hit1.max_steps = true;
      hit1.hit_point = pos1;
    }
  }

  /* Shade and write both pixels with optional wiregrid overlay */
  auto const applyWGH2 = [](float4 c, HitResult const& h) -> float4 {
    if (d_wiregrid_enabled == 0) return c;
    float3 hp = h.hit_point;
    float r = sqrtf(hp.x*hp.x + hp.y*hp.y + hp.z*hp.z);
    if (r < 1e-5f) return c;
    float theta = acosf(fmaxf(-1.0f, fminf(hp.z / r, 1.0f)));
    float phi   = atan2f(hp.y, hp.x);
    float4 wg = d_wiregrid_overlay(r, theta, phi, d_spin,
                                   d_wiregrid_show_ergo != 0.0f, d_wiregrid_grid_scale);
    float alpha = d_wg_overlay_blend_alpha(wg, make_f3(c.x, c.y, c.z));
    float inv_a = 1.0f - alpha;
    return make_float4(c.x*inv_a + wg.x*alpha, c.y*inv_a + wg.y*alpha,
                       c.z*inv_a + wg.z*alpha, c.w);
  };
  dFramebuffer[idx0] = applyWGH2(d_shade_hit(hit0, hit0.origin), hit0);
  if (hasRay1) {
    dFramebuffer[idx1] = applyWGH2(d_shade_hit(hit1, hit1.origin), hit1);
  }
}

/**
 * @brief Launch the FP16 H2 ILP kernel (2 rays/thread, 1D blocks of 128).
 *
 * @param dFramebuffer Device framebuffer pointer (float4[width*height]).
 * @param width        Framebuffer width in pixels.
 * @param height       Framebuffer height in pixels.
 * @param stream       CUDA stream to launch on.
 */
extern "C" void launchFp16H2Ilp(float4 *dFramebuffer, int width, int height, cudaStream_t stream) {
  int const totalPixels = width * height;
  int const threadsNeeded = (totalPixels + 1) / 2;
  dim3 const block(128);
  dim3 const grid(static_cast<unsigned int>((threadsNeeded + 127) / 128));
  geodesicTraceFp16H2<<<grid, block, 0, stream>>>(dFramebuffer);
}
