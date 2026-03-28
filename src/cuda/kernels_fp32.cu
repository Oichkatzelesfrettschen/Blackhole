/**
 * @file kernels_fp32.cu
 * @brief FP32 baseline and FP32 coarsened geodesic tracing kernels.
 *
 * - Baseline: 1 thread = 1 pixel = 1 ray, 16x16 thread blocks.
 * - Coarsened: 1 thread = 2 pixels = 2 rays, interleaved per-step ILP.
 *
 * Output: linear float4* dFramebuffer (perfectly coalesced writes).
 * Parameters are read from __constant__ memory populated by kernel_launch.cu.
 */

#include <driver_types.h>     /* cudaStream_t */
#include <math.h>             // NOLINT(modernize-deprecated-headers) -- CUDA device code
#include <vector_functions.h> /* make_float3 */
#include <vector_types.h>     /* float2, float3, float4, dim3 */

#include "device_physics.cuh"

/* ========================================================================
 * FP32 Baseline Kernel
 * ======================================================================== */

/**
 * @brief FP32 baseline geodesic tracing kernel (1 ray per thread).
 *
 * Each thread maps to one framebuffer pixel. Reads all scene parameters from
 * __constant__ memory, traces a Kerr or Schwarzschild geodesic, shades the
 * hit result, and writes a float4 RGBA value to the linear framebuffer.
 *
 * @param dFramebuffer Device pointer to float4[d_width * d_height]; output RGBA pixels.
 */
__launch_bounds__(256, 4)
    // NOLINTNEXTLINE(misc-use-internal-linkage) -- __global__ cannot be static or in anonymous
    // namespace
    __global__ void geodesicTraceFp32(float4 *__restrict__ dFramebuffer) {
  int const px = static_cast<int>((blockIdx.x * blockDim.x) + threadIdx.x);
  int const py = static_cast<int>((blockIdx.y * blockDim.y) + threadIdx.y);
  if (px >= d_width || py >= d_height) {
    return;
  }

  float3 const cam = make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]);
  float3 const dir = d_ray_dir(px, py);

  float4 color;
  /* D4: Stokes polarized path supersedes scalar RTE; D3: scalar RTE.
   * Volumetric modes now return a terminal position for wiregrid parity. */
  if (d_stokes_enabled) {
    float3 term_pos;
    color = d_trace_geodesic_stokes(cam, dir, &term_pos);
    if (d_wiregrid_enabled != 0) {
      float const r_bl = sqrtf(term_pos.x * term_pos.x + term_pos.y * term_pos.y + term_pos.z * term_pos.z);
      if (r_bl > 1e-5f) {
        float const theta_bl = acosf(fmaxf(-1.0f, fminf(term_pos.z / r_bl, 1.0f)));
        float const phi_bl   = atan2f(term_pos.y, term_pos.x);
        float4 const wg = d_wiregrid_overlay(r_bl, theta_bl, phi_bl,
                                             d_spin, d_wiregrid_show_ergo != 0.0f,
                                             d_wiregrid_grid_scale);
        float const alpha = wg.w * d_wg_overlay_attenuation(make_f3(color.x, color.y, color.z));
        float const inv_a = 1.0f - alpha;
        color = make_float4(color.x * inv_a + wg.x * alpha,
                            color.y * inv_a + wg.y * alpha,
                            color.z * inv_a + wg.z * alpha,
                            color.w);
      }
    }
  } else if (d_rte_enabled) {
    float3 term_pos;
    color = d_trace_geodesic_rte(cam, dir, &term_pos);
    if (d_wiregrid_enabled != 0) {
      float const r_bl = sqrtf(term_pos.x * term_pos.x + term_pos.y * term_pos.y + term_pos.z * term_pos.z);
      if (r_bl > 1e-5f) {
        float const theta_bl = acosf(fmaxf(-1.0f, fminf(term_pos.z / r_bl, 1.0f)));
        float const phi_bl   = atan2f(term_pos.y, term_pos.x);
        float4 const wg = d_wiregrid_overlay(r_bl, theta_bl, phi_bl,
                                             d_spin, d_wiregrid_show_ergo != 0.0f,
                                             d_wiregrid_grid_scale);
        float const alpha = wg.w * d_wg_overlay_attenuation(make_f3(color.x, color.y, color.z));
        float const inv_a = 1.0f - alpha;
        color = make_float4(color.x * inv_a + wg.x * alpha,
                            color.y * inv_a + wg.y * alpha,
                            color.z * inv_a + wg.z * alpha,
                            color.w);
      }
    }
  } else {
    HitResult const hit = d_trace_geodesic(cam, dir);
    color = d_shade_hit(hit, cam);

    /* Wiregrid BL-coord overlay (task A4): convert Cartesian hit->spherical BL */
    if (d_wiregrid_enabled != 0) {
      float3 const hp = hit.hit_point;
      float const r_bl = sqrtf(hp.x*hp.x + hp.y*hp.y + hp.z*hp.z);
      if (r_bl > 1e-5f) {
        float const theta_bl = acosf(fmaxf(-1.0f, fminf(hp.z / r_bl, 1.0f)));
        float const phi_bl   = atan2f(hp.y, hp.x);
        float4 const wg = d_wiregrid_overlay(r_bl, theta_bl, phi_bl,
                                              d_spin, d_wiregrid_show_ergo != 0.0f,
                                              d_wiregrid_grid_scale);
        float const alpha = wg.w * d_wg_overlay_attenuation(make_f3(color.x, color.y, color.z));
        float const inv_a = 1.0f - alpha;
        color = make_float4(color.x*inv_a + wg.x*alpha,
                            color.y*inv_a + wg.y*alpha,
                            color.z*inv_a + wg.z*alpha,
                            color.w);
      }
    }
  }
  /* Perfectly coalesced linear write: adjacent threads write adjacent float4s */
  dFramebuffer[(py * d_width) + px] = color;
}

/* ========================================================================
 * FP32 Coarsened Kernel (2 pixels per thread, true ILP)
 *
 * Following YSU-engine kernels_fp16_soa_half2.cu interleaved pattern at FP32.
 * Thread k handles linearized pixels (2k) and (2k+1).
 *
 * WHY interleaved (not sequential): calling d_trace_geodesic(ray0) then
 * d_trace_geodesic(ray1) sequentially gives zero ILP -- the second chain
 * only starts after the first loop completes. True ILP requires per-step
 * interleaving: both rays advance one RK4 step per iteration, giving the
 * Ada warp scheduler two independent FMA chains to dual-issue simultaneously.
 *
 * The full integration loop is replicated explicitly rather than calling
 * d_trace_geodesic so that both ray chains are visible to the scheduler
 * within the same basic block.
 * ======================================================================== */

/**
 * @brief FP32 coarsened geodesic tracing kernel (2 rays per thread, interleaved ILP).
 *
 * Thread k processes linearized pixel indices 2k and 2k+1. Both geodesic
 * chains advance one integration step per loop iteration, exposing independent
 * FMA instruction chains to the Ada warp dual-issue scheduler. The explicit
 * loop replaces two sequential d_trace_geodesic() calls to make both chains
 * visible within the same basic block.
 *
 * @param dFramebuffer Device pointer to float4[d_width * d_height]; output RGBA pixels.
 */
/* WHY 128 not 256: __launch_bounds__(256, 4) forces the compiler to target
 * 65536/(256*4)=64 regs/thread on SM8.9, which is insufficient for two live
 * FP32 ray states (~80 regs needed).  The excess overflows to local memory.
 * __launch_bounds__(128, 4) gives a 128-reg budget (same as H2 ILP) and
 * achieves the same 33% minimum occupancy without spill. */
__launch_bounds__(128, 4)
    // NOLINTNEXTLINE(misc-use-internal-linkage,readability-function-cognitive-complexity)
    __global__ void geodesicTraceFp32Coarsened(float4 *__restrict__ dFramebuffer) {
  int const tid = static_cast<int>((blockIdx.x * blockDim.x) + threadIdx.x);
  int const totalPixels = d_width * d_height;
  int const idx0 = 2 * tid;
  int const idx1 = idx0 + 1;

  if (idx0 >= totalPixels) {
    return;
  }

  float3 const cam = make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]);
  float const rs = d_rs;
  float const dt = d_step_size;
  int const maxSteps = d_max_steps;
  float const maxDist = d_max_dist;
  bool const doKerr = (d_kerr_enabled != 0) && (fabsf(d_spin) > D_EPSILON);
  float const aSpin = 0.5f * d_spin * rs;

  int const px0 = idx0 % d_width;
  int const py0 = idx0 / d_width;
  float3 const dir0 = d_ray_dir(px0, py0);

  bool const hasRay1 = (idx1 < totalPixels);
  int px1 = 0;
  int py1 = 0;
  float3 dir1 = make_f3(0.0f, 0.0f, -1.0f);
  if (hasRay1) {
    px1 = idx1 % d_width;
    py1 = idx1 / d_width;
    dir1 = d_ray_dir(px1, py1);
  }

  HitResult hit0{};
  hit0.hit_disk = hit0.hit_horizon = hit0.escaped = false;
  hit0.hit_point = make_f3(0.0f, 0.0f, 0.0f);
  hit0.phi = 0.0f;
  hit0.redshift = 1.0f;
  hit0.min_radius = d_length(cam);
  HitResult hit1 = hit0;

  if (doKerr) {
    float rHorizon = d_kerr_outer_horizon(rs, aSpin);
    if (rHorizon <= D_EPSILON) {
      rHorizon = rs;
    }
    float const rDiskIn = d_isco;
    float const rDiskOut = 100.0f * rs;

    KerrConsts const c0 = d_kerr_init_consts(cam, dir0, rs, aSpin);
    KerrRay kr0 = d_kerr_init_ray(cam, dir0);
    KerrConsts const c1 = d_kerr_init_consts(cam, dir1, rs, aSpin);
    KerrRay kr1 = d_kerr_init_ray(cam, dir1);

    bool done0 = false;
    bool done1 = !hasRay1;

    for (int step = 0; step < maxSteps; ++step) {
      if (done0 && done1) {
        break;
      }

      /* Ray 0 -- independent of ray 1, enabling dual-issue */
      if (!done0) {
        hit0.min_radius = fminf(hit0.min_radius, kr0.r);
        float3 const old0 = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);

        if (kr0.r <= rHorizon) {
          hit0.hit_horizon = true;
          hit0.hit_point = old0;
          done0 = true;
        } else {
          /* D10: adaptive step near horizon and photon sphere */
          float const sdt0 = d_adaptive_step(kr0.r, rs, rHorizon, dt);
          d_kerr_step(kr0, rs, aSpin, c0, sdt0);
          float3 const new0 = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);
          if (d_adisk_enabled != 0) {
            float3 dh;
            if (d_check_disk(old0, new0, rDiskIn, rDiskOut, dh)) {
              hit0.hit_disk = true;
              hit0.hit_point = dh;
              hit0.phi = atan2f(dh.y, dh.x);
              hit0.redshift = d_redshift_factor(d_length(dh), rs);
              done0 = true;
            }
          }
          if (!done0 && kr0.r > maxDist) {
            hit0.escaped = true;
            hit0.hit_point = new0;
            done0 = true;
          }
        }
      }

      /* Ray 1 -- interleaved: both chains visible in the same loop body */
      if (!done1) {
        hit1.min_radius = fminf(hit1.min_radius, kr1.r);
        float3 const old1 = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);

        if (kr1.r <= rHorizon) {
          hit1.hit_horizon = true;
          hit1.hit_point = old1;
          done1 = true;
        } else {
          float const sdt1 = d_adaptive_step(kr1.r, rs, rHorizon, dt);
          d_kerr_step(kr1, rs, aSpin, c1, sdt1);
          float3 const new1 = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);
          if (d_adisk_enabled != 0) {
            float3 dh;
            if (d_check_disk(old1, new1, rDiskIn, rDiskOut, dh)) {
              hit1.hit_disk = true;
              hit1.hit_point = dh;
              hit1.phi = atan2f(dh.y, dh.x);
              hit1.redshift = d_redshift_factor(d_length(dh), rs);
              done1 = true;
            }
          }
          if (!done1 && kr1.r > maxDist) {
            hit1.escaped = true;
            hit1.hit_point = new1;
            done1 = true;
          }
        }
      }
    }

    if (!done0) {
      hit0.escaped = true;
      hit0.hit_point = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);
    }
    if (!done1 && hasRay1) {
      hit1.escaped = true;
      hit1.hit_point = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);
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
        hit0.min_radius = fminf(hit0.min_radius, r);
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
            hit0.redshift = d_redshift_factor(d_length(dh), rs);
            done0 = true;
          }
        }
        if (!done0 && r > maxDist) {
          hit0.escaped = true;
          hit0.hit_point = pos0;
          done0 = true;
        }
      }

      if (!done1) {
        float3 const old1 = pos1;
        d_step_rk4(pos1, vel1, rs, dt);
        float const r = d_length(pos1);
        hit1.min_radius = fminf(hit1.min_radius, r);
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
            hit1.redshift = d_redshift_factor(d_length(dh), rs);
            done1 = true;
          }
        }
        if (!done1 && r > maxDist) {
          hit1.escaped = true;
          hit1.hit_point = pos1;
          done1 = true;
        }
      }
    }

    if (!done0) {
      hit0.escaped = true;
      hit0.hit_point = pos0;
    }
    if (!done1 && hasRay1) {
      hit1.escaped = true;
      hit1.hit_point = pos1;
    }
  }

  /* Apply wiregrid overlay and write */
  auto const applyWG = [](float4 c, HitResult const& h) -> float4 {
    if (d_wiregrid_enabled == 0) return c;
    float3 hp = h.hit_point;
    float r = sqrtf(hp.x*hp.x + hp.y*hp.y + hp.z*hp.z);
    if (r < 1e-5f) return c;
    float theta = acosf(fmaxf(-1.0f, fminf(hp.z / r, 1.0f)));
    float phi   = atan2f(hp.y, hp.x);
    float4 wg = d_wiregrid_overlay(r, theta, phi, d_spin,
                                   d_wiregrid_show_ergo != 0.0f, d_wiregrid_grid_scale);
    float alpha = wg.w * d_wg_overlay_attenuation(make_f3(c.x, c.y, c.z));
    float inv_a = 1.0f - alpha;
    return make_float4(c.x*inv_a + wg.x*alpha, c.y*inv_a + wg.y*alpha,
                       c.z*inv_a + wg.z*alpha, c.w);
  };
  dFramebuffer[idx0] = applyWG(d_shade_hit(hit0, cam), hit0);
  if (hasRay1) {
    dFramebuffer[idx1] = applyWG(d_shade_hit(hit1, cam), hit1);
  }
}

/* ========================================================================
 * Host wrapper to launch FP32 kernels
 * ======================================================================== */

/**
 * @brief Launch the FP32 baseline kernel (1 ray/thread, 16x16 blocks).
 *
 * @param dFramebuffer Device framebuffer pointer (float4[width*height]).
 * @param width        Framebuffer width in pixels.
 * @param height       Framebuffer height in pixels.
 * @param stream       CUDA stream to launch on.
 */
extern "C" void launchFp32Baseline(float4 *dFramebuffer, int width, int height,
                                   cudaStream_t stream) {
  dim3 const block(16, 16);
  dim3 const grid(static_cast<unsigned int>((width + 15) / 16),
                  static_cast<unsigned int>((height + 15) / 16));
  geodesicTraceFp32<<<grid, block, 0, stream>>>(dFramebuffer);
}

/**
 * @brief Launch the FP32 coarsened kernel (2 rays/thread, 1D blocks of 256).
 *
 * @param dFramebuffer Device framebuffer pointer (float4[width*height]).
 * @param width        Framebuffer width in pixels.
 * @param height       Framebuffer height in pixels.
 * @param stream       CUDA stream to launch on.
 */
extern "C" void launchFp32Coarsened(float4 *dFramebuffer, int width, int height,
                                    cudaStream_t stream) {
  int const totalPixels = width * height;
  int const threadsNeeded = (totalPixels + 1) / 2;
  dim3 const block(128);
  dim3 const grid(static_cast<unsigned int>((threadsNeeded + 127) / 128));
  geodesicTraceFp32Coarsened<<<grid, block, 0, stream>>>(dFramebuffer);
}
