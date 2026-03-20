/*
 * kernels_fp32.cu
 * FP32 baseline and FP32 coarsened geodesic tracing kernels.
 *
 * Baseline: 1 thread = 1 pixel = 1 ray. 16x16 thread blocks.
 * Coarsened: 1 thread = 2 pixels = 2 rays, interleaved per-step ILP.
 *
 * Output: linear float4* d_framebuffer (perfectly coalesced writes).
 * Uses __constant__ memory for params (following YSU-engine kernels_fp32_soa_cs.cu).
 */

#include "device_physics.cuh"

/* ========================================================================
 * FP32 Baseline Kernel
 * ======================================================================== */

__launch_bounds__(256, 4)
__global__ void geodesic_trace_fp32(float4* __restrict__ d_framebuffer) {
    int px = blockIdx.x * blockDim.x + threadIdx.x;
    int py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= d_width || py >= d_height) return;

    float3 cam = make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]);
    float3 dir = d_ray_dir(px, py);

    HitResult hit = d_trace_geodesic(cam, dir);
    float4 color = d_shade_hit(hit, cam);

    /* Perfectly coalesced linear write: adjacent threads write adjacent float4s */
    d_framebuffer[py * d_width + px] = color;
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

__launch_bounds__(256, 4)
__global__ void geodesic_trace_fp32_coarsened(float4* __restrict__ d_framebuffer) {
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int total_pixels = d_width * d_height;
    int idx0 = 2 * tid;
    int idx1 = idx0 + 1;

    if (idx0 >= total_pixels) return;

    float3 cam = make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]);
    float rs = d_rs;
    float dt = d_step_size;
    int max_steps = d_max_steps;
    float max_dist = d_max_dist;
    bool do_kerr = d_kerr_enabled && (fabsf(d_spin) > D_EPSILON);
    float a_spin = 0.5f * d_spin * rs;

    int px0 = idx0 % d_width, py0 = idx0 / d_width;
    float3 dir0 = d_ray_dir(px0, py0);

    bool has_ray1 = (idx1 < total_pixels);
    int px1 = 0, py1 = 0;
    float3 dir1 = make_f3(0.0f, 0.0f, -1.0f);
    if (has_ray1) {
        px1 = idx1 % d_width;
        py1 = idx1 / d_width;
        dir1 = d_ray_dir(px1, py1);
    }

    HitResult hit0, hit1;
    hit0.hit_disk = hit0.hit_horizon = hit0.escaped = false;
    hit0.hit_point = make_f3(0.0f, 0.0f, 0.0f);
    hit0.phi = 0.0f; hit0.redshift = 1.0f;
    hit0.min_radius = d_length(cam);
    hit1 = hit0;

    if (do_kerr) {
        float r_horizon = d_kerr_outer_horizon(rs, a_spin);
        if (r_horizon <= D_EPSILON) r_horizon = rs;
        float r_disk_in = d_isco;
        float r_disk_out = 100.0f * rs;

        KerrConsts c0 = d_kerr_init_consts(cam, dir0);
        KerrRay kr0 = d_kerr_init_ray(cam, dir0);
        KerrConsts c1 = d_kerr_init_consts(cam, dir1);
        KerrRay kr1 = d_kerr_init_ray(cam, dir1);

        bool done0 = false, done1 = !has_ray1;

        for (int step = 0; step < max_steps; ++step) {
            if (done0 && done1) break;

            /* Ray 0 -- independent of ray 1, enabling dual-issue */
            if (!done0) {
                hit0.min_radius = fminf(hit0.min_radius, kr0.r);
                float3 old0 = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);

                if (kr0.r <= r_horizon) {
                    hit0.hit_horizon = true; hit0.hit_point = old0; done0 = true;
                } else {
                    d_kerr_step(kr0, rs, a_spin, c0, dt);
                    float3 new0 = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);
                    if (d_adisk_enabled) {
                        float3 dh;
                        if (d_check_disk(old0, new0, r_disk_in, r_disk_out, dh)) {
                            hit0.hit_disk = true; hit0.hit_point = dh;
                            hit0.phi = atan2f(dh.y, dh.x);
                            hit0.redshift = d_redshift_factor(d_length(dh), rs);
                            done0 = true;
                        }
                    }
                    if (!done0 && kr0.r > max_dist) {
                        hit0.escaped = true; hit0.hit_point = new0; done0 = true;
                    }
                }
            }

            /* Ray 1 -- interleaved: both chains visible in the same loop body */
            if (!done1) {
                hit1.min_radius = fminf(hit1.min_radius, kr1.r);
                float3 old1 = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);

                if (kr1.r <= r_horizon) {
                    hit1.hit_horizon = true; hit1.hit_point = old1; done1 = true;
                } else {
                    d_kerr_step(kr1, rs, a_spin, c1, dt);
                    float3 new1 = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);
                    if (d_adisk_enabled) {
                        float3 dh;
                        if (d_check_disk(old1, new1, r_disk_in, r_disk_out, dh)) {
                            hit1.hit_disk = true; hit1.hit_point = dh;
                            hit1.phi = atan2f(dh.y, dh.x);
                            hit1.redshift = d_redshift_factor(d_length(dh), rs);
                            done1 = true;
                        }
                    }
                    if (!done1 && kr1.r > max_dist) {
                        hit1.escaped = true; hit1.hit_point = new1; done1 = true;
                    }
                }
            }
        }

        if (!done0) {
            hit0.escaped = true;
            hit0.hit_point = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);
        }
        if (!done1 && has_ray1) {
            hit1.escaped = true;
            hit1.hit_point = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);
        }
    } else {
        /* Schwarzschild: interleaved RK4 */
        float3 pos0 = cam, vel0 = dir0;
        float3 pos1 = cam, vel1 = dir1;
        float r_disk_in = d_isco;
        float r_disk_out = 100.0f * rs;
        bool done0 = false, done1 = !has_ray1;

        for (int step = 0; step < max_steps; ++step) {
            if (done0 && done1) break;

            if (!done0) {
                float3 old0 = pos0;
                d_step_rk4(pos0, vel0, rs, dt);
                float r = d_length(pos0);
                hit0.min_radius = fminf(hit0.min_radius, r);
                if (r <= rs) {
                    hit0.hit_horizon = true; hit0.hit_point = pos0; done0 = true;
                } else if (d_adisk_enabled) {
                    float3 dh;
                    if (d_check_disk(old0, pos0, r_disk_in, r_disk_out, dh)) {
                        hit0.hit_disk = true; hit0.hit_point = dh;
                        hit0.phi = atan2f(dh.y, dh.x);
                        hit0.redshift = d_redshift_factor(d_length(dh), rs);
                        done0 = true;
                    }
                }
                if (!done0 && r > max_dist) {
                    hit0.escaped = true; hit0.hit_point = pos0; done0 = true;
                }
            }

            if (!done1) {
                float3 old1 = pos1;
                d_step_rk4(pos1, vel1, rs, dt);
                float r = d_length(pos1);
                hit1.min_radius = fminf(hit1.min_radius, r);
                if (r <= rs) {
                    hit1.hit_horizon = true; hit1.hit_point = pos1; done1 = true;
                } else if (d_adisk_enabled) {
                    float3 dh;
                    if (d_check_disk(old1, pos1, r_disk_in, r_disk_out, dh)) {
                        hit1.hit_disk = true; hit1.hit_point = dh;
                        hit1.phi = atan2f(dh.y, dh.x);
                        hit1.redshift = d_redshift_factor(d_length(dh), rs);
                        done1 = true;
                    }
                }
                if (!done1 && r > max_dist) {
                    hit1.escaped = true; hit1.hit_point = pos1; done1 = true;
                }
            }
        }

        if (!done0) { hit0.escaped = true; hit0.hit_point = pos0; }
        if (!done1 && has_ray1) { hit1.escaped = true; hit1.hit_point = pos1; }
    }

    d_framebuffer[idx0] = d_shade_hit(hit0, cam);
    if (has_ray1) {
        d_framebuffer[idx1] = d_shade_hit(hit1, cam);
    }
}

/* ========================================================================
 * Host wrapper to launch FP32 kernels
 * ======================================================================== */

extern "C" void launch_fp32_baseline(float4* d_framebuffer, int width, int height,
                                      cudaStream_t stream) {
    dim3 block(16, 16);
    dim3 grid((width + 15) / 16, (height + 15) / 16);
    geodesic_trace_fp32<<<grid, block, 0, stream>>>(d_framebuffer);
}

extern "C" void launch_fp32_coarsened(float4* d_framebuffer, int width, int height,
                                       cudaStream_t stream) {
    int total_pixels = width * height;
    int threads_needed = (total_pixels + 1) / 2;
    dim3 block(256);
    dim3 grid((threads_needed + 255) / 256);
    geodesic_trace_fp32_coarsened<<<grid, block, 0, stream>>>(d_framebuffer);
}
