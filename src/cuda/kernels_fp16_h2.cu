/*
 * kernels_fp16_h2.cu
 * H2 ILP variant: 2 rays per thread with __half2 packed intermediate storage.
 *
 * Following YSU-engine kernels_fp16_soa_half2.cu pattern:
 * - Thread k processes pixels (2k, 2k+1) in linearized grid
 * - Two independent geodesic chains interleave on Ada dual-issue FP32 pipelines
 * - __half2 packs both rays' bounded fields into one 32-bit register each:
 *     h_r     = (kr0.r,       kr1.r)        -- both in [r_horizon, max_dist]
 *     h_theta = (kr0.theta,   kr1.theta)    -- both in [0, pi]
 *     h_signr = (kr0.sign_r,  kr1.sign_r)   -- both in {-1, +1}
 *     h_signt = (kr0.sign_theta, kr1.sign_theta)
 *     h_minr  = (min_radius0, min_radius1)  -- tracked via __hmin2
 *   phi and t remain FP32 per ray (can exceed FP16 max near the horizon).
 * - Core Kerr metric FMA stays FP32 for precision.
 * - __half2 promote/demote cost amortized over max_steps iterations.
 *
 * REGISTER PRESSURE WARNING: Kerr RK4 is compute-heavy. If register spill
 * is detected via `ncu --metrics l1tex__t_sectors_pipe_lsu_mem_local_op_ld`,
 * reduce max_steps or demote to FP16_STORAGE. The registry gates this
 * variant at SM89+ to ensure Ada dual-issue FP16 pipelines are present.
 *
 * __launch_bounds__(128, 4) limits active blocks to 4/SM for register budget.
 */

#include "device_physics.cuh"
#include <cuda_fp16.h>

/* ========================================================================
 * HalfRayPair: packed __half2 intermediate storage for 2-ray threads.
 *
 * Fields in []:
 *   h_r, h_theta, h_signr, h_signt -- bounded, safe for FP16
 *   phi0, phi1, t0, t1             -- FP32: can overflow FP16 near horizon
 * ======================================================================== */
struct HalfRayPair {
    __half2 h_r;        /* (kr0.r,          kr1.r)          */
    __half2 h_theta;    /* (kr0.theta,       kr1.theta)      */
    __half2 h_signr;    /* (kr0.sign_r,      kr1.sign_r)     */
    __half2 h_signt;    /* (kr0.sign_theta,  kr1.sign_theta) */
    float phi0, phi1;   /* FP32: phi can reach ~1e5 rad/step */
    float t0, t1;
};

__device__ __forceinline__
HalfRayPair rays_to_pair(const KerrRay& a, const KerrRay& b) {
    HalfRayPair h;
    h.h_r     = __floats2half2_rn(a.r,           b.r);
    h.h_theta = __floats2half2_rn(a.theta,        b.theta);
    h.h_signr = __floats2half2_rn(a.sign_r,       b.sign_r);
    h.h_signt = __floats2half2_rn(a.sign_theta,   b.sign_theta);
    h.phi0 = a.phi;  h.phi1 = b.phi;
    h.t0   = a.t;    h.t1   = b.t;
    return h;
}

__device__ __forceinline__
void pair_to_rays(const HalfRayPair& h, KerrRay& a, KerrRay& b) {
    float2 r  = __half22float2(h.h_r);
    float2 th = __half22float2(h.h_theta);
    float2 sr = __half22float2(h.h_signr);
    float2 st = __half22float2(h.h_signt);
    a.r           = r.x;   b.r           = r.y;
    a.theta       = th.x;  b.theta       = th.y;
    a.sign_r      = sr.x;  b.sign_r      = sr.y;
    a.sign_theta  = st.x;  b.sign_theta  = st.y;
    a.phi = h.phi0;        b.phi = h.phi1;
    a.t   = h.t0;          b.t   = h.t1;
}

/* ========================================================================
 * H2 ILP Kernel: 2 rays/thread, __half2 accumulation
 *
 * Uses interleaved tracing: both rays advance one step at a time,
 * allowing the instruction scheduler to hide latency across the two
 * independent chains.
 * ======================================================================== */

__launch_bounds__(128, 4)
__global__ void geodesic_trace_fp16_h2(float4* __restrict__ d_framebuffer) {
    /* Linearize thread index, each thread owns 2 adjacent pixels */
    int tid = blockIdx.x * blockDim.x + threadIdx.x;
    int total_pixels = d_width * d_height;
    int idx0 = 2 * tid;
    int idx1 = idx0 + 1;

    if (idx0 >= total_pixels) return;

    float3 cam = make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]);
    float rs = d_rs;
    float a_spin = 0.5f * d_spin * rs;
    float dt = d_step_size;
    int max_steps = d_max_steps;
    float max_dist = d_max_dist;
    bool do_kerr = d_kerr_enabled && fabsf(a_spin) > D_EPSILON;

    /* Compute ray directions for both pixels */
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

    /* Initialize hit results */
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

        /* Pack initial ray state into __half2 pairs.
         * h_minr tracks min(r0, r1) across steps via __hmin2 (one HMNMX2 SASS
         * instruction per step instead of two fminf -- 2x FP16 throughput). */
        HalfRayPair hp = rays_to_pair(kr0, kr1);
        __half2 h_minr = __floats2half2_rn(hit0.min_radius, hit1.min_radius);

        bool done0 = false, done1 = !has_ray1;

        for (int step = 0; step < max_steps; ++step) {
            if (done0 && done1) break;

            /* Promote both rays from packed FP16 to FP32 for this step.
             * pair_to_rays unpacks h_r, h_theta, h_signr, h_signt and copies
             * phi/t (already FP32) in a single pass. */
            pair_to_rays(hp, kr0, kr1);

            /* Update min-radius pair before any horizon check so the packed
             * __hmin2 runs on fresh values. */
            h_minr = __hmin2(h_minr, hp.h_r);

            /* --- Ray 0 step --- */
            if (!done0) {
                float3 old0 = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);

                if (kr0.r <= r_horizon) {
                    hit0.hit_horizon = true;
                    hit0.hit_point = old0;
                    done0 = true;
                } else {
                    d_kerr_step(kr0, rs, a_spin, c0, dt);
                    float3 new0 = d_kerr_to_cartesian(kr0.r, kr0.theta, kr0.phi);

                    if (d_adisk_enabled) {
                        float3 dh;
                        if (d_check_disk(old0, new0, r_disk_in, r_disk_out, dh)) {
                            hit0.hit_disk = true;
                            hit0.hit_point = dh;
                            hit0.phi = atan2f(dh.y, dh.x);
                            hit0.redshift = d_redshift_factor(d_length(dh), rs);
                            done0 = true;
                        }
                    }
                    if (!done0 && kr0.r > max_dist) {
                        hit0.escaped = true;
                        hit0.hit_point = new0;
                        done0 = true;
                    }
                }
            }

            /* --- Ray 1 step (interleaved for dual-issue ILP) --- */
            if (!done1) {
                float3 old1 = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);

                if (kr1.r <= r_horizon) {
                    hit1.hit_horizon = true;
                    hit1.hit_point = old1;
                    done1 = true;
                } else {
                    d_kerr_step(kr1, rs, a_spin, c1, dt);
                    float3 new1 = d_kerr_to_cartesian(kr1.r, kr1.theta, kr1.phi);

                    if (d_adisk_enabled) {
                        float3 dh;
                        if (d_check_disk(old1, new1, r_disk_in, r_disk_out, dh)) {
                            hit1.hit_disk = true;
                            hit1.hit_point = dh;
                            hit1.phi = atan2f(dh.y, dh.x);
                            hit1.redshift = d_redshift_factor(d_length(dh), rs);
                            done1 = true;
                        }
                    }
                    if (!done1 && kr1.r > max_dist) {
                        hit1.escaped = true;
                        hit1.hit_point = new1;
                        done1 = true;
                    }
                }
            }

            /* Demote updated FP32 state back to packed FP16 for next step.
             * rays_to_pair emits F2FP2 SASS for each __floats2half2_rn call. */
            hp = rays_to_pair(kr0, kr1);
        }

        /* Extract packed min_radius values */
        float2 mr = __half22float2(h_minr);
        hit0.min_radius = mr.x;
        hit1.min_radius = mr.y;

        /* Handle rays that ran out of steps */
        pair_to_rays(hp, kr0, kr1);
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

    /* Shade and write both pixels */
    d_framebuffer[idx0] = d_shade_hit(hit0, cam);
    if (has_ray1) {
        d_framebuffer[idx1] = d_shade_hit(hit1, cam);
    }
}

/* Host wrapper */
extern "C" void launch_fp16_h2_ilp(float4* d_framebuffer, int width, int height,
                                    cudaStream_t stream) {
    int total_pixels = width * height;
    int threads_needed = (total_pixels + 1) / 2;
    dim3 block(128);
    dim3 grid((threads_needed + 127) / 128);
    geodesic_trace_fp16_h2<<<grid, block, 0, stream>>>(d_framebuffer);
}
