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

#include "device_physics.cuh"
#include <cuda_fp16.h>

/* ========================================================================
 * FP16 storage helpers
 * ======================================================================== */

/* phi and t are kept in FP32: phi can grow by ~1e5 radians/step near the
 * Kerr horizon (delta -> 0, delta_safe = 1e-6), far exceeding FP16 max 65504.
 * Only r, theta, and sign fields (bounded, slow-varying) use FP16. */
struct HalfRayState {
    __half r, theta;
    float  phi, t;      /* FP32: avoids Inf -> sincosf NaN near horizon */
    __half sign_r, sign_theta;
};

__device__ __forceinline__ HalfRayState kerr_ray_to_half(const KerrRay& kr) {
    HalfRayState h;
    h.r = __float2half(kr.r);
    h.theta = __float2half(kr.theta);
    h.phi = kr.phi;             /* keep FP32 */
    h.t = kr.t;                 /* keep FP32 */
    h.sign_r = __float2half(kr.sign_r);
    h.sign_theta = __float2half(kr.sign_theta);
    return h;
}

__device__ __forceinline__ KerrRay half_to_kerr_ray(const HalfRayState& h) {
    KerrRay kr;
    kr.r = __half2float(h.r);
    kr.theta = __half2float(h.theta);
    kr.phi = h.phi;             /* keep FP32 */
    kr.t = h.t;                 /* keep FP32 */
    kr.sign_r = __half2float(h.sign_r);
    kr.sign_theta = __half2float(h.sign_theta);
    return kr;
}

/* ========================================================================
 * FP16 Storage Kernel
 *
 * Trace geodesic with FP16 intermediate storage of ray state.
 * All Kerr metric arithmetic is FP32; only the ray state between
 * integration steps is stored in FP16 to reduce register pressure.
 * ======================================================================== */

__launch_bounds__(256, 4)
__global__ void geodesic_trace_fp16_storage(float4* __restrict__ d_framebuffer) {
    int px = blockIdx.x * blockDim.x + threadIdx.x;
    int py = blockIdx.y * blockDim.y + threadIdx.y;
    if (px >= d_width || py >= d_height) return;

    float3 cam = make_float3(d_cam_pos[0], d_cam_pos[1], d_cam_pos[2]);
    float3 dir = d_ray_dir(px, py);

    float rs = d_rs;
    float a = 0.5f * d_spin * rs;
    float dt = d_step_size;
    int max_steps = d_max_steps;
    float max_dist = d_max_dist;

    HitResult result;
    result.hit_disk = false;
    result.hit_horizon = false;
    result.escaped = false;
    result.hit_point = make_f3(0.0f, 0.0f, 0.0f);
    result.phi = 0.0f;
    result.redshift = 1.0f;
    result.min_radius = d_length(cam);

    if (d_kerr_enabled && fabsf(a) > D_EPSILON) {
        float r_horizon = d_kerr_outer_horizon(rs, a);
        if (r_horizon <= D_EPSILON) r_horizon = rs;
        float r_disk_in = d_isco;
        float r_disk_out = 100.0f * rs;

        KerrConsts c = d_kerr_init_consts(cam, dir);
        KerrRay kr = d_kerr_init_ray(cam, dir);

        /* Store initial state in FP16 */
        HalfRayState hs = kerr_ray_to_half(kr);

        for (int step = 0; step < max_steps; ++step) {
            /* Promote to FP32 for computation */
            kr = half_to_kerr_ray(hs);

            float3 old_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
            result.min_radius = fminf(result.min_radius, kr.r);

            if (kr.r <= r_horizon) {
                result.hit_horizon = true;
                result.hit_point = old_pos;
                goto shade;
            }

            /* Kerr step in full FP32 precision */
            d_kerr_step(kr, rs, a, c, dt);

            /* Demote back to FP16 for storage */
            hs = kerr_ray_to_half(kr);

            float3 new_pos = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);

            if (d_adisk_enabled) {
                float3 disk_hit;
                if (d_check_disk(old_pos, new_pos, r_disk_in, r_disk_out, disk_hit)) {
                    result.hit_disk = true;
                    result.hit_point = disk_hit;
                    result.phi = atan2f(disk_hit.y, disk_hit.x);
                    result.redshift = d_redshift_factor(d_length(disk_hit), rs);
                    goto shade;
                }
            }

            if (kr.r > max_dist) {
                result.escaped = true;
                result.hit_point = new_pos;
                goto shade;
            }
        }
        result.escaped = true;
        kr = half_to_kerr_ray(hs);
        result.hit_point = d_kerr_to_cartesian(kr.r, kr.theta, kr.phi);
    } else {
        /* Schwarzschild path: FP16 storage of position */
        float3 pos = cam;
        float3 vel = dir;
        float r_disk_in = d_isco;
        float r_disk_out = 100.0f * rs;

        for (int step = 0; step < max_steps; ++step) {
            float3 old_pos = pos;
            d_step_rk4(pos, vel, rs, dt);

            float r = d_length(pos);
            result.min_radius = fminf(result.min_radius, r);

            if (r <= rs) {
                result.hit_horizon = true;
                result.hit_point = pos;
                goto shade;
            }

            if (d_adisk_enabled) {
                float3 disk_hit;
                if (d_check_disk(old_pos, pos, r_disk_in, r_disk_out, disk_hit)) {
                    result.hit_disk = true;
                    result.hit_point = disk_hit;
                    result.phi = atan2f(disk_hit.y, disk_hit.x);
                    result.redshift = d_redshift_factor(d_length(disk_hit), rs);
                    goto shade;
                }
            }

            if (r > max_dist) {
                result.escaped = true;
                result.hit_point = pos;
                goto shade;
            }
        }
        result.escaped = true;
        result.hit_point = pos;
    }

shade:
    d_framebuffer[py * d_width + px] = d_shade_hit(result, cam);
}

/* Host wrapper */
extern "C" void launch_fp16_storage(float4* d_framebuffer, int width, int height,
                                     cudaStream_t stream) {
    dim3 block(16, 16);
    dim3 grid((width + 15) / 16, (height + 15) / 16);
    geodesic_trace_fp16_storage<<<grid, block, 0, stream>>>(d_framebuffer);
}
