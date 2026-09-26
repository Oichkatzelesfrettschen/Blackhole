/**
 * @file device_disk_transfer.cuh
 * @brief CUDA twins of the Page-Thorne flux, orbiting-emitter shift and
 *        blackbody chroma (shader/include/disk_transfer.glsl).
 *
 * M = 1 units, signed spin a with the disk orbiting in +phi; g is
 * E_obs / E_emit for an observer at rest at infinity, and the renderer draws
 * bolometric g^4 F / F_peak times the unit-luminance chroma at g T_emit
 * (physics/disk_transfer.h). Pure functions of their arguments with no
 * __constant__ state, so tests/cuda_disk_transfer_test.cu can call them
 * directly and compare against the double-precision C++ in
 * src/physics/page_thorne.h and src/physics/disk_transfer.h.
 *
 * FIREWALL: includes only <cuda_runtime.h> and <math.h>, like device_physics.cuh.
 */

#ifndef BLACKHOLE_CUDA_DEVICE_DISK_TRANSFER_CUH
#define BLACKHOLE_CUDA_DEVICE_DISK_TRANSFER_CUH

#include <cuda_runtime.h>
#include <math.h>

/** @brief ISCO radius (M = 1) for a disk orbiting in +phi; twin of isco_radius. */
__host__ __device__ __forceinline__ float d_dt_isco_radius(float a) {
    a = fmaxf(-0.9999f, fminf(a, 0.9999f));
    float const z1 = 1.0f + cbrtf(1.0f - a * a) * (cbrtf(1.0f + a) + cbrtf(1.0f - a));
    float const z2 = sqrtf(3.0f * a * a + z1 * z1);
    float const root = sqrtf((3.0f - z1) * (3.0f + z1 + 2.0f * z2));
    return a >= 0.0f ? 3.0f + z2 - root : 3.0f + z2 + root;
}

/**
 * @brief Page-Thorne flux shape S(r) = F(r) 8 pi / (3 Mdot); zero inside the ISCO.
 *
 * x2 comes from Vieta's product x1 x2 x3 = -2a so it stays accurate in float
 * as x2 -> 0 at a -> 0, where its term vanishes.
 */
__host__ __device__ __forceinline__ float d_dt_page_thorne_shape(float r, float a) {
    float const r_isco = d_dt_isco_radius(a);
    if (!(r > r_isco)) {
        return 0.0f;
    }
    float const x = sqrtf(r);
    float const x0 = sqrtf(r_isco);
    float const theta = acosf(fmaxf(-1.0f, fminf(a, 1.0f))) / 3.0f;
    float const x1 = 2.0f * cosf(theta - 1.0471975512f);
    float const x3 = -2.0f * cosf(theta);
    float const x2 = -2.0f * a / (x1 * x3);

    float bracket = x - x0 - 1.5f * a * logf(x / x0);
    bracket -= 3.0f * (x1 - a) * (x1 - a) / (x1 * (x1 - x2) * (x1 - x3)) *
               logf((x - x1) / (x0 - x1));
    if (fabsf(x2) > 1e-7f) {
        bracket -= 3.0f * (x2 - a) * (x2 - a) / (x2 * (x2 - x1) * (x2 - x3)) *
                   logf((x - x2) / (x0 - x2));
    }
    bracket -= 3.0f * (x3 - a) * (x3 - a) / (x3 * (x3 - x1) * (x3 - x2)) *
               logf((x - x3) / (x0 - x3));
    float const q = x * x * x - 3.0f * x + 2.0f * a;
    return fmaxf(bracket, 0.0f) / (x * x * x * x * q);
}

/**
 * @brief g = 1 / (u^t (1 - Omega lambda)) for a Keplerian emitter at r and a
 *        photon with lambda = Lz / E; 0 where no circular orbit exists or the
 *        photon's local energy would be non-positive.
 */
__host__ __device__ __forceinline__ float d_dt_disk_transfer_g(float r, float a, float lambda) {
    float const r32 = r * sqrtf(r);
    float const inv_r32 = 1.0f / r32;
    float const q = 1.0f - 3.0f / r + 2.0f * a * inv_r32;
    if (!(q > 0.0f)) {
        return 0.0f;
    }
    float const ut = (1.0f + a * inv_r32) / sqrtf(q);
    float const denom = 1.0f - lambda / (r32 + a);
    if (!(denom > 0.0f)) {
        return 0.0f;
    }
    return 1.0f / (ut * denom);
}

/**
 * @brief Linear-sRGB blackbody chromaticity at luminance Y = 1 (Kim et al.
 *        2002 Planckian-locus fit, 1667-25000 K, out-of-gamut clipped).
 */
__host__ __device__ __forceinline__ float3 d_dt_blackbody_chroma(float temperature_k) {
    float const t = fmaxf(1667.0f, fminf(temperature_k, 25000.0f));
    float const inv = 1.0e3f / t;
    float const inv2 = inv * inv;
    float const inv3 = inv2 * inv;
    float const xc = t <= 4000.0f
                         ? -0.2661239f * inv3 - 0.2343589f * inv2 + 0.8776956f * inv + 0.179910f
                         : -3.0258469f * inv3 + 2.1070379f * inv2 + 0.2226347f * inv + 0.240390f;
    float const xc2 = xc * xc;
    float const xc3 = xc2 * xc;
    float yc;
    if (t <= 2222.0f) {
        yc = -1.1063814f * xc3 - 1.34811020f * xc2 + 2.18555832f * xc - 0.20219683f;
    } else if (t <= 4000.0f) {
        yc = -0.9549476f * xc3 - 1.37418593f * xc2 + 2.09137015f * xc - 0.16748867f;
    } else {
        yc = 3.0817580f * xc3 - 5.87338670f * xc2 + 3.75112997f * xc - 0.37001483f;
    }
    float const big_x = xc / yc;
    float const big_z = (1.0f - xc - yc) / yc;
    return make_float3(fmaxf(3.2404542f * big_x - 1.5371385f - 0.4985314f * big_z, 0.0f),
                       fmaxf(-0.9692660f * big_x + 1.8760108f + 0.0415560f * big_z, 0.0f),
                       fmaxf(0.0556434f * big_x - 0.2040259f + 1.0572252f * big_z, 0.0f));
}

#endif /* BLACKHOLE_CUDA_DEVICE_DISK_TRANSFER_CUH */
