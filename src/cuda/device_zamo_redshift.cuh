/**
 * @file device_zamo_redshift.cuh
 * @brief Equatorial ZAMO-lapse redshift for the no-LUT CUDA paths.
 *
 * physics::kerrRedshift (src/physics/kerr.h) and the redshift LUT built from it
 * take 1 + z = 1 / alpha with the zero-angular-momentum observer's lapse
 * alpha = sqrt(Sigma Delta / A). At the equator, with M = r_s / 2 and
 * a = a* M,
 *
 *   alpha^2 = r^2 Delta / ((r^2 + a^2)^2 - a^2 Delta),  Delta = r^2 - r_s r + a^2.
 *
 * The lapse stays positive through the ergoregion and vanishes at the horizon;
 * z is clamped to [0, 10], the LUT's cap in kerrRedshiftBatch, and a radius at
 * or inside the horizon returns the cap. At a* = 0.9, r = 3M, z = 0.64819.
 *
 * Includes only <cuda_runtime.h> and <math.h> and defines no __constant__
 * symbols, so tests can include it without the renderer's device state.
 */

#ifndef DEVICE_ZAMO_REDSHIFT_CUH
#define DEVICE_ZAMO_REDSHIFT_CUH

#include <cuda_runtime.h>
#include <math.h>

/** @brief Redshift cap shared with the LUT (physics::kerrRedshiftBatch). */
#define D_ZAMO_REDSHIFT_CAP 10.0f

/**
 * @brief Equatorial ZAMO redshift z, clamped to [0, D_ZAMO_REDSHIFT_CAP].
 *
 * @param r      Emission radius (same units as rs).
 * @param rs     Schwarzschild radius r_s = 2M.
 * @param a_star Dimensionless spin a / M (signed; only a^2 enters).
 */
__host__ __device__ __forceinline__ float d_zamo_redshift(float r, float rs, float a_star) {
    float const a = 0.5f * a_star * rs;
    float const a2 = a * a;
    float const r2 = r * r;
    float const delta = r2 - rs * r + a2;
    float const big_a = (r2 + a2) * (r2 + a2) - a2 * delta;
    if (!(delta > 0.0f) || !(big_a > 0.0f)) {
        return D_ZAMO_REDSHIFT_CAP;
    }
    float const lapse = sqrtf(r2 * delta / big_a);
    float const z = 1.0f / lapse - 1.0f;
    return fminf(fmaxf(z, 0.0f), D_ZAMO_REDSHIFT_CAP);
}

#endif /* DEVICE_ZAMO_REDSHIFT_CUH */
