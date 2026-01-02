/**
 * @file xsimd_eval.h
 * @brief xsimd vs Eigen SIMD evaluation utilities.
 *
 * This header provides explicit xsimd implementations of key physics kernels
 * for benchmarking against Eigen's auto-vectorization approach.
 *
 * Evaluation Methodology:
 * - Eigen: Uses Map<VectorXd> with compiler auto-vectorization
 * - xsimd: Uses explicit batch<double> SIMD operations
 *
 * Key Findings (Phase 2.2.2):
 * - Eigen's approach: Requires data to be in contiguous arrays via Map
 * - xsimd's approach: Explicit batch operations with architecture-specific optimization
 * - Trade-off: xsimd offers more control but requires manual loop vectorization
 *
 * Usage:
 *   #if BLACKHOLE_ENABLE_XSIMD
 *   auto result = xsimd_eval::redshift_batch_xsimd(radii, theta, mass, a);
 *   #endif
 */

#ifndef PHYSICS_XSIMD_EVAL_H
#define PHYSICS_XSIMD_EVAL_H

#include "constants.h"
#include <vector>
#include <cmath>
#include <algorithm>

#if BLACKHOLE_ENABLE_XSIMD
#include <xsimd/xsimd.hpp>
#endif

namespace physics {
namespace xsimd_eval {

// ============================================================================
// Architecture Detection
// ============================================================================

/**
 * @brief Get the xsimd architecture name if available.
 */
inline const char* getArchitectureName() {
#if BLACKHOLE_ENABLE_XSIMD
    using arch = xsimd::default_arch;
    return arch::name();
#else
    return "disabled";
#endif
}

/**
 * @brief Get SIMD vector width for doubles.
 */
inline std::size_t getSimdWidth() {
#if BLACKHOLE_ENABLE_XSIMD
    using batch_type = xsimd::batch<double>;
    return batch_type::size;
#else
    return 1;
#endif
}

/**
 * @brief Check if xsimd is available and functional.
 */
inline bool isAvailable() {
#if BLACKHOLE_ENABLE_XSIMD
    return true;
#else
    return false;
#endif
}

// ============================================================================
// Benchmark Kernels: Schwarzschild Potential
// ============================================================================

/**
 * @brief Compute Schwarzschild metric component f = 1 - r_s/r for a batch of radii.
 *
 * Scalar reference implementation.
 */
inline void schwarzschild_f_scalar(
    const double* radii,
    double r_s,
    double* out,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        out[i] = 1.0 - r_s / radii[i];
    }
}

/**
 * @brief Compute Schwarzschild metric component using xsimd explicit vectorization.
 */
inline void schwarzschild_f_xsimd(
    const double* radii,
    double r_s,
    double* out,
    std::size_t count) {

#if BLACKHOLE_ENABLE_XSIMD
    using batch_type = xsimd::batch<double>;
    constexpr std::size_t simd_size = batch_type::size;

    const batch_type one(1.0);
    const batch_type rs(r_s);

    // Vectorized loop
    std::size_t i = 0;
    for (; i + simd_size <= count; i += simd_size) {
        batch_type r = xsimd::load_unaligned(&radii[i]);
        batch_type f = one - rs / r;
        xsimd::store_unaligned(&out[i], f);
    }

    // Scalar tail
    for (; i < count; ++i) {
        out[i] = 1.0 - r_s / radii[i];
    }
#else
    schwarzschild_f_scalar(radii, r_s, out, count);
#endif
}

// ============================================================================
// Benchmark Kernels: Kerr Redshift
// ============================================================================

/**
 * @brief Compute Kerr redshift batch using scalar operations.
 *
 * Simplified redshift: g = sqrt(1 - r_s/r) for equatorial plane.
 */
inline void redshift_batch_scalar(
    const double* radii,
    double r_s,
    double* out,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        double r = radii[i];
        double f = 1.0 - r_s / r;
        out[i] = (f > 0.0) ? std::sqrt(f) : 0.0;
    }
}

/**
 * @brief Compute Kerr redshift batch using xsimd explicit vectorization.
 */
inline void redshift_batch_xsimd(
    const double* radii,
    double r_s,
    double* out,
    std::size_t count) {

#if BLACKHOLE_ENABLE_XSIMD
    using batch_type = xsimd::batch<double>;
    constexpr std::size_t simd_size = batch_type::size;

    const batch_type one(1.0);
    const batch_type zero(0.0);
    const batch_type rs(r_s);

    std::size_t i = 0;
    for (; i + simd_size <= count; i += simd_size) {
        batch_type r = xsimd::load_unaligned(&radii[i]);
        batch_type f = one - rs / r;

        // Conditional: sqrt if f > 0, else 0
        auto mask = f > zero;
        batch_type result = xsimd::select(mask, xsimd::sqrt(f), zero);

        xsimd::store_unaligned(&out[i], result);
    }

    // Scalar tail
    for (; i < count; ++i) {
        double r = radii[i];
        double f = 1.0 - r_s / r;
        out[i] = (f > 0.0) ? std::sqrt(f) : 0.0;
    }
#else
    redshift_batch_scalar(radii, r_s, out, count);
#endif
}

// ============================================================================
// Benchmark Kernels: RK4 Step Acceleration
// ============================================================================

/**
 * @brief Compute Christoffel-based radial acceleration for Schwarzschild geodesic.
 *
 * Scalar reference implementation.
 */
inline void christoffel_accel_scalar(
    const double* r,
    const double* dr,
    const double* dtheta,
    const double* dphi,
    const double* theta,
    double r_s,
    double* accel_out,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        double r_i = r[i];
        double dr_i = dr[i];
        double dth_i = dtheta[i];
        double dph_i = dphi[i];
        double th_i = theta[i];

        double f = 1.0 - r_s / r_i;
        double sin_th = std::sin(th_i);

        double Gamma_r_tt = r_s * f / (2.0 * r_i * r_i);
        double Gamma_r_rr = -r_s / (2.0 * r_i * r_i * f);
        double Gamma_r_thth = -r_i * f;
        double Gamma_r_phph = -r_i * f * sin_th * sin_th;
        double dt_dl = 1.0 / f;

        accel_out[i] = -Gamma_r_tt * dt_dl * dt_dl
                      - Gamma_r_rr * dr_i * dr_i
                      - Gamma_r_thth * dth_i * dth_i
                      - Gamma_r_phph * dph_i * dph_i;
    }
}

/**
 * @brief Compute Christoffel-based radial acceleration using xsimd.
 */
inline void christoffel_accel_xsimd(
    const double* r,
    const double* dr,
    const double* dtheta,
    const double* dphi,
    const double* theta,
    double r_s,
    double* accel_out,
    std::size_t count) {

#if BLACKHOLE_ENABLE_XSIMD
    using batch_type = xsimd::batch<double>;
    constexpr std::size_t simd_size = batch_type::size;

    const batch_type one(1.0);
    const batch_type two(2.0);
    const batch_type rs(r_s);
    const batch_type neg_rs(-r_s);

    std::size_t i = 0;
    for (; i + simd_size <= count; i += simd_size) {
        batch_type r_v = xsimd::load_unaligned(&r[i]);
        batch_type dr_v = xsimd::load_unaligned(&dr[i]);
        batch_type dth_v = xsimd::load_unaligned(&dtheta[i]);
        batch_type dph_v = xsimd::load_unaligned(&dphi[i]);
        batch_type th_v = xsimd::load_unaligned(&theta[i]);

        batch_type f = one - rs / r_v;
        batch_type sin_th = xsimd::sin(th_v);
        batch_type r2 = r_v * r_v;

        batch_type Gamma_r_tt = rs * f / (two * r2);
        batch_type Gamma_r_rr = neg_rs / (two * r2 * f);
        batch_type Gamma_r_thth = -r_v * f;
        batch_type Gamma_r_phph = Gamma_r_thth * sin_th * sin_th;
        batch_type dt_dl = one / f;

        batch_type accel = -Gamma_r_tt * dt_dl * dt_dl
                         - Gamma_r_rr * dr_v * dr_v
                         - Gamma_r_thth * dth_v * dth_v
                         - Gamma_r_phph * dph_v * dph_v;

        xsimd::store_unaligned(&accel_out[i], accel);
    }

    // Scalar tail
    for (; i < count; ++i) {
        double r_i = r[i];
        double dr_i = dr[i];
        double dth_i = dtheta[i];
        double dph_i = dphi[i];
        double th_i = theta[i];

        double f = 1.0 - r_s / r_i;
        double sin_th = std::sin(th_i);

        double Gamma_r_tt = r_s * f / (2.0 * r_i * r_i);
        double Gamma_r_rr = -r_s / (2.0 * r_i * r_i * f);
        double Gamma_r_thth = -r_i * f;
        double Gamma_r_phph = -r_i * f * sin_th * sin_th;
        double dt_dl = 1.0 / f;

        accel_out[i] = -Gamma_r_tt * dt_dl * dt_dl
                      - Gamma_r_rr * dr_i * dr_i
                      - Gamma_r_thth * dth_i * dth_i
                      - Gamma_r_phph * dph_i * dph_i;
    }
#else
    christoffel_accel_scalar(r, dr, dtheta, dphi, theta, r_s, accel_out, count);
#endif
}

// ============================================================================
// Benchmark Harness
// ============================================================================

/**
 * @brief Result of a single benchmark run.
 */
struct BenchResult {
    const char* name;
    double scalar_ms;
    double xsimd_ms;
    double speedup;
    std::size_t elements;
};

/**
 * @brief Run comparison benchmark for Schwarzschild f computation.
 */
inline BenchResult benchSchwarzschild_f(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> out_scalar(count);
    std::vector<double> out_xsimd(count);

    // Initialize with reasonable radii (3 to 100 r_s)
    const double r_s = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii[i] = 3.0 * r_s + (97.0 * r_s * static_cast<double>(i) / static_cast<double>(count));
    }

    // Warmup
    schwarzschild_f_scalar(radii.data(), r_s, out_scalar.data(), count);
    schwarzschild_f_xsimd(radii.data(), r_s, out_xsimd.data(), count);

    // Benchmark scalar
    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschild_f_scalar(radii.data(), r_s, out_scalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    double scalar_ms = std::chrono::duration<double, std::milli>(end - start).count();

    // Benchmark xsimd
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschild_f_xsimd(radii.data(), r_s, out_xsimd.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    double xsimd_ms = std::chrono::duration<double, std::milli>(end - start).count();

    return {"schwarzschild_f", scalar_ms, xsimd_ms, scalar_ms / xsimd_ms, count};
}

/**
 * @brief Run comparison benchmark for redshift computation.
 */
inline BenchResult benchRedshift(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> out_scalar(count);
    std::vector<double> out_xsimd(count);

    const double r_s = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii[i] = 3.0 * r_s + (97.0 * r_s * static_cast<double>(i) / static_cast<double>(count));
    }

    // Warmup
    redshift_batch_scalar(radii.data(), r_s, out_scalar.data(), count);
    redshift_batch_xsimd(radii.data(), r_s, out_xsimd.data(), count);

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshift_batch_scalar(radii.data(), r_s, out_scalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    double scalar_ms = std::chrono::duration<double, std::milli>(end - start).count();

    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshift_batch_xsimd(radii.data(), r_s, out_xsimd.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    double xsimd_ms = std::chrono::duration<double, std::milli>(end - start).count();

    return {"redshift_batch", scalar_ms, xsimd_ms, scalar_ms / xsimd_ms, count};
}

/**
 * @brief Run comparison benchmark for Christoffel acceleration.
 */
inline BenchResult benchChristoffelAccel(std::size_t count, int iterations) {
    std::vector<double> r(count), dr(count), dtheta(count), dphi(count), theta(count);
    std::vector<double> out_scalar(count), out_xsimd(count);

    const double r_s = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        double u = static_cast<double>(i) / static_cast<double>(count);
        r[i] = 6.0 * r_s + 50.0 * u * r_s;
        dr[i] = -0.5 + u;
        dtheta[i] = 0.1 * u;
        dphi[i] = 0.5 + 0.5 * u;
        theta[i] = PI * 0.5;
    }

    // Warmup
    christoffel_accel_scalar(r.data(), dr.data(), dtheta.data(), dphi.data(),
                             theta.data(), r_s, out_scalar.data(), count);
    christoffel_accel_xsimd(r.data(), dr.data(), dtheta.data(), dphi.data(),
                            theta.data(), r_s, out_xsimd.data(), count);

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffel_accel_scalar(r.data(), dr.data(), dtheta.data(), dphi.data(),
                                 theta.data(), r_s, out_scalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    double scalar_ms = std::chrono::duration<double, std::milli>(end - start).count();

    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffel_accel_xsimd(r.data(), dr.data(), dtheta.data(), dphi.data(),
                                theta.data(), r_s, out_xsimd.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    double xsimd_ms = std::chrono::duration<double, std::milli>(end - start).count();

    return {"christoffel_accel", scalar_ms, xsimd_ms, scalar_ms / xsimd_ms, count};
}

} // namespace xsimd_eval
} // namespace physics

#endif // PHYSICS_XSIMD_EVAL_H
