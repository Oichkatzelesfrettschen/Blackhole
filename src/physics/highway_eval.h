/**
 * @file highway_eval.h
 * @brief Highway SIMD evaluation utilities for comparison with xsimd.
 *
 * This header provides Highway implementations of key physics kernels
 * for benchmarking against xsimd and scalar implementations.
 *
 * Highway Approach:
 * - Performance-portable: same code works across x86/ARM/RISC-V
 * - Length-agnostic: code adapts to available vector width
 * - Uses static dispatch for header-only usage simplicity
 *
 * Usage:
 *   #if BLACKHOLE_ENABLE_HIGHWAY
 *   auto result = highway_eval::benchChristoffelAccel(count, iterations);
 *   #endif
 */

#ifndef PHYSICS_HIGHWAY_EVAL_H
#define PHYSICS_HIGHWAY_EVAL_H

#include "constants.h"
#include <vector>
#include <cmath>
#include <chrono>

#if BLACKHOLE_ENABLE_HIGHWAY
#include <hwy/highway.h>
#include <hwy/contrib/math/math-inl.h>
#endif

namespace physics {
namespace highway_eval {

// ============================================================================
// Architecture Detection
// ============================================================================

/**
 * @brief Get the Highway target name if available.
 */
inline const char* getArchitectureName() {
#if BLACKHOLE_ENABLE_HIGHWAY
    return hwy::TargetName(hwy::SupportedTargets());
#else
    return "disabled";
#endif
}

/**
 * @brief Check if Highway is available.
 */
inline bool isAvailable() {
#if BLACKHOLE_ENABLE_HIGHWAY
    return true;
#else
    return false;
#endif
}

/**
 * @brief Get SIMD vector width for doubles.
 */
inline std::size_t getSimdWidth() {
#if BLACKHOLE_ENABLE_HIGHWAY
    // Use the HWY_NAMESPACE to get proper Lanes function
    namespace hn = hwy::HWY_NAMESPACE;
    const HWY_FULL(double) d;
    return hn::Lanes(d);
#else
    return 1;
#endif
}

// ============================================================================
// Benchmark Results Structure
// ============================================================================

struct BenchResult {
    const char* name;
    double scalar_ms;
    double highway_ms;
    double speedup;
    std::size_t elements;
};

// ============================================================================
// Scalar Reference Implementations
// ============================================================================

inline void schwarzschild_f_scalar(
    const double* radii,
    double r_s,
    double* out,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        out[i] = 1.0 - r_s / radii[i];
    }
}

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

// ============================================================================
// Highway SIMD Implementations
// ============================================================================

#if BLACKHOLE_ENABLE_HIGHWAY

namespace hn = hwy::HWY_NAMESPACE;

inline void schwarzschild_f_highway(
    const double* HWY_RESTRICT radii,
    double r_s,
    double* HWY_RESTRICT out,
    std::size_t count) {

    const HWY_FULL(double) d;
    const std::size_t N = hn::Lanes(d);

    const auto one = hn::Set(d, 1.0);
    const auto rs = hn::Set(d, r_s);

    std::size_t i = 0;
    for (; i + N <= count; i += N) {
        auto r = hn::LoadU(d, radii + i);
        auto f = hn::Sub(one, hn::Div(rs, r));
        hn::StoreU(f, d, out + i);
    }

    // Scalar tail
    for (; i < count; ++i) {
        out[i] = 1.0 - r_s / radii[i];
    }
}

inline void redshift_batch_highway(
    const double* HWY_RESTRICT radii,
    double r_s,
    double* HWY_RESTRICT out,
    std::size_t count) {

    const HWY_FULL(double) d;
    const std::size_t N = hn::Lanes(d);

    const auto one = hn::Set(d, 1.0);
    const auto zero = hn::Zero(d);
    const auto rs = hn::Set(d, r_s);

    std::size_t i = 0;
    for (; i + N <= count; i += N) {
        auto r = hn::LoadU(d, radii + i);
        auto f = hn::Sub(one, hn::Div(rs, r));

        // Conditional: sqrt if f > 0, else 0
        auto mask = hn::Gt(f, zero);
        auto sqrt_f = hn::Sqrt(f);
        auto result = hn::IfThenElse(mask, sqrt_f, zero);

        hn::StoreU(result, d, out + i);
    }

    // Scalar tail
    for (; i < count; ++i) {
        double r = radii[i];
        double f = 1.0 - r_s / r;
        out[i] = (f > 0.0) ? std::sqrt(f) : 0.0;
    }
}

inline void christoffel_accel_highway(
    const double* HWY_RESTRICT r,
    const double* HWY_RESTRICT dr,
    const double* HWY_RESTRICT dtheta,
    const double* HWY_RESTRICT dphi,
    const double* HWY_RESTRICT theta,
    double r_s,
    double* HWY_RESTRICT accel_out,
    std::size_t count) {

    const HWY_FULL(double) d;
    const std::size_t N = hn::Lanes(d);

    const auto one = hn::Set(d, 1.0);
    const auto two = hn::Set(d, 2.0);
    const auto rs = hn::Set(d, r_s);
    const auto neg_rs = hn::Set(d, -r_s);

    std::size_t i = 0;
    for (; i + N <= count; i += N) {
        auto r_v = hn::LoadU(d, r + i);
        auto dr_v = hn::LoadU(d, dr + i);
        auto dth_v = hn::LoadU(d, dtheta + i);
        auto dph_v = hn::LoadU(d, dphi + i);
        auto th_v = hn::LoadU(d, theta + i);

        auto f = hn::Sub(one, hn::Div(rs, r_v));

        // Use scalar sin for each lane (Highway math contrib has Sin but needs specific setup)
        // For benchmark fairness, we'll compute sin in the scalar tail or use approximation
        // Here we use a simple vectorized approach
        double sin_arr[8];  // Max SIMD width we might encounter
        double th_arr[8];
        hn::StoreU(th_v, d, th_arr);
        for (std::size_t j = 0; j < N; ++j) {
            sin_arr[j] = std::sin(th_arr[j]);
        }
        auto sin_th = hn::LoadU(d, sin_arr);

        auto r2 = hn::Mul(r_v, r_v);

        // Christoffel symbols
        auto Gamma_r_tt = hn::Div(hn::Mul(rs, f), hn::Mul(two, r2));
        auto Gamma_r_rr = hn::Div(neg_rs, hn::Mul(hn::Mul(two, r2), f));
        auto Gamma_r_thth = hn::Neg(hn::Mul(r_v, f));
        auto Gamma_r_phph = hn::Mul(Gamma_r_thth, hn::Mul(sin_th, sin_th));
        auto dt_dl = hn::Div(one, f);

        // Acceleration computation
        auto accel = hn::Neg(hn::Mul(Gamma_r_tt, hn::Mul(dt_dl, dt_dl)));
        accel = hn::Sub(accel, hn::Mul(Gamma_r_rr, hn::Mul(dr_v, dr_v)));
        accel = hn::Sub(accel, hn::Mul(Gamma_r_thth, hn::Mul(dth_v, dth_v)));
        accel = hn::Sub(accel, hn::Mul(Gamma_r_phph, hn::Mul(dph_v, dph_v)));

        hn::StoreU(accel, d, accel_out + i);
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
}

#endif  // BLACKHOLE_ENABLE_HIGHWAY

// ============================================================================
// Benchmark Harness
// ============================================================================

inline BenchResult benchSchwarzschild_f(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> out_scalar(count);
    std::vector<double> out_highway(count);

    const double r_s = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii[i] = 3.0 * r_s + (97.0 * r_s * static_cast<double>(i) / static_cast<double>(count));
    }

    // Warmup
    schwarzschild_f_scalar(radii.data(), r_s, out_scalar.data(), count);
#if BLACKHOLE_ENABLE_HIGHWAY
    schwarzschild_f_highway(radii.data(), r_s, out_highway.data(), count);
#endif

    // Benchmark scalar
    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschild_f_scalar(radii.data(), r_s, out_scalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    double scalar_ms = std::chrono::duration<double, std::milli>(end - start).count();

    // Benchmark Highway
    double highway_ms = scalar_ms;
#if BLACKHOLE_ENABLE_HIGHWAY
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschild_f_highway(radii.data(), r_s, out_highway.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    highway_ms = std::chrono::duration<double, std::milli>(end - start).count();
#endif

    return {"schwarzschild_f", scalar_ms, highway_ms, scalar_ms / highway_ms, count};
}

inline BenchResult benchRedshift(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> out_scalar(count);
    std::vector<double> out_highway(count);

    const double r_s = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii[i] = 3.0 * r_s + (97.0 * r_s * static_cast<double>(i) / static_cast<double>(count));
    }

    // Warmup
    redshift_batch_scalar(radii.data(), r_s, out_scalar.data(), count);
#if BLACKHOLE_ENABLE_HIGHWAY
    redshift_batch_highway(radii.data(), r_s, out_highway.data(), count);
#endif

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshift_batch_scalar(radii.data(), r_s, out_scalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    double scalar_ms = std::chrono::duration<double, std::milli>(end - start).count();

    double highway_ms = scalar_ms;
#if BLACKHOLE_ENABLE_HIGHWAY
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshift_batch_highway(radii.data(), r_s, out_highway.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    highway_ms = std::chrono::duration<double, std::milli>(end - start).count();
#endif

    return {"redshift_batch", scalar_ms, highway_ms, scalar_ms / highway_ms, count};
}

inline BenchResult benchChristoffelAccel(std::size_t count, int iterations) {
    std::vector<double> r(count), dr(count), dtheta(count), dphi(count), theta(count);
    std::vector<double> out_scalar(count), out_highway(count);

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
#if BLACKHOLE_ENABLE_HIGHWAY
    christoffel_accel_highway(r.data(), dr.data(), dtheta.data(), dphi.data(),
                              theta.data(), r_s, out_highway.data(), count);
#endif

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffel_accel_scalar(r.data(), dr.data(), dtheta.data(), dphi.data(),
                                 theta.data(), r_s, out_scalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    double scalar_ms = std::chrono::duration<double, std::milli>(end - start).count();

    double highway_ms = scalar_ms;
#if BLACKHOLE_ENABLE_HIGHWAY
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffel_accel_highway(r.data(), dr.data(), dtheta.data(), dphi.data(),
                                  theta.data(), r_s, out_highway.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    highway_ms = std::chrono::duration<double, std::milli>(end - start).count();
#endif

    return {"christoffel_accel", scalar_ms, highway_ms, scalar_ms / highway_ms, count};
}

}  // namespace highway_eval
}  // namespace physics

#endif  // PHYSICS_HIGHWAY_EVAL_H
