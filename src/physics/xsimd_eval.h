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

#include <chrono>
#include <cmath>
#include <cstddef>
#include <ratio>
#include <vector> // NOLINT(misc-include-cleaner) -- std::vector used in benchmark functions; transitive provision is fragile

#include "constants.h"

#if BLACKHOLE_ENABLE_XSIMD
#include <xsimd/xsimd.hpp> // NOLINT(misc-include-cleaner) -- xsimd 14 requires the umbrella header for stable public API macros/types
#endif

namespace physics::xsimd_eval {

// ============================================================================
// Architecture Detection
// ============================================================================

/**
 * @brief Get the xsimd architecture name if available.
 */
[[nodiscard]] inline const char* getArchitectureName() {
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
[[nodiscard]] inline std::size_t getSimdWidth() {
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
[[nodiscard]] inline bool isAvailable() {
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
inline void schwarzschildFScalar(
    const double* radii,
    double rS,
    double* out,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        out[i] = 1.0 - (rS / radii[i]);
    }
}

/**
 * @brief Compute Schwarzschild metric component using xsimd explicit vectorization.
 */
inline void schwarzschildFXsimd(
    const double* radii,
    double rS,
    double* out,
    std::size_t count) {

#if BLACKHOLE_ENABLE_XSIMD
    using batch_type = xsimd::batch<double>;
    constexpr std::size_t simdSize = batch_type::size;

    const batch_type one(1.0);
    const batch_type rs(rS);

    // Vectorized loop
    std::size_t i = 0;
    for (; (i + simdSize) <= count; i += simdSize) {
        const batch_type rVec = xsimd::load_unaligned(&radii[i]);
        const batch_type fVec = one - (rs / rVec);
        xsimd::store_unaligned(&out[i], fVec);
    }

    // Scalar tail
    for (; i < count; ++i) {
        out[i] = 1.0 - (rS / radii[i]);
    }
#else
    schwarzschildFScalar(radii, rS, out, count);
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
inline void redshiftBatchScalar(
    const double* radii,
    double rS,
    double* out,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        const double r = radii[i];
        const double f = 1.0 - (rS / r);
        out[i] = (f > 0.0) ? std::sqrt(f) : 0.0;
    }
}

/**
 * @brief Compute Kerr redshift batch using xsimd explicit vectorization.
 */
inline void redshiftBatchXsimd(
    const double* radii,
    double rS,
    double* out,
    std::size_t count) {

#if BLACKHOLE_ENABLE_XSIMD
    using batch_type = xsimd::batch<double>;
    constexpr std::size_t simdSize = batch_type::size;

    const batch_type one(1.0);
    const batch_type zero(0.0);
    const batch_type rs(rS);

    std::size_t i = 0;
    for (; (i + simdSize) <= count; i += simdSize) {
        const batch_type rVec   = xsimd::load_unaligned(&radii[i]);
        const batch_type fVec   = one - (rs / rVec);

        // Conditional: sqrt if f > 0, else 0
        const auto mask         = fVec > zero;
        const batch_type result = xsimd::select(mask, xsimd::sqrt(fVec), zero);

        xsimd::store_unaligned(&out[i], result);
    }

    // Scalar tail
    for (; i < count; ++i) {
        const double r = radii[i];
        const double f = 1.0 - (rS / r);
        out[i] = (f > 0.0) ? std::sqrt(f) : 0.0;
    }
#else
    redshiftBatchScalar(radii, rS, out, count);
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
inline void christoffelAccelScalar(
    const double* rArr,
    const double* drArr,
    const double* dthetaArr,
    const double* dphiArr,
    const double* thetaArr,
    double rS,
    double* accelOut,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        const double rI   = rArr[i];
        const double drI  = drArr[i];
        const double dthI = dthetaArr[i];
        const double dphI = dphiArr[i];
        const double thI  = thetaArr[i];

        const double f        = 1.0 - (rS / rI);
        const double sinTh    = std::sin(thI);

        const double gammaRTt   = (rS * f) / (2.0 * rI * rI);
        const double gammaRRr   = -(rS / (2.0 * rI * rI * f));
        const double gammaRThth = -(rI * f);
        const double gammaRPhph = -(rI * f * sinTh * sinTh);
        const double dtDl       = 1.0 / f;

        accelOut[i] = -(gammaRTt   * dtDl * dtDl)
                      - (gammaRRr   * drI  * drI)
                      - (gammaRThth * dthI * dthI)
                      - (gammaRPhph * dphI * dphI);
    }
}

/**
 * @brief Compute Christoffel-based radial acceleration using xsimd.
 */
inline void christoffelAccelXsimd(
    const double* rArr,
    const double* drArr,
    const double* dthetaArr,
    const double* dphiArr,
    const double* thetaArr,
    double rS,
    double* accelOut,
    std::size_t count) {

#if BLACKHOLE_ENABLE_XSIMD
    using batch_type = xsimd::batch<double>;
    constexpr std::size_t simdSize = batch_type::size;

    const batch_type one(1.0);
    const batch_type two(2.0);
    const batch_type rs(rS);
    const batch_type negRs(-rS);

    std::size_t i = 0;
    for (; i + simdSize <= count; i += simdSize) {
        const batch_type rV   = xsimd::load_unaligned(&rArr[i]);
        const batch_type drV  = xsimd::load_unaligned(&drArr[i]);
        const batch_type dthV = xsimd::load_unaligned(&dthetaArr[i]);
        const batch_type dphV = xsimd::load_unaligned(&dphiArr[i]);
        const batch_type thV  = xsimd::load_unaligned(&thetaArr[i]);

        const batch_type f       = one - (rs / rV);
        const batch_type sinTh   = xsimd::sin(thV);
        const batch_type r2      = rV * rV;

        const batch_type gammaRTt   = (rs * f) / (two * r2);
        const batch_type gammaRRr   = negRs / (two * r2 * f);
        const batch_type gammaRThth = -rV * f;
        const batch_type gammaRPhph = gammaRThth * sinTh * sinTh;
        const batch_type dtDl       = one / f;

        const batch_type accel = -(gammaRTt   * dtDl * dtDl)
                                 - (gammaRRr   * drV  * drV)
                                 - (gammaRThth * dthV * dthV)
                                 - (gammaRPhph * dphV * dphV);

        xsimd::store_unaligned(&accelOut[i], accel);
    }

    // Scalar tail
    for (; i < count; ++i) {
        const double rI   = rArr[i];
        const double drI  = drArr[i];
        const double dthI = dthetaArr[i];
        const double dphI = dphiArr[i];
        const double thI  = thetaArr[i];

        const double f        = 1.0 - (rS / rI);
        const double sinTh    = std::sin(thI);

        const double gammaRTt   = (rS * f) / (2.0 * rI * rI);
        const double gammaRRr   = -(rS / (2.0 * rI * rI * f));
        const double gammaRThth = -(rI * f);
        const double gammaRPhph = -(rI * f * sinTh * sinTh);
        const double dtDl       = 1.0 / f;

        accelOut[i] = -(gammaRTt   * dtDl * dtDl)
                      - (gammaRRr   * drI  * drI)
                      - (gammaRThth * dthI * dthI)
                      - (gammaRPhph * dphI * dphI);
    }
#else
    christoffelAccelScalar(rArr, drArr, dthetaArr, dphiArr, thetaArr, rS, accelOut, count);
#endif
}

// ============================================================================
// Benchmark Harness
// ============================================================================

/**
 * @brief Result of a single benchmark run.
 */
struct BenchResult {
    const char* name     = nullptr;
    double scalarMs      = 0.0;
    double xsimdMs       = 0.0;
    double speedup       = 0.0;
    std::size_t elements = 0;
};

/**
 * @brief Run comparison benchmark for Schwarzschild f computation.
 */
[[nodiscard]] inline BenchResult benchSchwarzschildF(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> outScalar(count);
    std::vector<double> outXsimd(count);

    // Initialize with reasonable radii (3 to 100 r_s)
    const double rS = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii[i] = (3.0 * rS) + (97.0 * rS * static_cast<double>(i) / static_cast<double>(count));
    }

    // Warmup
    schwarzschildFScalar(radii.data(), rS, outScalar.data(), count);
    schwarzschildFXsimd(radii.data(), rS, outXsimd.data(), count);

    // Benchmark scalar
    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschildFScalar(radii.data(), rS, outScalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    const double scalarMs = std::chrono::duration<double, std::milli>(end - start).count();

    // Benchmark xsimd
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschildFXsimd(radii.data(), rS, outXsimd.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    const double xsimdMs = std::chrono::duration<double, std::milli>(end - start).count();

    return {.name = "schwarzschild_f", .scalarMs = scalarMs, .xsimdMs = xsimdMs,
            .speedup = scalarMs / xsimdMs, .elements = count};
}

/**
 * @brief Run comparison benchmark for redshift computation.
 */
[[nodiscard]] inline BenchResult benchRedshift(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> outScalar(count);
    std::vector<double> outXsimd(count);

    const double rS = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii[i] = (3.0 * rS) + (97.0 * rS * static_cast<double>(i) / static_cast<double>(count));
    }

    // Warmup
    redshiftBatchScalar(radii.data(), rS, outScalar.data(), count);
    redshiftBatchXsimd(radii.data(), rS, outXsimd.data(), count);

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshiftBatchScalar(radii.data(), rS, outScalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    const double scalarMs = std::chrono::duration<double, std::milli>(end - start).count();

    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshiftBatchXsimd(radii.data(), rS, outXsimd.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    const double xsimdMs = std::chrono::duration<double, std::milli>(end - start).count();

    return {.name = "redshift_batch", .scalarMs = scalarMs, .xsimdMs = xsimdMs,
            .speedup = scalarMs / xsimdMs, .elements = count};
}

/**
 * @brief Run comparison benchmark for Christoffel acceleration.
 */
[[nodiscard]] inline BenchResult benchChristoffelAccel(std::size_t count, int iterations) {
  std::vector<double> rVec(count);
  std::vector<double> drVec(count);
  std::vector<double> dthetaVec(count);
  std::vector<double> dphiVec(count);
  std::vector<double> thetaVec(count);
  std::vector<double> outScalar(count);
  std::vector<double> outXsimd(count);

  const double rS = 2.0;
  for (std::size_t i = 0; i < count; ++i) {
    const double u = static_cast<double>(i) / static_cast<double>(count);
    rVec[i] = (6.0 * rS) + (50.0 * u * rS);
    drVec[i] = -0.5 + u;
    dthetaVec[i] = 0.1 * u;
    dphiVec[i] = 0.5 + (0.5 * u);
    thetaVec[i] = PI * 0.5;
  }

    // Warmup
    christoffelAccelScalar(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                           thetaVec.data(), rS, outScalar.data(), count);
    christoffelAccelXsimd(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                          thetaVec.data(), rS, outXsimd.data(), count);

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffelAccelScalar(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                               thetaVec.data(), rS, outScalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    const double scalarMs = std::chrono::duration<double, std::milli>(end - start).count();

    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffelAccelXsimd(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                              thetaVec.data(), rS, outXsimd.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    const double xsimdMs = std::chrono::duration<double, std::milli>(end - start).count();

    return {.name = "christoffel_accel", .scalarMs = scalarMs, .xsimdMs = xsimdMs,
            .speedup = scalarMs / xsimdMs, .elements = count};
}

} // namespace physics::xsimd_eval

#endif // PHYSICS_XSIMD_EVAL_H
