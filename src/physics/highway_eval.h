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
#include <chrono>
#include <cmath>
#include <cstddef>
#include <ratio>
#include <vector>

#if BLACKHOLE_ENABLE_HIGHWAY
#include <hwy/highway.h>
#include <hwy/contrib/math/math-inl.h>
#endif

namespace physics::highway_eval {

// ============================================================================
// Architecture Detection
// ============================================================================

/**
 * @brief Get the Highway target name if available.
 */
[[nodiscard]] inline const char* getArchitectureName() {
#if BLACKHOLE_ENABLE_HIGHWAY
    return hwy::TargetName(hwy::SupportedTargets());
#else
    return "disabled";
#endif
}

/**
 * @brief Check if Highway is available.
 */
[[nodiscard]] inline bool isAvailable() {
#if BLACKHOLE_ENABLE_HIGHWAY
    return true;
#else
    return false;
#endif
}

/**
 * @brief Get SIMD vector width for doubles.
 */
[[nodiscard]] inline std::size_t getSimdWidth() {
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
    const char* name{};
    double scalarMs{};
    double highwayMs{};
    double speedup{};
    std::size_t elements{};
};

// ============================================================================
// Scalar Reference Implementations
// ============================================================================

inline void schwarzschildFScalar(
    const double* radii,
    double rS,
    double* out,
    std::size_t count) {

    for (std::size_t i = 0; i < count; ++i) {
        out[i] = 1.0 - (rS / radii[i]);
    }
}

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

        const double f       = 1.0 - (rS / rI);
        const double sinTh   = std::sin(thI);

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

// ============================================================================
// Highway SIMD Implementations
// ============================================================================

#if BLACKHOLE_ENABLE_HIGHWAY

namespace hn = hwy::HWY_NAMESPACE;

inline void schwarzschildFHighway(
    const double* HWY_RESTRICT radii,
    double rS,
    double* HWY_RESTRICT out,
    std::size_t count) {

    const HWY_FULL(double) d;
    const std::size_t laneN = hn::Lanes(d);

    const auto one = hn::Set(d, 1.0);
    const auto rs = hn::Set(d, rS);

    std::size_t i = 0;
    for (; (i + laneN) <= count; i += laneN) {
        const auto rVec = hn::LoadU(d, radii + i);
        const auto fVec = hn::Sub(one, hn::Div(rs, rVec));
        hn::StoreU(fVec, d, out + i);
    }

    // Scalar tail
    for (; i < count; ++i) {
        out[i] = 1.0 - (rS / radii[i]);
    }
}

inline void redshiftBatchHighway(
    const double* HWY_RESTRICT radii,
    double rS,
    double* HWY_RESTRICT out,
    std::size_t count) {

    const HWY_FULL(double) d;
    const std::size_t laneN = hn::Lanes(d);

    const auto one  = hn::Set(d, 1.0);
    const auto zero = hn::Zero(d);
    const auto rs   = hn::Set(d, rS);

    std::size_t i = 0;
    for (; (i + laneN) <= count; i += laneN) {
        const auto rVec   = hn::LoadU(d, radii + i);
        const auto fVec   = hn::Sub(one, hn::Div(rs, rVec));

        // Conditional: sqrt if f > 0, else 0
        const auto mask   = hn::Gt(fVec, zero);
        const auto sqrtF  = hn::Sqrt(fVec);
        const auto result = hn::IfThenElse(mask, sqrtF, zero);

        hn::StoreU(result, d, out + i);
    }

    // Scalar tail
    for (; i < count; ++i) {
        const double r = radii[i];
        const double f = 1.0 - (rS / r);
        out[i] = (f > 0.0) ? std::sqrt(f) : 0.0;
    }
}

inline void christoffelAccelHighway(
    const double* HWY_RESTRICT rArr,
    const double* HWY_RESTRICT drArr,
    const double* HWY_RESTRICT dthetaArr,
    const double* HWY_RESTRICT dphiArr,
    const double* HWY_RESTRICT thetaArr,
    double rS,
    double* HWY_RESTRICT accelOut,
    std::size_t count) {

    const HWY_FULL(double) d;
    const std::size_t laneN = hn::Lanes(d);

    const auto one   = hn::Set(d, 1.0);
    const auto two   = hn::Set(d, 2.0);
    const auto rs    = hn::Set(d, rS);
    const auto negRs = hn::Set(d, -rS);

    std::size_t i = 0;
    for (; (i + laneN) <= count; i += laneN) {
        const auto rV   = hn::LoadU(d, rArr     + i);
        const auto drV  = hn::LoadU(d, drArr    + i);
        const auto dthV = hn::LoadU(d, dthetaArr + i);
        const auto dphV = hn::LoadU(d, dphiArr  + i);
        const auto thV  = hn::LoadU(d, thetaArr + i);

        const auto fVec = hn::Sub(one, hn::Div(rs, rV));

        // Use scalar sin for each lane
        double sinArr[8];  // Max SIMD width we might encounter
        double thArr[8];
        hn::StoreU(thV, d, thArr);
        for (std::size_t j = 0; j < laneN; ++j) {
            sinArr[j] = std::sin(thArr[j]);
        }
        const auto sinTh = hn::LoadU(d, sinArr);

        const auto r2 = hn::Mul(rV, rV);

        // Christoffel symbols
        const auto gammaRTt   = hn::Div(hn::Mul(rs, fVec), hn::Mul(two, r2));
        const auto gammaRRr   = hn::Div(negRs, hn::Mul(hn::Mul(two, r2), fVec));
        const auto gammaRThth = hn::Neg(hn::Mul(rV, fVec));
        const auto gammaRPhph = hn::Mul(gammaRThth, hn::Mul(sinTh, sinTh));
        const auto dtDl       = hn::Div(one, fVec);

        // Acceleration computation
        auto accel = hn::Neg(hn::Mul(gammaRTt, hn::Mul(dtDl, dtDl)));
        accel = hn::Sub(accel, hn::Mul(gammaRRr,   hn::Mul(drV,  drV)));
        accel = hn::Sub(accel, hn::Mul(gammaRThth, hn::Mul(dthV, dthV)));
        accel = hn::Sub(accel, hn::Mul(gammaRPhph, hn::Mul(dphV, dphV)));

        hn::StoreU(accel, d, accelOut + i);
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
}

#endif  // BLACKHOLE_ENABLE_HIGHWAY

// ============================================================================
// Benchmark Harness
// ============================================================================

[[nodiscard]] inline BenchResult benchSchwarzschildF(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> outScalar(count);
    std::vector<double> outHighway(count);

    const double rS = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii.at(i) = (3.0 * rS) + (97.0 * rS * (static_cast<double>(i) / static_cast<double>(count)));
    }

    // Warmup
    schwarzschildFScalar(radii.data(), rS, outScalar.data(), count);
#if BLACKHOLE_ENABLE_HIGHWAY
    schwarzschildFHighway(radii.data(), rS, outHighway.data(), count);
#endif

    // Benchmark scalar
    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschildFScalar(radii.data(), rS, outScalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    const double scalarMs = std::chrono::duration<double, std::milli>(end - start).count();

    // Benchmark Highway
#if BLACKHOLE_ENABLE_HIGHWAY
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        schwarzschildFHighway(radii.data(), rS, outHighway.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    const double highwayMs = std::chrono::duration<double, std::milli>(end - start).count();
#else
    const double highwayMs = scalarMs;
#endif

    return {.name = "schwarzschild_f", .scalarMs = scalarMs, .highwayMs = highwayMs,
            .speedup = scalarMs / highwayMs, .elements = count};
}

[[nodiscard]] inline BenchResult benchRedshift(std::size_t count, int iterations) {
    std::vector<double> radii(count);
    std::vector<double> outScalar(count);
    std::vector<double> outHighway(count);

    const double rS = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        radii.at(i) = (3.0 * rS) + (97.0 * rS * (static_cast<double>(i) / static_cast<double>(count)));
    }

    // Warmup
    redshiftBatchScalar(radii.data(), rS, outScalar.data(), count);
#if BLACKHOLE_ENABLE_HIGHWAY
    redshiftBatchHighway(radii.data(), rS, outHighway.data(), count);
#endif

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshiftBatchScalar(radii.data(), rS, outScalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    const double scalarMs = std::chrono::duration<double, std::milli>(end - start).count();

#if BLACKHOLE_ENABLE_HIGHWAY
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        redshiftBatchHighway(radii.data(), rS, outHighway.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    const double highwayMs = std::chrono::duration<double, std::milli>(end - start).count();
#else
    const double highwayMs = scalarMs;
#endif

    return {.name = "redshift_batch", .scalarMs = scalarMs, .highwayMs = highwayMs,
            .speedup = scalarMs / highwayMs, .elements = count};
}

[[nodiscard]] inline BenchResult benchChristoffelAccel(std::size_t count, int iterations) {
    std::vector<double> rVec(count);
    std::vector<double> drVec(count);
    std::vector<double> dthetaVec(count);
    std::vector<double> dphiVec(count);
    std::vector<double> thetaVec(count);
    std::vector<double> outScalar(count);
    std::vector<double> outHighway(count);

    const double rS = 2.0;
    for (std::size_t i = 0; i < count; ++i) {
        const double u = static_cast<double>(i) / static_cast<double>(count);
        rVec.at(i)     = (6.0 * rS) + (50.0 * u * rS);
        drVec.at(i)    = -0.5 + u;
        dthetaVec.at(i) = 0.1 * u;
        dphiVec.at(i)  = 0.5 + (0.5 * u);
        thetaVec.at(i) = PI * 0.5;
    }

    // Warmup
    christoffelAccelScalar(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                           thetaVec.data(), rS, outScalar.data(), count);
#if BLACKHOLE_ENABLE_HIGHWAY
    christoffelAccelHighway(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                            thetaVec.data(), rS, outHighway.data(), count);
#endif

    auto start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffelAccelScalar(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                               thetaVec.data(), rS, outScalar.data(), count);
    }
    auto end = std::chrono::high_resolution_clock::now();
    const double scalarMs = std::chrono::duration<double, std::milli>(end - start).count();

#if BLACKHOLE_ENABLE_HIGHWAY
    start = std::chrono::high_resolution_clock::now();
    for (int iter = 0; iter < iterations; ++iter) {
        christoffelAccelHighway(rVec.data(), drVec.data(), dthetaVec.data(), dphiVec.data(),
                                thetaVec.data(), rS, outHighway.data(), count);
    }
    end = std::chrono::high_resolution_clock::now();
    const double highwayMs = std::chrono::duration<double, std::milli>(end - start).count();
#else
    const double highwayMs = scalarMs;
#endif

    return {.name = "christoffel_accel", .scalarMs = scalarMs, .highwayMs = highwayMs,
            .speedup = scalarMs / highwayMs, .elements = count};
}

}  // namespace physics::highway_eval

#endif  // PHYSICS_HIGHWAY_EVAL_H
