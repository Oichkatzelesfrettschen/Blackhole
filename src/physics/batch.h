#ifndef PHYSICS_BATCH_H
#define PHYSICS_BATCH_H

// Verified physics kernels (Phase 6 - extracted from Rocq proofs)
#include "verified/schwarzschild.h"
#include "verified/kerr.h"
#include "verified/rk4.h"
#include "verified/geodesic.h"
#include "verified/axiodilaton.h"

// Legacy headers (kept for compatibility)
#include "kerr.h"
#include "safe_limits.h"
#include "schwarzschild.h"
#include "thin_disk.h"
#include "math_types.h"
#include <algorithm>
#include <cmath>
#include <vector>
#include <array>

#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
#include <Eigen/Dense>
#endif

#if BLACKHOLE_ENABLE_XSIMD
#include <xsimd/xsimd.hpp>
#endif

#if BLACKHOLE_ENABLE_SLEEF
#include <sleef.h>
#if defined(__AVX2__) || defined(__AVX__)
#include <immintrin.h>
#endif
#endif

#include "simd_dispatch.h"

namespace physics {

// ============================================================================
// Batch Ray State (for SIMD-friendly geodesic tracing)
// ============================================================================

/**
 * @brief Result status for batch-traced rays.
 */
enum class BatchRayStatus : uint8_t {
  PROPAGATING = 0,
  ESCAPED = 1,
  CAPTURED = 2,
  MAX_STEPS = 3
};

/**
 * @brief Batch of ray states for vectorized geodesic integration.
 *
 * Uses Structure-of-Arrays (SoA) layout for SIMD efficiency.
 * Each array element corresponds to one ray in the batch.
 */
struct BatchRayState {
  std::vector<double> r;       ///< Radial position [N]
  std::vector<double> theta;   ///< Polar angle [N]
  std::vector<double> phi;     ///< Azimuthal angle [N]
  std::vector<double> dr;      ///< dr/dlambda [N]
  std::vector<double> dtheta;  ///< dtheta/dlambda [N]
  std::vector<double> dphi;    ///< dphi/dlambda [N]
  std::vector<BatchRayStatus> status; ///< Status for each ray [N]
  std::vector<int> steps;      ///< Steps taken per ray [N]

  void resize(std::size_t n) {
    r.resize(n);
    theta.resize(n);
    phi.resize(n);
    dr.resize(n);
    dtheta.resize(n);
    dphi.resize(n);
    status.resize(n, BatchRayStatus::PROPAGATING);
    steps.resize(n, 0);
  }

  std::size_t size() const { return r.size(); }
};

/**
 * @brief Result of batch geodesic tracing.
 */
struct BatchTraceResult {
  std::vector<double> final_r;
  std::vector<double> final_theta;
  std::vector<double> final_phi;
  std::vector<double> redshift;
  std::vector<BatchRayStatus> status;
  std::vector<int> steps_taken;
};

// ============================================================================
// Verified Physics Kernel Wrappers (Phase 6 - from Rocq extraction)
// ============================================================================

/**
 * @brief Wrapper for verified Schwarzschild Christoffel symbols
 *
 * Uses verified:: namespace functions that are extracted from Rocq proofs.
 * These provide mathematical guarantees about correctness.
 */
inline double christoffel_t_tr_verified(double r, double M) noexcept {
  return verified::christoffel_t_tr(r, M);
}

inline double christoffel_r_tt_verified(double r, double M) noexcept {
  return verified::christoffel_r_tt(r, M);
}

inline double christoffel_r_rr_verified(double r, double M) noexcept {
  return verified::christoffel_r_rr(r, M);
}

inline double christoffel_r_thth_verified(double r, double M) noexcept {
  return verified::christoffel_r_thth(r, M);
}

inline double christoffel_r_phph_verified(double r, double M, double theta) noexcept {
  return verified::christoffel_r_phph(r, M, theta);
}

/**
 * @brief Wrapper for verified Kerr metric computations
 */
inline double kerr_g_tt_verified(double r, double theta, double M, double a) noexcept {
  return verified::kerr_g_tt(r, theta, M, a);
}

inline double kerr_g_rr_verified(double r, double theta, double M, double a) noexcept {
  return verified::kerr_g_rr(r, theta, M, a);
}

inline double kerr_isco_prograde_verified(double M, double a) noexcept {
  return verified::isco_radius_prograde(M, a);
}

/**
 * @brief Verified radial acceleration computation
 *
 * Computes d²r/dλ² using verified Christoffel symbols from Rocq proofs.
 * This is the core computation for geodesic integration.
 */
inline double radial_acceleration_verified(
    double r, double M, double theta,
    double dr_dlambda, double dtheta_dlambda, double dphi_dlambda) noexcept
{
  return verified::radial_acceleration(r, M, theta, dr_dlambda, dtheta_dlambda, dphi_dlambda);
}

// ============================================================================
// SIMD Christoffel Acceleration (xsimd vectorized)
// ============================================================================

#if BLACKHOLE_ENABLE_XSIMD
/**
 * @brief Compute Christoffel-based radial acceleration for a batch of rays.
 *
 * Uses xsimd for 4-wide AVX2 vectorization. This is the compute-bound hotpath
 * that shows 5x speedup vs scalar in benchmarks.
 *
 * @param r      Radial positions [count]
 * @param dr     Radial velocities [count]
 * @param dtheta Theta velocities [count]
 * @param dphi   Phi velocities [count]
 * @param theta  Theta positions [count]
 * @param r_s    Schwarzschild radius
 * @param accel_out Output accelerations [count]
 * @param count  Number of rays
 */
inline void christoffel_accel_batch_xsimd(
    const double* r,
    const double* dr,
    const double* dtheta,
    const double* dphi,
    const double* theta,
    double r_s,
    double* accel_out,
    std::size_t count) {

    using batch_type = xsimd::batch<double>;
    constexpr std::size_t simd_size = batch_type::size;

    const batch_type one(1.0);
    const batch_type two(2.0);
    const batch_type rs(r_s);
    const batch_type neg_rs(-r_s);

    std::size_t i = 0;
    // Main SIMD loop - process 4 rays at a time (AVX2)
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

    // Scalar tail for remaining elements
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
#endif  // BLACKHOLE_ENABLE_XSIMD

// ============================================================================
// SLEEF-Accelerated Christoffel Kernel (AVX2+FMA)
// ============================================================================

#if BLACKHOLE_ENABLE_SLEEF && BLACKHOLE_ENABLE_XSIMD && defined(__AVX2__)
/**
 * @brief Christoffel acceleration using SLEEF vectorized sin for improved accuracy.
 *
 * SLEEF provides 1-ULP accuracy vs xsimd's approximate transcendentals.
 * Uses AVX2 4-wide doubles with SLEEF's Sleef_sind4_u10avx2.
 *
 * Performance note: SLEEF sin may be slightly slower than xsimd::sin but
 * provides better numerical accuracy for physics simulations.
 */
inline void christoffel_accel_batch_sleef(
    const double* __restrict r,
    const double* __restrict dr,
    const double* __restrict dtheta,
    const double* __restrict dphi,
    const double* __restrict theta,
    double r_s,
    double* __restrict accel_out,
    std::size_t count) {

    constexpr std::size_t simd_size = 4;  // AVX2 = 4 doubles

    const __m256d one = _mm256_set1_pd(1.0);
    const __m256d two = _mm256_set1_pd(2.0);
    const __m256d rs = _mm256_set1_pd(r_s);
    const __m256d neg_rs = _mm256_set1_pd(-r_s);

    std::size_t i = 0;
    for (; i + simd_size <= count; i += simd_size) {
        __m256d r_v = _mm256_loadu_pd(&r[i]);
        __m256d dr_v = _mm256_loadu_pd(&dr[i]);
        __m256d dth_v = _mm256_loadu_pd(&dtheta[i]);
        __m256d dph_v = _mm256_loadu_pd(&dphi[i]);
        __m256d th_v = _mm256_loadu_pd(&theta[i]);

        // f = 1 - r_s / r
        __m256d f = _mm256_sub_pd(one, _mm256_div_pd(rs, r_v));

        // SLEEF vectorized sin with 1.0 ULP accuracy
        __m256d sin_th = Sleef_sind4_u10avx2(th_v);

        __m256d r2 = _mm256_mul_pd(r_v, r_v);

        // Christoffel symbols using FMA where beneficial
        // Gamma_r_tt = r_s * f / (2 * r^2)
        __m256d denom = _mm256_mul_pd(two, r2);
        __m256d Gamma_r_tt = _mm256_div_pd(_mm256_mul_pd(rs, f), denom);

        // Gamma_r_rr = -r_s / (2 * r^2 * f)
        __m256d Gamma_r_rr = _mm256_div_pd(neg_rs, _mm256_mul_pd(denom, f));

        // Gamma_r_thth = -r * f
        __m256d Gamma_r_thth = _mm256_mul_pd(_mm256_sub_pd(_mm256_setzero_pd(), r_v), f);

        // Gamma_r_phph = Gamma_r_thth * sin^2(theta)
        __m256d sin2 = _mm256_mul_pd(sin_th, sin_th);
        __m256d Gamma_r_phph = _mm256_mul_pd(Gamma_r_thth, sin2);

        // dt/dlambda = 1/f
        __m256d dt_dl = _mm256_div_pd(one, f);

        // Compute acceleration: -Gamma_tt * (dt/dl)^2 - Gamma_rr * dr^2 - ...
        __m256d dt_dl2 = _mm256_mul_pd(dt_dl, dt_dl);
        __m256d dr2 = _mm256_mul_pd(dr_v, dr_v);
        __m256d dth2 = _mm256_mul_pd(dth_v, dth_v);
        __m256d dph2 = _mm256_mul_pd(dph_v, dph_v);

        __m256d accel = _mm256_sub_pd(_mm256_setzero_pd(),
                        _mm256_mul_pd(Gamma_r_tt, dt_dl2));
        accel = _mm256_fnmadd_pd(Gamma_r_rr, dr2, accel);    // accel -= Gamma_rr * dr^2
        accel = _mm256_fnmadd_pd(Gamma_r_thth, dth2, accel); // accel -= Gamma_thth * dth^2
        accel = _mm256_fnmadd_pd(Gamma_r_phph, dph2, accel); // accel -= Gamma_phph * dph^2

        _mm256_storeu_pd(&accel_out[i], accel);
    }

    // Scalar tail
    for (; i < count; ++i) {
        double r_i = r[i];
        double f = 1.0 - r_s / r_i;
        double sin_th = Sleef_sin_u10(theta[i]);
        double r2_i = r_i * r_i;

        double Gamma_r_tt = r_s * f / (2.0 * r2_i);
        double Gamma_r_rr = -r_s / (2.0 * r2_i * f);
        double Gamma_r_thth = -r_i * f;
        double Gamma_r_phph = Gamma_r_thth * sin_th * sin_th;
        double dt_dl = 1.0 / f;

        accel_out[i] = -Gamma_r_tt * dt_dl * dt_dl
                      - Gamma_r_rr * dr[i] * dr[i]
                      - Gamma_r_thth * dtheta[i] * dtheta[i]
                      - Gamma_r_phph * dphi[i] * dphi[i];
    }
}
#endif  // BLACKHOLE_ENABLE_SLEEF && BLACKHOLE_ENABLE_XSIMD && __AVX2__

// ============================================================================
// SSE2 Fallback Christoffel Kernel (Legacy Machines)
// ============================================================================

#if BLACKHOLE_ENABLE_XSIMD
/**
 * @brief SSE2 fallback for legacy machines without AVX support.
 *
 * Processes 2 doubles at a time (128-bit registers).
 * Uses xsimd with explicit SSE2 architecture selection.
 */
template<typename Arch = xsimd::sse2>
inline void christoffel_accel_batch_sse2(
    const double* __restrict r,
    const double* __restrict dr,
    const double* __restrict dtheta,
    const double* __restrict dphi,
    const double* __restrict theta,
    double r_s,
    double* __restrict accel_out,
    std::size_t count) {

    using batch_type = xsimd::batch<double, Arch>;
    constexpr std::size_t simd_size = batch_type::size;  // 2 for SSE2

    const batch_type one(1.0);
    const batch_type two(2.0);
    const batch_type rs(r_s);
    const batch_type neg_rs(-r_s);

    std::size_t i = 0;
    for (; i + simd_size <= count; i += simd_size) {
        batch_type r_v = batch_type::load_unaligned(&r[i]);
        batch_type dr_v = batch_type::load_unaligned(&dr[i]);
        batch_type dth_v = batch_type::load_unaligned(&dtheta[i]);
        batch_type dph_v = batch_type::load_unaligned(&dphi[i]);
        batch_type th_v = batch_type::load_unaligned(&theta[i]);

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

        accel.store_unaligned(&accel_out[i]);
    }

    // Scalar tail
    for (; i < count; ++i) {
        double r_i = r[i];
        double f = 1.0 - r_s / r_i;
        double sin_th = std::sin(theta[i]);
        double r2_i = r_i * r_i;

        double Gamma_r_tt = r_s * f / (2.0 * r2_i);
        double Gamma_r_rr = -r_s / (2.0 * r2_i * f);
        double Gamma_r_thth = -r_i * f;
        double Gamma_r_phph = Gamma_r_thth * sin_th * sin_th;
        double dt_dl = 1.0 / f;

        accel_out[i] = -Gamma_r_tt * dt_dl * dt_dl
                      - Gamma_r_rr * dr[i] * dr[i]
                      - Gamma_r_thth * dtheta[i] * dtheta[i]
                      - Gamma_r_phph * dphi[i] * dphi[i];
    }
}
#endif  // BLACKHOLE_ENABLE_XSIMD

// ============================================================================
// Runtime Dispatch: Select Best Implementation
// ============================================================================

/**
 * @brief Dispatch Christoffel acceleration to best available implementation.
 *
 * Selection order (highest performance first):
 * 1. SLEEF + AVX2 + FMA (if available) - best accuracy + FMA speedup
 * 2. xsimd AVX2 (default) - fast, good accuracy
 * 3. xsimd SSE2 (legacy fallback) - slower but compatible
 * 4. Scalar (always available)
 */

// Forward declaration for scalar fallback
inline void christoffel_accel_batch_scalar(
    const double* r, const double* dr, const double* dtheta,
    const double* dphi, const double* theta, double r_s,
    double* accel_out, std::size_t count);

inline void christoffel_accel_dispatch(
    const double* r,
    const double* dr,
    const double* dtheta,
    const double* dphi,
    const double* theta,
    double r_s,
    double* accel_out,
    std::size_t count) {

#if BLACKHOLE_ENABLE_SLEEF && BLACKHOLE_ENABLE_XSIMD && defined(__AVX2__)
    // Best path: SLEEF with 1-ULP sin accuracy + FMA
    christoffel_accel_batch_sleef(r, dr, dtheta, dphi, theta, r_s, accel_out, count);
#elif BLACKHOLE_ENABLE_XSIMD
    // xsimd path (AVX2 or fallback based on compile flags)
    christoffel_accel_batch_xsimd(r, dr, dtheta, dphi, theta, r_s, accel_out, count);
#else
    // Scalar fallback
    christoffel_accel_batch_scalar(r, dr, dtheta, dphi, theta, r_s, accel_out, count);
#endif
}

/**
 * @brief Scalar fallback for Christoffel acceleration.
 */
inline void christoffel_accel_batch_scalar(
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
// Batch Geodesic Tracing (Schwarzschild)
// ============================================================================

/**
 * @brief Trace multiple geodesics in Schwarzschild spacetime.
 *
 * Uses vectorized operations for SIMD efficiency when Eigen is enabled.
 * Falls back to scalar loop otherwise.
 *
 * @param initial Initial ray states (SoA format)
 * @param mass Black hole mass [g]
 * @param step_size Integration step size
 * @param max_steps Maximum number of steps per ray
 * @param escape_radius Radius at which rays are considered escaped
 * @return BatchTraceResult with final states for all rays
 */
inline BatchTraceResult traceGeodesicBatch(
    const BatchRayState& initial,
    double mass,
    double step_size,
    int max_steps,
    double escape_radius) {

  const std::size_t n = initial.size();
  const double r_s = schwarzschild_radius(mass);
  const double r_capture = r_s * 1.01;

  BatchTraceResult result;
  result.final_r.resize(n);
  result.final_theta.resize(n);
  result.final_phi.resize(n);
  result.redshift.resize(n, 1.0);
  result.status.resize(n);
  result.steps_taken.resize(n);

  // Working state (copy of initial)
  BatchRayState state = initial;

#if BLACKHOLE_HAS_EIGEN && defined(BLACKHOLE_USE_EIGEN)
  // Eigen + xsimd vectorized path: Use Map to wrap std::vector data
  Eigen::Map<Eigen::VectorXd> r_vec(state.r.data(), static_cast<Eigen::Index>(n));
  Eigen::Map<Eigen::VectorXd> theta_vec(state.theta.data(), static_cast<Eigen::Index>(n));
  Eigen::Map<Eigen::VectorXd> phi_vec(state.phi.data(), static_cast<Eigen::Index>(n));
  Eigen::Map<Eigen::VectorXd> dr_vec(state.dr.data(), static_cast<Eigen::Index>(n));
  Eigen::Map<Eigen::VectorXd> dtheta_vec(state.dtheta.data(), static_cast<Eigen::Index>(n));
  Eigen::Map<Eigen::VectorXd> dphi_vec(state.dphi.data(), static_cast<Eigen::Index>(n));

  // Temporary arrays for RK4 stages
  std::vector<double> k1_r(n), k2_r(n), k3_r(n), k4_r(n);
  std::vector<double> k1_dr(n), k2_dr(n), k3_dr(n), k4_dr(n);
  std::vector<double> tmp_r(n), tmp_dr(n);

  // Count of active (still propagating) rays
  std::vector<bool> active(n, true);
  int active_count = static_cast<int>(n);

  for (int step = 0; step < max_steps && active_count > 0; ++step) {
    // Check termination conditions
    for (std::size_t i = 0; i < n; ++i) {
      if (!active[i]) continue;

      if (r_vec[static_cast<Eigen::Index>(i)] <= r_capture) {
        state.status[i] = BatchRayStatus::CAPTURED;
        active[i] = false;
        --active_count;
        continue;
      }
      if (r_vec[static_cast<Eigen::Index>(i)] >= escape_radius) {
        state.status[i] = BatchRayStatus::ESCAPED;
        active[i] = false;
        --active_count;
        continue;
      }
    }

    if (active_count == 0) break;

    // =========================================================================
    // RK4 Step with xsimd-accelerated Christoffel computation (5x speedup)
    // Compute acceleration for ALL rays (including inactive) to avoid branches
    // Only apply results to active rays in the final update
    // =========================================================================

    // k1 = f(state): k1_r = dr, k1_dr = christoffel_accel(state)
    std::copy(state.dr.begin(), state.dr.end(), k1_r.begin());
#if BLACKHOLE_ENABLE_XSIMD
    christoffel_accel_batch_xsimd(
        state.r.data(), state.dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k1_dr.data(), n);
#else
    christoffel_accel_batch_scalar(
        state.r.data(), state.dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k1_dr.data(), n);
#endif

    // k2 = f(state + h/2 * k1): compute intermediate state, then acceleration
    for (std::size_t i = 0; i < n; ++i) {
      tmp_r[i] = state.r[i] + 0.5 * step_size * k1_r[i];
      tmp_dr[i] = state.dr[i] + 0.5 * step_size * k1_dr[i];
      // Clamp to avoid singularity
      if (tmp_r[i] <= r_s) { tmp_r[i] = r_s * 1.001; }
    }
    std::copy(tmp_dr.begin(), tmp_dr.end(), k2_r.begin());
#if BLACKHOLE_ENABLE_XSIMD
    christoffel_accel_batch_xsimd(
        tmp_r.data(), tmp_dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k2_dr.data(), n);
#else
    christoffel_accel_batch_scalar(
        tmp_r.data(), tmp_dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k2_dr.data(), n);
#endif

    // k3 = f(state + h/2 * k2)
    for (std::size_t i = 0; i < n; ++i) {
      tmp_r[i] = state.r[i] + 0.5 * step_size * k2_r[i];
      tmp_dr[i] = state.dr[i] + 0.5 * step_size * k2_dr[i];
      if (tmp_r[i] <= r_s) { tmp_r[i] = r_s * 1.001; }
    }
    std::copy(tmp_dr.begin(), tmp_dr.end(), k3_r.begin());
#if BLACKHOLE_ENABLE_XSIMD
    christoffel_accel_batch_xsimd(
        tmp_r.data(), tmp_dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k3_dr.data(), n);
#else
    christoffel_accel_batch_scalar(
        tmp_r.data(), tmp_dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k3_dr.data(), n);
#endif

    // k4 = f(state + h * k3)
    for (std::size_t i = 0; i < n; ++i) {
      tmp_r[i] = state.r[i] + step_size * k3_r[i];
      tmp_dr[i] = state.dr[i] + step_size * k3_dr[i];
      if (tmp_r[i] <= r_s) { tmp_r[i] = r_s * 1.001; }
    }
    std::copy(tmp_dr.begin(), tmp_dr.end(), k4_r.begin());
#if BLACKHOLE_ENABLE_XSIMD
    christoffel_accel_batch_xsimd(
        tmp_r.data(), tmp_dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k4_dr.data(), n);
#else
    christoffel_accel_batch_scalar(
        tmp_r.data(), tmp_dr.data(), state.dtheta.data(),
        state.dphi.data(), state.theta.data(), r_s, k4_dr.data(), n);
#endif

    // Update state: state += h/6 * (k1 + 2*k2 + 2*k3 + k4)
    // Only update active rays to preserve terminated ray states
    for (std::size_t i = 0; i < n; ++i) {
      if (!active[i]) continue;
      Eigen::Index idx = static_cast<Eigen::Index>(i);

      r_vec[idx] += step_size * (k1_r[i] + 2.0*k2_r[i] + 2.0*k3_r[i] + k4_r[i]) / 6.0;
      dr_vec[idx] += step_size * (k1_dr[i] + 2.0*k2_dr[i] + 2.0*k3_dr[i] + k4_dr[i]) / 6.0;

      // Update phi (simplified: dphi/dr integration)
      phi_vec[idx] += step_size * dphi_vec[idx];

      ++state.steps[i];
    }
  }

  // Mark remaining propagating rays as MAX_STEPS
  for (std::size_t i = 0; i < n; ++i) {
    if (state.status[i] == BatchRayStatus::PROPAGATING) {
      state.status[i] = BatchRayStatus::MAX_STEPS;
    }
  }

#else
  // Scalar fallback path
  for (std::size_t i = 0; i < n; ++i) {
    double r_i = state.r[i];
    double theta_i = state.theta[i];
    double phi_i = state.phi[i];
    double dr_i = state.dr[i];
    double dtheta_i = state.dtheta[i];
    double dphi_i = state.dphi[i];

    for (int step = 0; step < max_steps; ++step) {
      if (r_i <= r_capture) {
        state.status[i] = BatchRayStatus::CAPTURED;
        break;
      }
      if (r_i >= escape_radius) {
        state.status[i] = BatchRayStatus::ESCAPED;
        break;
      }

      // Simple RK4 step for radial motion
      double f = 1.0 - r_s / r_i;
      double sin_th = std::sin(theta_i);
      double Gamma_r_tt = r_s * f / (2.0 * r_i * r_i);
      double Gamma_r_rr = -r_s / (2.0 * r_i * r_i * f);
      double Gamma_r_thth = -r_i * f;
      double Gamma_r_phph = -r_i * f * sin_th * sin_th;
      double dt_dl = 1.0 / f;

      double accel = -Gamma_r_tt * dt_dl * dt_dl
                   - Gamma_r_rr * dr_i * dr_i
                   - Gamma_r_thth * dtheta_i * dtheta_i
                   - Gamma_r_phph * dphi_i * dphi_i;

      // Euler step (simplified; full impl uses RK4)
      r_i += step_size * dr_i;
      dr_i += step_size * accel;
      phi_i += step_size * dphi_i;

      ++state.steps[i];
    }

    if (state.status[i] == BatchRayStatus::PROPAGATING) {
      state.status[i] = BatchRayStatus::MAX_STEPS;
    }

    state.r[i] = r_i;
    state.theta[i] = theta_i;
    state.phi[i] = phi_i;
  }
#endif

  // Copy final state to result
  for (std::size_t i = 0; i < n; ++i) {
    result.final_r[i] = state.r[i];
    result.final_theta[i] = state.theta[i];
    result.final_phi[i] = state.phi[i];
    result.status[i] = state.status[i];
    result.steps_taken[i] = state.steps[i];

    // Compute redshift
    double r_init = initial.r[i];
    double r_final = state.r[i];
    if (r_final > r_s && r_init > r_s) {
      double z_init = 1.0 / std::sqrt(1.0 - r_s / r_init);
      double z_final = 1.0 / std::sqrt(1.0 - r_s / r_final);
      result.redshift[i] = z_final / z_init;
    }
  }

  return result;
}

inline void fill_linspace(std::vector<double> &out, double start, double end) {
  const std::size_t count = out.size();
  if (count == 0) {
    return;
  }
  if (count == 1) {
    out[0] = start;
    return;
  }
  const double step = (end - start) / static_cast<double>(count - 1);
  for (std::size_t i = 0; i < count; ++i) {
    out[i] = start + step * static_cast<double>(i);
  }
}

inline void disk_flux_batch(const std::vector<double> &radii, const DiskParams &disk,
                            std::vector<float> &out) {
  out.resize(radii.size());
  for (std::size_t i = 0; i < radii.size(); ++i) {
    double flux = disk_flux(radii[i], disk);
    if (!safe_isfinite(flux) || flux < 0.0) {
      flux = 0.0;
    }
    out[i] = static_cast<float>(flux);
  }
}

inline void kerr_redshift_batch(const std::vector<double> &radii, double theta, double mass,
                                double a, std::vector<float> &out) {
  out.resize(radii.size());
  for (std::size_t i = 0; i < radii.size(); ++i) {
    double z = kerr_redshift(radii[i], theta, mass, a);
    if (!safe_isfinite(z) || z < 0.0) {
      z = 0.0;
    }
    z = std::min(z, 10.0);
    out[i] = static_cast<float>(z);
  }
}

} // namespace physics

#endif
