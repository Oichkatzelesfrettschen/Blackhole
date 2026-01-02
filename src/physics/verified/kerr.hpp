/**
 * @file verified/kerr.hpp
 * @brief Verified Kerr metric functions - derived from Rocq formalization
 *
 * This file is generated from proven Rocq theories in rocq/theories/Metrics/Kerr.v
 * All formulas verified against Bardeen-Press-Teukolsky (1972) analytical results.
 *
 * Metric in Boyer-Lindquist coordinates (c = G = 1, geometric units):
 *   ds^2 = -(1 - 2Mr/Sigma) dt^2
 *        - (4Mra sin^2 theta / Sigma) dt dphi
 *        + (Sigma / Delta) dr^2
 *        + Sigma dtheta^2
 *        + (A sin^2 theta / Sigma) dphi^2
 *
 * where:
 *   Sigma = r^2 + a^2 cos^2 theta
 *   Delta = r^2 - 2Mr + a^2
 *   A = (r^2 + a^2)^2 - a^2 Delta sin^2 theta
 *   a = J/M (spin parameter, |a| <= M for non-naked singularity)
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note All functions are constexpr where possible
 * @note Uses geometric units where c = G = 1
 */

#ifndef PHYSICS_VERIFIED_KERR_HPP
#define PHYSICS_VERIFIED_KERR_HPP

#include <cmath>
#include <concepts>

namespace verified {

// ============================================================================
// Kerr Metric Helper Functions (from Rocq: kerr_Sigma, kerr_Delta, kerr_A)
// ============================================================================

/**
 * @brief Sigma = r^2 + a^2 cos^2(theta)
 *
 * Derived from Rocq: Definition kerr_Sigma (r theta a : R) : R :=
 *   r^2 + a^2 * (cos theta)^2.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter (J/M)
 * @return Sigma
 */
[[nodiscard]] inline double kerr_Sigma(double r, double theta, double a) noexcept {
    const double cos_theta = std::cos(theta);
    return r * r + a * a * cos_theta * cos_theta;
}

/**
 * @brief Delta = r^2 - 2Mr + a^2
 *
 * Derived from Rocq: Definition kerr_Delta (r M a : R) : R :=
 *   r^2 - 2 * M * r + a^2.
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @param a Spin parameter (J/M)
 * @return Delta
 */
[[nodiscard]] constexpr double kerr_Delta(double r, double M, double a) noexcept {
    return r * r - 2.0 * M * r + a * a;
}

/**
 * @brief A = (r^2 + a^2)^2 - a^2 Delta sin^2(theta)
 *
 * Derived from Rocq: Definition kerr_A (r theta M a : R) : R :=
 *   (r^2 + a^2)^2 - a^2 * kerr_Delta r M a * (sin theta)^2.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @return A
 */
[[nodiscard]] inline double kerr_A(double r, double theta, double M, double a) noexcept {
    const double r2_plus_a2 = r * r + a * a;
    const double sin_theta = std::sin(theta);
    const double Delta = kerr_Delta(r, M, a);
    return r2_plus_a2 * r2_plus_a2 - a * a * Delta * sin_theta * sin_theta;
}

// ============================================================================
// Horizon Structure (from Rocq: outer_horizon, inner_horizon)
// ============================================================================

/**
 * @brief Outer (event) horizon: r_+ = M + sqrt(M^2 - a^2)
 *
 * Derived from Rocq: Definition outer_horizon (M a : R) : R :=
 *   M + sqrt (M^2 - a^2).
 *
 * @param M Black hole mass
 * @param a Spin parameter (|a| <= M for horizon to exist)
 * @return r_+ outer horizon radius
 */
[[nodiscard]] inline double outer_horizon(double M, double a) noexcept {
    return M + std::sqrt(M * M - a * a);
}

/**
 * @brief Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2)
 *
 * Derived from Rocq: Definition inner_horizon (M a : R) : R :=
 *   M - sqrt (M^2 - a^2).
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @return r_- inner horizon radius
 */
[[nodiscard]] inline double inner_horizon(double M, double a) noexcept {
    return M - std::sqrt(M * M - a * a);
}

// ============================================================================
// Ergosphere (from Rocq: ergosphere_radius)
// ============================================================================

/**
 * @brief Outer ergosphere boundary: r_ergo = M + sqrt(M^2 - a^2 cos^2 theta)
 *
 * Derived from Rocq: Definition ergosphere_radius (theta M a : R) : R :=
 *   M + sqrt (M^2 - a^2 * (cos theta)^2).
 *
 * The ergosphere always extends beyond the horizon (except at poles).
 *
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @return Ergosphere radius at angle theta
 */
[[nodiscard]] inline double ergosphere_radius(double theta, double M, double a) noexcept {
    const double cos_theta = std::cos(theta);
    return M + std::sqrt(M * M - a * a * cos_theta * cos_theta);
}

// ============================================================================
// Frame Dragging (from Rocq: frame_dragging_omega)
// ============================================================================

/**
 * @brief Frame dragging angular velocity omega = -g_tphi / g_phph
 *
 * Derived from Rocq: Definition frame_dragging_omega (r theta M a : R) : R :=
 *   let Sigma := kerr_Sigma r theta a in
 *   2 * M * r * a / (kerr_A r theta M a).
 *
 * This is the angular velocity at which local inertial frames are dragged.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @return Frame dragging angular velocity
 */
[[nodiscard]] inline double frame_dragging_omega(double r, double theta, double M, double a) noexcept {
    const double A = kerr_A(r, theta, M, a);
    return 2.0 * M * r * a / A;
}

// ============================================================================
// ISCO - Bardeen-Press-Teukolsky Formula (from Rocq: Z1, Z2, kerr_isco_*)
// ============================================================================

/**
 * @brief Z1 helper for ISCO calculation
 *
 * Derived from Rocq: Definition Z1 (M a : R) : R :=
 *   1 + ((1 - a^2 / M^2) ^ (1/3)) *
 *       (((1 + a / M) ^ (1/3)) + ((1 - a / M) ^ (1/3))).
 */
[[nodiscard]] inline double kerr_Z1(double M, double a) noexcept {
    const double a_over_M = a / M;
    const double one_minus_a2_M2 = 1.0 - a_over_M * a_over_M;
    const double cbrt_factor = std::cbrt(one_minus_a2_M2);
    const double cbrt_plus = std::cbrt(1.0 + a_over_M);
    const double cbrt_minus = std::cbrt(1.0 - a_over_M);
    return 1.0 + cbrt_factor * (cbrt_plus + cbrt_minus);
}

/**
 * @brief Z2 helper for ISCO calculation
 *
 * Derived from Rocq: Definition Z2 (M a : R) : R :=
 *   sqrt (3 * a^2 / M^2 + (Z1 M a)^2).
 */
[[nodiscard]] inline double kerr_Z2(double M, double a) noexcept {
    const double a_over_M = a / M;
    const double z1 = kerr_Z1(M, a);
    return std::sqrt(3.0 * a_over_M * a_over_M + z1 * z1);
}

/**
 * @brief Prograde ISCO radius (Bardeen-Press-Teukolsky formula)
 *
 * Derived from Rocq: Definition kerr_isco_prograde (M a : R) : R :=
 *   M * (3 + Z2 M a - sqrt ((3 - Z1 M a) * (3 + Z1 M a + 2 * Z2 M a))).
 *
 * For a = 0: r_ISCO = 6M (Schwarzschild limit, proven in Rocq)
 * For a = M: r_ISCO = M (extremal prograde)
 *
 * @param M Black hole mass
 * @param a Spin parameter (positive for prograde)
 * @return Prograde ISCO radius
 */
[[nodiscard]] inline double kerr_isco_prograde(double M, double a) noexcept {
    const double z1 = kerr_Z1(M, a);
    const double z2 = kerr_Z2(M, a);
    const double sqrt_term = std::sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2));
    return M * (3.0 + z2 - sqrt_term);
}

/**
 * @brief Retrograde ISCO radius (Bardeen-Press-Teukolsky formula)
 *
 * Derived from Rocq: Definition kerr_isco_retrograde (M a : R) : R :=
 *   M * (3 + Z2 M a + sqrt ((3 - Z1 M a) * (3 + Z1 M a + 2 * Z2 M a))).
 *
 * For a = M: r_ISCO = 9M (extremal retrograde)
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @return Retrograde ISCO radius
 */
[[nodiscard]] inline double kerr_isco_retrograde(double M, double a) noexcept {
    const double z1 = kerr_Z1(M, a);
    const double z2 = kerr_Z2(M, a);
    const double sqrt_term = std::sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2));
    return M * (3.0 + z2 + sqrt_term);
}

// ============================================================================
// Photon Orbits (from Rocq: photon_orbit_prograde, photon_orbit_retrograde)
// ============================================================================

/**
 * @brief Prograde photon orbit radius
 *
 * Derived from Rocq: Definition photon_orbit_prograde (M a : R) : R :=
 *   2 * M * (1 + cos ((2/3) * acos (- a / M))).
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @return Prograde photon orbit radius
 */
[[nodiscard]] inline double photon_orbit_prograde(double M, double a) noexcept {
    return 2.0 * M * (1.0 + std::cos((2.0/3.0) * std::acos(-a / M)));
}

/**
 * @brief Retrograde photon orbit radius
 *
 * Derived from Rocq: Definition photon_orbit_retrograde (M a : R) : R :=
 *   2 * M * (1 + cos ((2/3) * acos (a / M))).
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @return Retrograde photon orbit radius
 */
[[nodiscard]] inline double photon_orbit_retrograde(double M, double a) noexcept {
    return 2.0 * M * (1.0 + std::cos((2.0/3.0) * std::acos(a / M)));
}

// ============================================================================
// Metric Components (from Rocq: kerr_metric, kerr_g_*)
// ============================================================================

/**
 * @brief Kerr g_tt component: g_tt = -(1 - 2Mr/Sigma)
 *
 * Derived from Rocq: kerr_metric returns mkMetric(-(1 - 2 * M * r / Sigma)...)
 */
[[nodiscard]] inline double kerr_g_tt(double r, double theta, double M, double a) noexcept {
    const double Sigma = kerr_Sigma(r, theta, a);
    return -(1.0 - 2.0 * M * r / Sigma);
}

/**
 * @brief Kerr g_rr component: g_rr = Sigma / Delta
 *
 * Derived from Rocq: g_rr := Sigma / Delta
 */
[[nodiscard]] inline double kerr_g_rr(double r, double theta, double M, double a) noexcept {
    const double Sigma = kerr_Sigma(r, theta, a);
    const double Delta = kerr_Delta(r, M, a);
    return Sigma / Delta;
}

/**
 * @brief Kerr g_thth component: g_thth = Sigma
 *
 * Derived from Rocq: g_thth := Sigma
 */
[[nodiscard]] inline double kerr_g_thth(double r, double theta, double a) noexcept {
    return kerr_Sigma(r, theta, a);
}

/**
 * @brief Kerr g_phph component: g_phph = A sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_phph := A * sin2 / Sigma
 */
[[nodiscard]] inline double kerr_g_phph(double r, double theta, double M, double a) noexcept {
    const double Sigma = kerr_Sigma(r, theta, a);
    const double A = kerr_A(r, theta, M, a);
    const double sin_theta = std::sin(theta);
    return A * sin_theta * sin_theta / Sigma;
}

/**
 * @brief Kerr g_tph (cross term): g_tph = -2Mar sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_tph := - 2 * M * r * a * sin2 / Sigma
 * This is the frame dragging term.
 */
[[nodiscard]] inline double kerr_g_tph(double r, double theta, double M, double a) noexcept {
    const double Sigma = kerr_Sigma(r, theta, a);
    const double sin_theta = std::sin(theta);
    return -2.0 * M * r * a * sin_theta * sin_theta / Sigma;
}

// ============================================================================
// Christoffel Symbols (from Rocq: kerr_christoffel_*)
// ============================================================================

/**
 * @brief Kerr Gamma^t_{tr}
 *
 * Derived from Rocq: Definition kerr_christoffel_t_tr (r theta M a : R) : R :=
 *   let Sigma := kerr_Sigma r theta a in
 *   let Delta := kerr_Delta r M a in
 *   M * (r^2 - a^2 * (cos theta)^2) / (Sigma^2 * Delta) * (r^2 + a^2).
 */
[[nodiscard]] inline double kerr_christoffel_t_tr(double r, double theta, double M, double a) noexcept {
    const double Sigma = kerr_Sigma(r, theta, a);
    const double Delta = kerr_Delta(r, M, a);
    const double cos_theta = std::cos(theta);
    const double r2_minus_a2cos2 = r * r - a * a * cos_theta * cos_theta;
    const double r2_plus_a2 = r * r + a * a;
    return M * r2_minus_a2cos2 / (Sigma * Sigma * Delta) * r2_plus_a2;
}

/**
 * @brief Kerr Gamma^r_{tt}
 *
 * Derived from Rocq: Definition kerr_christoffel_r_tt (r theta M a : R) : R :=
 *   let Sigma := kerr_Sigma r theta a in
 *   let Delta := kerr_Delta r M a in
 *   M * Delta * (r^2 - a^2 * (cos theta)^2) / Sigma^3.
 */
[[nodiscard]] inline double kerr_christoffel_r_tt(double r, double theta, double M, double a) noexcept {
    const double Sigma = kerr_Sigma(r, theta, a);
    const double Delta = kerr_Delta(r, M, a);
    const double cos_theta = std::cos(theta);
    const double r2_minus_a2cos2 = r * r - a * a * cos_theta * cos_theta;
    const double Sigma3 = Sigma * Sigma * Sigma;
    return M * Delta * r2_minus_a2cos2 / Sigma3;
}

// ============================================================================
// Helper Functions for Validation
// ============================================================================

/**
 * @brief Check if spin parameter is sub-extremal (|a| < M)
 */
[[nodiscard]] constexpr bool is_subextremal(double M, double a) noexcept {
    return std::abs(a) < M;
}

/**
 * @brief Check if point is outside the outer horizon
 */
[[nodiscard]] inline bool outside_outer_horizon(double r, double M, double a) noexcept {
    return r > outer_horizon(M, a);
}

/**
 * @brief Check if point is inside the ergosphere but outside the horizon
 */
[[nodiscard]] inline bool in_ergosphere(double r, double theta, double M, double a) noexcept {
    return r > outer_horizon(M, a) && r < ergosphere_radius(theta, M, a);
}

/**
 * @brief Schwarzschild limit: frame dragging vanishes for a = 0
 *
 * Proven in Rocq: Theorem no_frame_dragging_schwarzschild
 */
[[nodiscard]] constexpr bool has_frame_dragging(double a) noexcept {
    return a != 0.0;
}

} // namespace verified

#endif // PHYSICS_VERIFIED_KERR_HPP
