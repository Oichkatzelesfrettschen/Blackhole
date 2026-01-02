/**
 * @file verified/schwarzschild.hpp
 * @brief Verified Schwarzschild metric functions - derived from Rocq formalization
 *
 * This file is generated from proven Rocq theories in rocq/theories/Metrics/Schwarzschild.v
 * All formulas verified against theoretical values:
 *   - r_s = 2M (Schwarzschild radius)
 *   - r_ISCO = 6M (ISCO in geometric units)
 *   - r_ph = 3M (photon sphere = 1.5 r_s)
 *
 * Metric in Boyer-Lindquist coordinates (c = G = 1, geometric units):
 *   ds^2 = -(1 - 2M/r) dt^2 + (1 - 2M/r)^(-1) dr^2 + r^2 dOmega^2
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note All functions are constexpr for compile-time evaluation
 * @note Uses geometric units where c = G = 1
 */

#ifndef PHYSICS_VERIFIED_SCHWARZSCHILD_HPP
#define PHYSICS_VERIFIED_SCHWARZSCHILD_HPP

#include <cmath>
#include <concepts>

namespace verified {

// ============================================================================
// Core Schwarzschild Functions (from Rocq: Prelim.v, Schwarzschild.v)
// ============================================================================

/**
 * @brief Schwarzschild radius: r_s = 2M (geometric units)
 *
 * Derived from Rocq: Definition schwarzschild_radius (M : R) : R := 2 * M.
 *
 * @param M Black hole mass in geometric units
 * @return r_s = 2M
 */
[[nodiscard]] constexpr double schwarzschild_radius(double M) noexcept {
    return 2.0 * M;
}

/**
 * @brief ISCO radius: r_ISCO = 6M = 3 r_s (geometric units)
 *
 * Derived from Rocq: Definition schwarzschild_isco (M : R) : R := 6 * M.
 * Theorem schwarzschild_isco_radius: r_isco = 6 * M.
 *
 * @param M Black hole mass in geometric units
 * @return r_ISCO = 6M
 */
[[nodiscard]] constexpr double schwarzschild_isco(double M) noexcept {
    return 6.0 * M;
}

/**
 * @brief Photon sphere radius: r_ph = 3M = 1.5 r_s
 *
 * Derived from Rocq: Definition photon_sphere_radius (M : R) : R := 3 * M / 2 * 2 = 3M.
 * Unstable circular photon orbits exist at r = 3M.
 *
 * @param M Black hole mass in geometric units
 * @return r_ph = 3M
 */
[[nodiscard]] constexpr double photon_sphere_radius(double M) noexcept {
    return 3.0 * M;
}

// ============================================================================
// Metric Factor (from Rocq: f_schwarzschild)
// ============================================================================

/**
 * @brief Metric factor f(r) = 1 - 2M/r = 1 - r_s/r
 *
 * Derived from Rocq: Definition f_schwarzschild (r M : R) : R := 1 - (2 * M) / r.
 *
 * @param r Radial coordinate (geometric units)
 * @param M Black hole mass (geometric units)
 * @return f = 1 - 2M/r
 */
[[nodiscard]] constexpr double f_schwarzschild(double r, double M) noexcept {
    return 1.0 - (2.0 * M) / r;
}

// ============================================================================
// Metric Components (from Rocq: schwarzschild_metric)
// ============================================================================

/**
 * @brief Schwarzschild g_tt component: g_tt = -(1 - 2M/r)
 *
 * Derived from Rocq: schwarzschild_metric returns mkMetric(- f)... for g_tt
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @return g_tt = -(1 - 2M/r)
 */
[[nodiscard]] constexpr double schwarzschild_g_tt(double r, double M) noexcept {
    return -f_schwarzschild(r, M);
}

/**
 * @brief Schwarzschild g_rr component: g_rr = 1/(1 - 2M/r)
 *
 * Derived from Rocq: schwarzschild_metric returns mkMetric(..., 1/f, ...) for g_rr
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @return g_rr = 1/(1 - 2M/r)
 */
[[nodiscard]] constexpr double schwarzschild_g_rr(double r, double M) noexcept {
    return 1.0 / f_schwarzschild(r, M);
}

/**
 * @brief Schwarzschild g_thth component: g_thth = r^2
 *
 * Derived from Rocq: g_thth := r^2
 *
 * @param r Radial coordinate
 * @return g_thth = r^2
 */
[[nodiscard]] constexpr double schwarzschild_g_thth(double r) noexcept {
    return r * r;
}

/**
 * @brief Schwarzschild g_phph component: g_phph = r^2 sin^2(theta)
 *
 * Derived from Rocq: g_phph := r^2 * (sin theta)^2
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @return g_phph = r^2 sin^2(theta)
 */
[[nodiscard]] inline double schwarzschild_g_phph(double r, double theta) noexcept {
    const double sin_theta = std::sin(theta);
    return r * r * sin_theta * sin_theta;
}

// ============================================================================
// Christoffel Symbols (from Rocq: christoffel_* definitions)
// ============================================================================

/**
 * @brief Gamma^t_{tr} = Gamma^t_{rt} = M / (r(r - 2M))
 *
 * Derived from Rocq: Definition christoffel_t_tr (r M : R) : R :=
 *   M / (r * (r - 2 * M)).
 */
[[nodiscard]] constexpr double christoffel_t_tr(double r, double M) noexcept {
    return M / (r * (r - 2.0 * M));
}

/**
 * @brief Gamma^r_{tt} = M(r - 2M) / r^3
 *
 * Derived from Rocq: Definition christoffel_r_tt (r M : R) : R :=
 *   M * (r - 2 * M) / r^3.
 */
[[nodiscard]] constexpr double christoffel_r_tt(double r, double M) noexcept {
    const double r3 = r * r * r;
    return M * (r - 2.0 * M) / r3;
}

/**
 * @brief Gamma^r_{rr} = -M / (r(r - 2M))
 *
 * Derived from Rocq: Definition christoffel_r_rr (r M : R) : R :=
 *   - M / (r * (r - 2 * M)).
 */
[[nodiscard]] constexpr double christoffel_r_rr(double r, double M) noexcept {
    return -M / (r * (r - 2.0 * M));
}

/**
 * @brief Gamma^r_{thth} = -(r - 2M)
 *
 * Derived from Rocq: Definition christoffel_r_thth (r M : R) : R := -(r - 2 * M).
 */
[[nodiscard]] constexpr double christoffel_r_thth(double r, double M) noexcept {
    return -(r - 2.0 * M);
}

/**
 * @brief Gamma^r_{phph} = -(r - 2M) sin^2(theta)
 *
 * Derived from Rocq: Definition christoffel_r_phph (r theta M : R) : R :=
 *   -(r - 2 * M) * (sin theta)^2.
 */
[[nodiscard]] inline double christoffel_r_phph(double r, double theta, double M) noexcept {
    const double sin_theta = std::sin(theta);
    return -(r - 2.0 * M) * sin_theta * sin_theta;
}

/**
 * @brief Gamma^th_{r th} = Gamma^th_{th r} = 1/r
 *
 * Derived from Rocq: Definition christoffel_th_rth (r : R) : R := 1 / r.
 */
[[nodiscard]] constexpr double christoffel_th_rth(double r) noexcept {
    return 1.0 / r;
}

/**
 * @brief Gamma^th_{phph} = -sin(theta)cos(theta)
 *
 * Derived from Rocq: Definition christoffel_th_phph (theta : R) : R :=
 *   - sin theta * cos theta.
 */
[[nodiscard]] inline double christoffel_th_phph(double theta) noexcept {
    return -std::sin(theta) * std::cos(theta);
}

/**
 * @brief Gamma^ph_{r ph} = Gamma^ph_{ph r} = 1/r
 *
 * Derived from Rocq: Definition christoffel_ph_rph (r : R) : R := 1 / r.
 */
[[nodiscard]] constexpr double christoffel_ph_rph(double r) noexcept {
    return 1.0 / r;
}

/**
 * @brief Gamma^ph_{th ph} = Gamma^ph_{ph th} = cot(theta)
 *
 * Derived from Rocq: Definition christoffel_ph_thph (theta : R) : R :=
 *   cos theta / sin theta.
 */
[[nodiscard]] inline double christoffel_ph_thph(double theta) noexcept {
    return std::cos(theta) / std::sin(theta);
}

// ============================================================================
// Geodesic Acceleration (from Rocq: radial_acceleration)
// ============================================================================

/**
 * @brief Radial acceleration for a test particle in Schwarzschild spacetime
 *
 * Derived from Rocq: Definition radial_acceleration (r dr dtheta dphi theta M : R) : R :=
 *   - christoffel_r_tt r M * 1
 *   - christoffel_r_rr r M * dr * dr
 *   - christoffel_r_thth r M * dtheta * dtheta
 *   - christoffel_r_phph r theta M * dphi * dphi.
 *
 * @param r Radial coordinate
 * @param dr dr/dlambda
 * @param dtheta dtheta/dlambda
 * @param dphi dphi/dlambda
 * @param theta Polar angle
 * @param M Black hole mass
 * @return Radial acceleration d^2r/dlambda^2
 */
[[nodiscard]] inline double radial_acceleration(
    double r, double dr, double dtheta, double dphi,
    double theta, double M) noexcept
{
    // Note: dt/dlambda is normalized to 1 in the original definition
    return -christoffel_r_tt(r, M)
           - christoffel_r_rr(r, M) * dr * dr
           - christoffel_r_thth(r, M) * dtheta * dtheta
           - christoffel_r_phph(r, theta, M) * dphi * dphi;
}

// ============================================================================
// Curvature Invariants (from Rocq: kretschmann_schwarzschild)
// ============================================================================

/**
 * @brief Kretschmann scalar K = R_abcd R^abcd = 48 M^2 / r^6
 *
 * Derived from Rocq: Definition kretschmann_schwarzschild (r M : R) : R :=
 *   48 * M^2 / r^6.
 *
 * This is a curvature invariant that diverges at r = 0 (true singularity).
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @return Kretschmann scalar
 */
[[nodiscard]] constexpr double kretschmann_schwarzschild(double r, double M) noexcept {
    const double r6 = r * r * r * r * r * r;
    return 48.0 * M * M / r6;
}

// ============================================================================
// Helper Functions for Validation
// ============================================================================

/**
 * @brief Check if point is outside the event horizon
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @return true if r > 2M (outside horizon)
 */
[[nodiscard]] constexpr bool outside_horizon(double r, double M) noexcept {
    return r > schwarzschild_radius(M);
}

/**
 * @brief Check if point is outside the photon sphere
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @return true if r > 3M (outside photon sphere)
 */
[[nodiscard]] constexpr bool outside_photon_sphere(double r, double M) noexcept {
    return r > photon_sphere_radius(M);
}

/**
 * @brief Check if point is outside the ISCO
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @return true if r > 6M (outside ISCO)
 */
[[nodiscard]] constexpr bool outside_isco(double r, double M) noexcept {
    return r > schwarzschild_isco(M);
}

} // namespace verified

#endif // PHYSICS_VERIFIED_SCHWARZSCHILD_HPP
