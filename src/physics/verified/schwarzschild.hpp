/**
 * @file verified/schwarzschild.hpp
 * @brief Verified Schwarzschild metric functions - derived from Rocq formalization
 *
 * Maintained C++ reference for rocq/theories/Metrics/Schwarzschild.v
 * Analytical values exercised by the C++ tests:
 *   - r_s = 2M (Schwarzschild radius)
 *   - r_ISCO = 6M (ISCO in geometric units)
 *   - r_ph = 3M (photon sphere = 1.5 r_s)
 *
 * Metric in Boyer-Lindquist coordinates (c = G = 1, geometric units):
 *   ds^2 = -(1 - 2M/r) dt^2 + (1 - 2M/r)^(-1) dr^2 + r^2 dOmega^2
 *
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
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
 * @param m Black hole mass in geometric units
 * @return r_s = 2M
 */
[[nodiscard]] constexpr double schwarzschildRadius(double m) noexcept {
  return 2.0 * m;
}

/**
 * @brief ISCO radius: r_ISCO = 6M = 3 r_s (geometric units)
 *
 * Derived from Rocq: Definition schwarzschild_isco (M : R) : R := 6 * M.
 * Theorem schwarzschild_isco_radius: r_isco = 6 * M.
 *
 * @param m Black hole mass in geometric units
 * @return r_ISCO = 6M
 */
[[nodiscard]] constexpr double schwarzschildIsco(double m) noexcept {
  return 6.0 * m;
}

/**
 * @brief Photon sphere radius: r_ph = 3M = 1.5 r_s
 *
 * Derived from Rocq: Definition photon_sphere_radius (M : R) : R := 3 * M / 2 * 2 = 3M.
 * Unstable circular photon orbits exist at r = 3M.
 *
 * @param m Black hole mass in geometric units
 * @return r_ph = 3M
 */
[[nodiscard]] constexpr double photonSphereRadius(double m) noexcept {
  return 3.0 * m;
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
 * @param m Black hole mass (geometric units)
 * @return f = 1 - 2M/r
 */
[[nodiscard]] constexpr double fSchwarzschild(double r, double m) noexcept {
  return 1.0 - (2.0 * m) / r;
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
 * @param m Black hole mass
 * @return g_tt = -(1 - 2M/r)
 */
[[nodiscard]] constexpr double schwarzschildGTt(double r, double m) noexcept {
  return -fSchwarzschild(r, m);
}

/**
 * @brief Schwarzschild g_rr component: g_rr = 1/(1 - 2M/r)
 *
 * Derived from Rocq: schwarzschild_metric returns mkMetric(..., 1/f, ...) for g_rr
 *
 * @param r Radial coordinate
 * @param m Black hole mass
 * @return g_rr = 1/(1 - 2M/r)
 */
[[nodiscard]] constexpr double schwarzschildGRr(double r, double m) noexcept {
  return 1.0 / fSchwarzschild(r, m);
}

/**
 * @brief Schwarzschild g_thth component: g_thth = r^2
 *
 * Derived from Rocq: g_thth := r^2
 *
 * @param r Radial coordinate
 * @return g_thth = r^2
 */
[[nodiscard]] constexpr double schwarzschildGThth(double r) noexcept {
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
[[nodiscard]] inline double schwarzschildGPhph(double r, double theta) noexcept {
  const double sinTheta = std::sin(theta);
  return r * r * sinTheta * sinTheta;
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
[[nodiscard]] constexpr double christoffelTTr(double r, double m) noexcept {
  return m / (r * (r - 2.0 * m));
}

/**
 * @brief Gamma^r_{tt} = M(r - 2M) / r^3
 *
 * Derived from Rocq: Definition christoffel_r_tt (r M : R) : R :=
 *   M * (r - 2 * M) / r^3.
 */
[[nodiscard]] constexpr double christoffelRTt(double r, double m) noexcept {
  const double r3 = r * r * r;
  return m * (r - 2.0 * m) / r3;
}

/**
 * @brief Gamma^r_{rr} = -M / (r(r - 2M))
 *
 * Derived from Rocq: Definition christoffel_r_rr (r M : R) : R :=
 *   - M / (r * (r - 2 * M)).
 */
[[nodiscard]] constexpr double christoffelRRr(double r, double m) noexcept {
  return -m / (r * (r - 2.0 * m));
}

/**
 * @brief Gamma^r_{thth} = -(r - 2M)
 *
 * Derived from Rocq: Definition christoffel_r_thth (r M : R) : R := -(r - 2 * M).
 */
[[nodiscard]] constexpr double christoffelRThth(double r, double m) noexcept {
  return -(r - 2.0 * m);
}

/**
 * @brief Gamma^r_{phph} = -(r - 2M) sin^2(theta)
 *
 * Derived from Rocq: Definition christoffel_r_phph (r theta M : R) : R :=
 *   -(r - 2 * M) * (sin theta)^2.
 */
[[nodiscard]] inline double christoffelRPhph(double r, double theta, double m) noexcept {
  const double sinTheta = std::sin(theta);
  return -(r - 2.0 * m) * sinTheta * sinTheta;
}

/**
 * @brief Gamma^th_{r th} = Gamma^th_{th r} = 1/r
 *
 * Derived from Rocq: Definition christoffel_th_rth (r : R) : R := 1 / r.
 */
[[nodiscard]] constexpr double christoffelThRth(double r) noexcept {
  return 1.0 / r;
}

/**
 * @brief Gamma^th_{phph} = -sin(theta)cos(theta)
 *
 * Derived from Rocq: Definition christoffel_th_phph (theta : R) : R :=
 *   - sin theta * cos theta.
 */
[[nodiscard]] inline double christoffelThPhph(double theta) noexcept {
  return -std::sin(theta) * std::cos(theta);
}

/**
 * @brief Gamma^ph_{r ph} = Gamma^ph_{ph r} = 1/r
 *
 * Derived from Rocq: Definition christoffel_ph_rph (r : R) : R := 1 / r.
 */
[[nodiscard]] constexpr double christoffelPhRph(double r) noexcept {
  return 1.0 / r;
}

/**
 * @brief Gamma^ph_{th ph} = Gamma^ph_{ph th} = cot(theta)
 *
 * Derived from Rocq: Definition christoffel_ph_thph (theta : R) : R :=
 *   cos theta / sin theta.
 */
[[nodiscard]] inline double christoffelPhThph(double theta) noexcept {
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
 * @param m Black hole mass
 * @return Radial acceleration d^2r/dlambda^2
 */
[[nodiscard]] inline double radialAcceleration(double r, double dr, double dtheta, double dphi,
                                               double theta, double m) noexcept {
  // Note: dt/dlambda is normalized to 1 in the original definition
  return -christoffelRTt(r, m) - christoffelRRr(r, m) * dr * dr -
         christoffelRThth(r, m) * dtheta * dtheta - christoffelRPhph(r, theta, m) * dphi * dphi;
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
 * @param m Black hole mass
 * @return Kretschmann scalar
 */
[[nodiscard]] constexpr double kretschmannSchwarzschild(double r, double m) noexcept {
  const double r6 = r * r * r * r * r * r;
  return 48.0 * m * m / r6;
}

// ============================================================================
// Helper Functions for Validation
// ============================================================================

/**
 * @brief Check if point is outside the event horizon
 *
 * @param r Radial coordinate
 * @param m Black hole mass
 * @return true if r > 2M (outside horizon)
 */
[[nodiscard]] constexpr bool outsideHorizon(double r, double m) noexcept {
  return r > schwarzschildRadius(m);
}

/**
 * @brief Check if point is outside the photon sphere
 *
 * @param r Radial coordinate
 * @param m Black hole mass
 * @return true if r > 3M (outside photon sphere)
 */
[[nodiscard]] constexpr bool outsidePhotonSphere(double r, double m) noexcept {
  return r > photonSphereRadius(m);
}

/**
 * @brief Check if point is outside the ISCO
 *
 * @param r Radial coordinate
 * @param m Black hole mass
 * @return true if r > 6M (outside ISCO)
 */
[[nodiscard]] constexpr bool outsideIsco(double r, double m) noexcept {
  return r > schwarzschildIsco(m);
}

} // namespace verified

#endif // PHYSICS_VERIFIED_SCHWARZSCHILD_HPP
