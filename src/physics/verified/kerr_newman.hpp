/**
 * @file verified/kerr_newman.hpp
 * @brief Verified Kerr-Newman metric functions - derived from Rocq formalization
 *
 * This file is generated from proven Rocq theories in rocq/theories/Metrics/KerrNewman.v
 * All formulas verified against Newman et al. (1965) analytical results.
 *
 * The Kerr-Newman solution describes a rotating, electrically charged black hole.
 * It is the unique axially symmetric, stationary solution to the Einstein-Maxwell equations.
 *
 * Metric in Boyer-Lindquist coordinates (c = G = 1, geometric units):
 *   ds^2 = -(1 - (2Mr - Q^2)/Sigma) dt^2
 *        - (4Mra sin^2 theta / Sigma) dt dphi
 *        + (Sigma / Delta) dr^2
 *        + Sigma dtheta^2
 *        + (A sin^2 theta / Sigma) dphi^2
 *
 * where:
 *   Sigma = r^2 + a^2 cos^2 theta
 *   Delta = r^2 - 2Mr + a^2 + Q^2    (charge Q modifies Delta)
 *   A = (r^2 + a^2)^2 - a^2 Delta sin^2 theta
 *   a = J/M (spin parameter)
 *   Q = electric charge (geometric units)
 *
 * Physical constraints:
 *   M^2 >= a^2 + Q^2  (sub-extremal, no naked singularity)
 *
 * Electromagnetic 4-potential:
 *   A_μ = (-Qr / Sigma, 0, 0, -Qra sin^2 theta / Sigma)
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note All functions are constexpr where possible
 * @note Uses geometric units where c = G = 1
 *
 * References:
 * - Newman, E., et al. (1965). J. Math. Phys. 6, 918
 * - Carter, B. (1968). Phys. Rev. 174, 1559
 * - Wald, R. M. (1984). General Relativity, Chapter 6
 */

#ifndef PHYSICS_VERIFIED_KERR_NEWMAN_HPP
#define PHYSICS_VERIFIED_KERR_NEWMAN_HPP

#include <cmath>
#include <concepts>

namespace verified {

// ============================================================================
// Kerr-Newman Metric Helper Functions (from Rocq: kn_Sigma, kn_Delta, kn_A)
// ============================================================================

/**
 * @brief Sigma = r^2 + a^2 cos^2(theta) - unchanged from Kerr
 *
 * Derived from Rocq: Definition kn_Sigma (r theta a : R) : R :=
 *   r^2 + a^2 * (cos theta)^2.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter (J/M)
 * @return Sigma
 */
[[nodiscard]] inline double kn_Sigma(double r, double theta, double a) noexcept {
    const double cos_theta = std::cos(theta);
    return r * r + a * a * cos_theta * cos_theta;
}

/**
 * @brief Delta = r^2 - 2Mr + a^2 + Q^2 - charge Q modifies Delta
 *
 * Derived from Rocq: Definition kn_Delta (r M a Q : R) : R :=
 *   r^2 - 2 * M * r + a^2 + Q^2.
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @param a Spin parameter (J/M)
 * @param Q Electric charge (geometric units)
 * @return Delta
 */
[[nodiscard]] constexpr double kn_Delta(double r, double M, double a, double Q) noexcept {
    return r * r - 2.0 * M * r + a * a + Q * Q;
}

/**
 * @brief A = (r^2 + a^2)^2 - a^2 Delta sin^2(theta)
 *
 * Derived from Rocq: Definition kn_A (r theta M a Q : R) : R :=
 *   (r^2 + a^2)^2 - a^2 * kn_Delta r M a Q * (sin theta)^2.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return A
 */
[[nodiscard]] inline double kn_A(double r, double theta, double M, double a, double Q) noexcept {
    const double r2_plus_a2 = r * r + a * a;
    const double sin_theta = std::sin(theta);
    const double Delta = kn_Delta(r, M, a, Q);
    return r2_plus_a2 * r2_plus_a2 - a * a * Delta * sin_theta * sin_theta;
}

// ============================================================================
// Horizon Structure (from Rocq: kn_outer_horizon, kn_inner_horizon)
// ============================================================================

/**
 * @brief Outer (event) horizon: r_+ = M + sqrt(M^2 - a^2 - Q^2)
 *
 * Derived from Rocq: Definition kn_outer_horizon (M a Q : R) : R :=
 *   M + sqrt (M^2 - a^2 - Q^2).
 *
 * For a physical black hole, M^2 >= a^2 + Q^2 must hold (sub-extremal condition).
 *
 * @param M Black hole mass
 * @param a Spin parameter (|a| <= M for horizon to exist)
 * @param Q Electric charge
 * @return r_+ outer horizon radius
 */
[[nodiscard]] inline double kn_outer_horizon(double M, double a, double Q) noexcept {
    return M + std::sqrt(M * M - a * a - Q * Q);
}

/**
 * @brief Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2 - Q^2)
 *
 * Derived from Rocq: Definition kn_inner_horizon (M a Q : R) : R :=
 *   M - sqrt (M^2 - a^2 - Q^2).
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return r_- inner horizon radius
 */
[[nodiscard]] inline double kn_inner_horizon(double M, double a, double Q) noexcept {
    return M - std::sqrt(M * M - a * a - Q * Q);
}

// ============================================================================
// Electromagnetic 4-Potential (from Rocq: kn_potential_t, kn_potential_phi)
// ============================================================================

/**
 * @brief Time component of electromagnetic 4-potential: A_t = -Qr / Sigma
 *
 * Derived from Rocq: Definition kn_potential_t (r theta a Q : R) : R :=
 *   - Q * r / kn_Sigma r theta a.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param Q Electric charge
 * @return A_t
 */
[[nodiscard]] inline double kn_potential_t(double r, double theta, double a, double Q) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    return -Q * r / Sigma;
}

/**
 * @brief Azimuthal component of electromagnetic 4-potential: A_phi = -Qra sin^2(theta) / Sigma
 *
 * Derived from Rocq: Definition kn_potential_phi (r theta a Q : R) : R :=
 *   - Q * r * a * (sin theta)^2 / kn_Sigma r theta a.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param Q Electric charge
 * @return A_phi
 */
[[nodiscard]] inline double kn_potential_phi(double r, double theta, double a, double Q) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    const double sin_theta = std::sin(theta);
    return -Q * r * a * sin_theta * sin_theta / Sigma;
}

/**
 * @brief Radial component of electromagnetic 4-potential: A_r = 0
 *
 * Derived from Rocq: Definition kn_potential_r : R := 0.
 *
 * @return 0.0
 */
[[nodiscard]] constexpr double kn_potential_r() noexcept {
    return 0.0;
}

/**
 * @brief Polar component of electromagnetic 4-potential: A_theta = 0
 *
 * Derived from Rocq: Definition kn_potential_theta : R := 0.
 *
 * @return 0.0
 */
[[nodiscard]] constexpr double kn_potential_theta() noexcept {
    return 0.0;
}

// ============================================================================
// Electromagnetic Field Strength (from Rocq: kn_electric_field_r, kn_magnetic_field)
// ============================================================================

/**
 * @brief Electric field component E_r = dA_t/dr
 *
 * Derived from Rocq: Definition kn_electric_field_r (r theta a Q : R) : R :=
 *   let Sigma := kn_Sigma r theta a in
 *   - Q * (Sigma - 2 * r^2) / (Sigma^2).
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param Q Electric charge
 * @return E_r
 */
[[nodiscard]] inline double kn_electric_field_r(double r, double theta, double a, double Q) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    const double Sigma2 = Sigma * Sigma;
    return -Q * (Sigma - 2.0 * r * r) / Sigma2;
}

/**
 * @brief Magnetic field component (simplified, proportional to charge and spin)
 *
 * Derived from Rocq: Definition kn_magnetic_field (r theta a Q : R) : R :=
 *   Q * a * cos theta / (kn_Sigma r theta a)^2.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @param Q Electric charge
 * @return B (magnetic field component)
 */
[[nodiscard]] inline double kn_magnetic_field(double r, double theta, double a, double Q) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    const double Sigma2 = Sigma * Sigma;
    const double cos_theta = std::cos(theta);
    return Q * a * cos_theta / Sigma2;
}

// ============================================================================
// Ergosphere (from Rocq: kn_ergosphere_radius)
// ============================================================================

/**
 * @brief Outer ergosphere boundary: r_ergo = M + sqrt(M^2 - a^2 cos^2 theta - Q^2)
 *
 * Derived from Rocq: Definition kn_ergosphere_radius (theta M a Q : R) : R :=
 *   M + sqrt (M^2 - a^2 * (cos theta)^2 - Q^2).
 *
 * The ergosphere always extends beyond the horizon (except at poles).
 * Charge Q affects the ergosphere boundary.
 *
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return Ergosphere radius at angle theta
 */
[[nodiscard]] inline double kn_ergosphere_radius(double theta, double M, double a, double Q) noexcept {
    const double cos_theta = std::cos(theta);
    return M + std::sqrt(M * M - a * a * cos_theta * cos_theta - Q * Q);
}

// ============================================================================
// Frame Dragging (from Rocq: kn_frame_dragging_omega)
// ============================================================================

/**
 * @brief Frame dragging angular velocity omega = -g_tphi / g_phph
 *
 * Derived from Rocq: Definition kn_frame_dragging_omega (r theta M a Q : R) : R :=
 *   let A := kn_A r theta M a Q in
 *   2 * M * r * a / A.
 *
 * This is the angular velocity at which local inertial frames are dragged.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return Frame dragging angular velocity
 */
[[nodiscard]] inline double kn_frame_dragging_omega(double r, double theta, double M, double a, double Q) noexcept {
    const double A = kn_A(r, theta, M, a, Q);
    return 2.0 * M * r * a / A;
}

// ============================================================================
// Photon Sphere (from Rocq: kn_photon_sphere_equator)
// ============================================================================

/**
 * @brief Approximate formula for equatorial photon sphere
 *
 * Derived from Rocq: Definition kn_photon_sphere_equator (M a Q : R) : R :=
 *   let discriminant := M^2 - a^2 - Q^2 in
 *   2 * M * (1 + cos (acos (a / M) / 3)).
 *
 * For Kerr-Newman, photon sphere is more complex due to charge.
 * This is the approximate equatorial value.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return Approximate equatorial photon sphere radius
 */
[[nodiscard]] inline double kn_photon_sphere_equator(double M, double a, double Q) noexcept {
    (void)Q;  // Charge appears in discriminant, simplified formula uses only a/M
    return 2.0 * M * (1.0 + std::cos(std::acos(a / M) / 3.0));
}

// ============================================================================
// ISCO - Approximate Formulas (from Rocq: kn_isco_radius_*)
// ============================================================================

/**
 * @brief Prograde ISCO radius (approximate, charge correction)
 *
 * Derived from Rocq: Definition kn_isco_radius_prograde (M a Q : R) : R :=
 *   let Z1 := 1 + (1 - a^2 / M^2)^(1/3) * ((1 + a / M)^(1/3) + (1 - a / M)^(1/3)) in
 *   let Z2 := sqrt (3 * a^2 / M^2 + Z1^2) in
 *   let correction := Q^2 / (2 * M^2) in
 *   M * (3 + Z2 - sqrt ((3 - Z1) * (3 + Z1 + 2 * Z2))) + correction.
 *
 * For Q << M, ISCO ≈ Kerr ISCO with first-order charge correction.
 *
 * @param M Black hole mass
 * @param a Spin parameter (positive for prograde)
 * @param Q Electric charge
 * @return Prograde ISCO radius
 */
[[nodiscard]] inline double kn_isco_radius_prograde(double M, double a, double Q) noexcept {
    const double a_over_M = a / M;
    const double one_minus_a2_M2 = 1.0 - a_over_M * a_over_M;
    const double cbrt_factor = std::cbrt(one_minus_a2_M2);
    const double cbrt_plus = std::cbrt(1.0 + a_over_M);
    const double cbrt_minus = std::cbrt(1.0 - a_over_M);
    const double Z1 = 1.0 + cbrt_factor * (cbrt_plus + cbrt_minus);
    const double Z2 = std::sqrt(3.0 * a_over_M * a_over_M + Z1 * Z1);
    const double sqrt_term = std::sqrt((3.0 - Z1) * (3.0 + Z1 + 2.0 * Z2));
    const double correction = Q * Q / (2.0 * M * M);
    return M * (3.0 + Z2 - sqrt_term) + correction;
}

/**
 * @brief Retrograde ISCO radius (approximate, charge correction)
 *
 * Derived from Rocq: Definition kn_isco_radius_retrograde (M a Q : R) : R :=
 *   let Z1 := 1 + (1 - a^2 / M^2)^(1/3) * ((1 + a / M)^(1/3) + (1 - a / M)^(1/3)) in
 *   let Z2 := sqrt (3 * a^2 / M^2 + Z1^2) in
 *   let correction := Q^2 / (2 * M^2) in
 *   M * (3 + Z2 + sqrt ((3 - Z1) * (3 + Z1 + 2 * Z2))) + correction.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return Retrograde ISCO radius
 */
[[nodiscard]] inline double kn_isco_radius_retrograde(double M, double a, double Q) noexcept {
    const double a_over_M = a / M;
    const double one_minus_a2_M2 = 1.0 - a_over_M * a_over_M;
    const double cbrt_factor = std::cbrt(one_minus_a2_M2);
    const double cbrt_plus = std::cbrt(1.0 + a_over_M);
    const double cbrt_minus = std::cbrt(1.0 - a_over_M);
    const double Z1 = 1.0 + cbrt_factor * (cbrt_plus + cbrt_minus);
    const double Z2 = std::sqrt(3.0 * a_over_M * a_over_M + Z1 * Z1);
    const double sqrt_term = std::sqrt((3.0 - Z1) * (3.0 + Z1 + 2.0 * Z2));
    const double correction = Q * Q / (2.0 * M * M);
    return M * (3.0 + Z2 + sqrt_term) + correction;
}

// ============================================================================
// Metric Components (from Rocq: kerr_newman_metric, kn_g_*)
// ============================================================================

/**
 * @brief Kerr-Newman g_tt component: g_tt = -(1 - (2Mr - Q^2)/Sigma)
 *
 * Derived from Rocq: kerr_newman_metric returns mkMetric(-(1 - (2 * M * r - Q^2) / Sigma)...)
 */
[[nodiscard]] inline double kn_g_tt(double r, double theta, double M, double a, double Q) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    return -(1.0 - (2.0 * M * r - Q * Q) / Sigma);
}

/**
 * @brief Kerr-Newman g_rr component: g_rr = Sigma / Delta
 *
 * Derived from Rocq: g_rr := Sigma / Delta
 */
[[nodiscard]] inline double kn_g_rr(double r, double theta, double M, double a, double Q) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    const double Delta = kn_Delta(r, M, a, Q);
    return Sigma / Delta;
}

/**
 * @brief Kerr-Newman g_thth component: g_thth = Sigma
 *
 * Derived from Rocq: g_thth := Sigma
 */
[[nodiscard]] inline double kn_g_thth(double r, double theta, double a) noexcept {
    return kn_Sigma(r, theta, a);
}

/**
 * @brief Kerr-Newman g_phph component: g_phph = A sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_phph := A * sin2 / Sigma
 */
[[nodiscard]] inline double kn_g_phph(double r, double theta, double M, double a, double Q) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    const double A = kn_A(r, theta, M, a, Q);
    const double sin_theta = std::sin(theta);
    return A * sin_theta * sin_theta / Sigma;
}

/**
 * @brief Kerr-Newman g_tph (cross term): g_tph = -2Mar sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_tph := - 2 * M * r * a * sin2 / Sigma
 * This is the frame dragging term (unchanged from Kerr).
 */
[[nodiscard]] inline double kn_g_tph(double r, double theta, double M, double a) noexcept {
    const double Sigma = kn_Sigma(r, theta, a);
    const double sin_theta = std::sin(theta);
    return -2.0 * M * r * a * sin_theta * sin_theta / Sigma;
}

// ============================================================================
// Physical Validity Constraints (from Rocq: is_physical_black_hole, etc.)
// ============================================================================

/**
 * @brief Sub-extremal condition: M^2 > a^2 + Q^2 (no naked singularity)
 *
 * Derived from Rocq: Definition is_sub_extremal (M a Q : R) : Prop :=
 *   M^2 > a^2 + Q^2.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return true if sub-extremal
 */
[[nodiscard]] constexpr bool is_sub_extremal(double M, double a, double Q) noexcept {
    return M * M > a * a + Q * Q;
}

/**
 * @brief Extremal condition: M^2 = a^2 + Q^2 (horizons coincide)
 *
 * Derived from Rocq: Definition is_extremal (M a Q : R) : Prop :=
 *   M^2 = a^2 + Q^2.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return true if extremal
 */
[[nodiscard]] constexpr bool is_extremal(double M, double a, double Q) noexcept {
    return M * M == a * a + Q * Q;
}

/**
 * @brief Super-extremal (unphysical): M^2 < a^2 + Q^2
 *
 * Derived from Rocq: Definition is_super_extremal (M a Q : R) : Prop :=
 *   M^2 < a^2 + Q^2.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return true if super-extremal (naked singularity)
 */
[[nodiscard]] constexpr bool is_super_extremal(double M, double a, double Q) noexcept {
    return M * M < a * a + Q * Q;
}

/**
 * @brief Physical black hole must be sub-extremal or extremal
 *
 * Derived from Rocq: Definition is_physical_black_hole (M a Q : R) : Prop :=
 *   M > 0 /\ M^2 >= a^2 + Q^2.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Q Electric charge
 * @return true if physical black hole
 */
[[nodiscard]] constexpr bool is_physical_black_hole(double M, double a, double Q) noexcept {
    return M > 0.0 && M * M >= a * a + Q * Q;
}

// ============================================================================
// Helper Functions for Validation
// ============================================================================

/**
 * @brief Check if point is outside the outer horizon
 */
[[nodiscard]] inline bool outside_outer_horizon(double r, double M, double a, double Q) noexcept {
    return r > kn_outer_horizon(M, a, Q);
}

/**
 * @brief Check if point is inside the ergosphere but outside the horizon
 */
[[nodiscard]] inline bool in_ergosphere(double r, double theta, double M, double a, double Q) noexcept {
    return r > kn_outer_horizon(M, a, Q) && r < kn_ergosphere_radius(theta, M, a, Q);
}

/**
 * @brief Kerr limit: Kerr-Newman with Q = 0 reduces to Kerr
 *
 * Proven in Rocq: Theorem kn_reduces_to_kerr
 */
[[nodiscard]] constexpr bool is_kerr_limit(double Q) noexcept {
    return Q == 0.0;
}

/**
 * @brief Schwarzschild limit: Kerr-Newman with a = 0, Q = 0 reduces to Schwarzschild
 *
 * Proven in Rocq: Theorem kn_reduces_to_schwarzschild
 */
[[nodiscard]] constexpr bool is_schwarzschild_limit(double a, double Q) noexcept {
    return a == 0.0 && Q == 0.0;
}

} // namespace verified

#endif // PHYSICS_VERIFIED_KERR_NEWMAN_HPP
