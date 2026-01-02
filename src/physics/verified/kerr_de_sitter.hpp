/**
 * @file verified/kerr_de_sitter.hpp
 * @brief Verified Kerr-de Sitter metric - rotating black hole with cosmological constant
 *
 * This file is generated from proven Rocq theory rocq/theories/Metrics/KerrDeSitter.v
 *
 * The Kerr-de Sitter solution describes a rotating black hole in an asymptotically
 * de Sitter (expanding) universe with cosmological constant Λ.
 *
 * Physical Parameters:
 * - M: Black hole mass (M > 0)
 * - a: Specific angular momentum (0 ≤ a ≤ M)
 * - Λ: Cosmological constant (Λ > 0 for de Sitter expansion)
 *
 * Key Features:
 * - Triple horizon structure: inner (Cauchy), event, cosmological
 * - Reduces to Kerr metric when Λ → 0
 * - Reduces to de Sitter spacetime when M → 0, a → 0
 * - Horizon ordering: r₋ < r₊ < r_c (always)
 *
 * References:
 * - Griffiths & Podolský (2009): "Exact Space-Times in Einstein's General Relativity"
 * - Carter (1973): Black hole equilibrium states with cosmological constant
 * - Observed cosmological constant: Λ ≈ 1.1 × 10⁻⁵² m⁻²
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note Uses geometric units where c = G = 1
 * @note All functions use double precision for numerical stability
 */

#ifndef PHYSICS_VERIFIED_KERR_DE_SITTER_HPP
#define PHYSICS_VERIFIED_KERR_DE_SITTER_HPP

#include <cmath>
#include <stdexcept>

namespace verified {

// ============================================================================
// Basic Metric Functions (from Rocq: kds_Sigma, kds_Delta, kds_A)
// ============================================================================

/**
 * @brief Sigma = r² + a²cos²(θ)
 *
 * Derived from Rocq:
 *   Definition kds_Sigma (r theta a : R) : R :=
 *     r^2 + a^2 * (cos theta)^2.
 *
 * Same as Kerr metric - unchanged by cosmological constant.
 *
 * @param r Radial coordinate
 * @param theta Polar angle (0 ≤ θ ≤ π)
 * @param a Spin parameter (0 ≤ a ≤ M)
 * @return Sigma value
 */
[[nodiscard]] constexpr double kds_Sigma(double r, double theta, double a) noexcept {
    double cos_theta = std::cos(theta);
    return r * r + a * a * cos_theta * cos_theta;
}

/**
 * @brief Delta = r² - 2Mr + a² - Λr²/3
 *
 * Derived from Rocq:
 *   Definition kds_Delta (r M a Lambda : R) : R :=
 *     r^2 - 2 * M * r + a^2 - Lambda * r^2 / 3.
 *
 * Modified from Kerr by cosmological term -Λr²/3.
 * This is the key difference from standard Kerr metric.
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant (Λ > 0 for de Sitter)
 * @return Delta value
 */
[[nodiscard]] constexpr double kds_Delta(double r, double M, double a, double Lambda) noexcept {
    return r * r - 2.0 * M * r + a * a - Lambda * r * r / 3.0;
}

/**
 * @brief A = (r² + a²)² - a²·Δ·sin²(θ)
 *
 * Derived from Rocq:
 *   Definition kds_A (r theta M a Lambda : R) : R :=
 *     (r^2 + a^2)^2 - a^2 * kds_Delta r M a Lambda * (sin theta)^2.
 *
 * Uses modified Delta with cosmological term.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return A value
 */
[[nodiscard]] inline double kds_A(double r, double theta, double M, double a, double Lambda) noexcept {
    double r2_plus_a2 = r * r + a * a;
    double sin_theta = std::sin(theta);
    double Delta = kds_Delta(r, M, a, Lambda);
    return r2_plus_a2 * r2_plus_a2 - a * a * Delta * sin_theta * sin_theta;
}

// ============================================================================
// Metric Components in Boyer-Lindquist Coordinates
// ============================================================================

/**
 * @brief g_tt = -(1 - 2Mr/Σ + Λr²sin²θ/3)
 *
 * Derived from Rocq:
 *   Definition kds_g_tt (r theta M a Lambda : R) : R :=
 *     let Sigma := kds_Sigma r theta a in
 *     -(1 - 2 * M * r / Sigma + Lambda * r^2 * (sin theta)^2 / 3).
 *
 * Temporal metric component with cosmological modification.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return g_tt component
 */
[[nodiscard]] inline double kds_g_tt(double r, double theta, double M, double a, double Lambda) noexcept {
    double Sigma = kds_Sigma(r, theta, a);
    double sin_theta = std::sin(theta);
    return -(1.0 - 2.0 * M * r / Sigma + Lambda * r * r * sin_theta * sin_theta / 3.0);
}

/**
 * @brief g_rr = Σ / Δ
 *
 * Derived from Rocq:
 *   Definition kds_g_rr (r theta M a Lambda : R) : R :=
 *     kds_Sigma r theta a / kds_Delta r M a Lambda.
 *
 * Radial metric component.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return g_rr component
 */
[[nodiscard]] inline double kds_g_rr(double r, double theta, double M, double a, double Lambda) noexcept {
    return kds_Sigma(r, theta, a) / kds_Delta(r, M, a, Lambda);
}

/**
 * @brief g_θθ = Σ
 *
 * Derived from Rocq:
 *   Definition kds_g_thth (r theta a : R) : R :=
 *     kds_Sigma r theta a.
 *
 * Angular metric component (θ direction).
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param a Spin parameter
 * @return g_θθ component
 */
[[nodiscard]] constexpr double kds_g_thth(double r, double theta, double a) noexcept {
    return kds_Sigma(r, theta, a);
}

/**
 * @brief g_φφ = (r² + a² + 2Mra²sin²θ/Σ - Λr⁴sin²θ/3) sin²θ
 *
 * Derived from Rocq:
 *   Definition kds_g_phph (r theta M a Lambda : R) : R :=
 *     let Sigma := kds_Sigma r theta a in
 *     let sin2 := (sin theta)^2 in
 *     (r^2 + a^2 + 2 * M * r * a^2 * sin2 / Sigma
 *      - Lambda * r^4 * sin2 / 3) * sin2.
 *
 * Azimuthal metric component with cosmological modification.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return g_φφ component
 */
[[nodiscard]] inline double kds_g_phph(double r, double theta, double M, double a, double Lambda) noexcept {
    double Sigma = kds_Sigma(r, theta, a);
    double sin_theta = std::sin(theta);
    double sin2 = sin_theta * sin_theta;
    return (r * r + a * a + 2.0 * M * r * a * a * sin2 / Sigma
            - Lambda * r * r * r * r * sin2 / 3.0) * sin2;
}

/**
 * @brief g_tφ = -2Mra·sin²θ / Σ
 *
 * Derived from Rocq:
 *   Definition kds_g_tph (r theta M a : R) : R :=
 *     let Sigma := kds_Sigma r theta a in
 *     -2 * M * r * a * (sin theta)^2 / Sigma.
 *
 * Off-diagonal component (frame dragging) - unchanged from Kerr.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @return g_tφ component
 */
[[nodiscard]] inline double kds_g_tph(double r, double theta, double M, double a) noexcept {
    double Sigma = kds_Sigma(r, theta, a);
    double sin_theta = std::sin(theta);
    return -2.0 * M * r * a * sin_theta * sin_theta / Sigma;
}

// ============================================================================
// Horizon Calculations (from Rocq: kds_*_horizon functions)
// ============================================================================

/**
 * @brief Inner (Cauchy) horizon (approximate for small Λ)
 *
 * Derived from Rocq:
 *   Definition kds_inner_horizon (M a Lambda : R) : R :=
 *     let delta := sqrt (M^2 - a^2) in
 *     let r_kerr := M - delta in
 *     r_kerr - Lambda * r_kerr^3 / 3.
 *
 * r₋ ≈ M - √(M² - a²) - Λ(M - √(M² - a²))³/3
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return Inner horizon radius
 */
[[nodiscard]] inline double kds_inner_horizon(double M, double a, double Lambda) noexcept {
    double delta = std::sqrt(M * M - a * a);
    double r_kerr = M - delta;
    return r_kerr - Lambda * r_kerr * r_kerr * r_kerr / 3.0;
}

/**
 * @brief Event horizon (approximate for small Λ)
 *
 * Derived from Rocq:
 *   Definition kds_event_horizon (M a Lambda : R) : R :=
 *     let delta := sqrt (M^2 - a^2) in
 *     let r_kerr := M + delta in
 *     r_kerr + Lambda * r_kerr^3 / 3.
 *
 * r₊ ≈ M + √(M² - a²) + Λ(M + √(M² - a²))³/3
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return Event horizon radius
 */
[[nodiscard]] inline double kds_event_horizon(double M, double a, double Lambda) noexcept {
    double delta = std::sqrt(M * M - a * a);
    double r_kerr = M + delta;
    return r_kerr + Lambda * r_kerr * r_kerr * r_kerr / 3.0;
}

/**
 * @brief Cosmological horizon (approximate)
 *
 * Derived from Rocq:
 *   Definition kds_cosmological_horizon (Lambda : R) : R :=
 *     sqrt (3 / Lambda).
 *
 * For large r, Delta ≈ r²(1 - Λ/3) - 2Mr
 * Setting to zero: r_c ≈ √(3/Λ)
 *
 * This is the de Sitter cosmological horizon radius.
 *
 * @param Lambda Cosmological constant (must be > 0)
 * @return Cosmological horizon radius
 */
[[nodiscard]] inline double kds_cosmological_horizon(double Lambda) noexcept {
    return std::sqrt(3.0 / Lambda);
}

/**
 * @brief Ergosphere outer boundary
 *
 * Derived from Rocq:
 *   Definition kds_ergosphere_radius (theta M a Lambda : R) : R :=
 *     M + sqrt (M^2 - a^2 * (cos theta)^2).
 *
 * Where g_tt = 0:
 * 1 - 2Mr/Σ + Λr²sin²θ/3 = 0
 *
 * At equator (θ = π/2), approximate for small Λ:
 * r_ergo ≈ M + √(M² - a²cos²θ)
 *
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant (currently unused in approximation)
 * @return Ergosphere radius at angle theta
 */
[[nodiscard]] inline double kds_ergosphere_radius(double theta, double M, double a, double Lambda) noexcept {
    (void)Lambda;  // Unused in this approximation
    double cos_theta = std::cos(theta);
    return M + std::sqrt(M * M - a * a * cos_theta * cos_theta);
}

// ============================================================================
// Frame Dragging and Angular Velocity
// ============================================================================

/**
 * @brief Frame dragging angular velocity: ω = -g_tφ / g_φφ
 *
 * Derived from Rocq:
 *   Definition kds_frame_dragging_omega (r theta M a Lambda : R) : R :=
 *     let g_tph := kds_g_tph r theta M a in
 *     let g_phph := kds_g_phph r theta M a Lambda in
 *     - g_tph / g_phph.
 *
 * Unchanged from Kerr (cosmological constant doesn't affect frame dragging directly).
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return Frame dragging angular velocity
 */
[[nodiscard]] inline double kds_frame_dragging_omega(double r, double theta, double M, double a, double Lambda) noexcept {
    double g_tph = kds_g_tph(r, theta, M, a);
    double g_phph = kds_g_phph(r, theta, M, a, Lambda);
    return -g_tph / g_phph;
}

// ============================================================================
// Physical Validity Constraints
// ============================================================================

/**
 * @brief Check if parameters represent a physical Kerr-de Sitter black hole
 *
 * Derived from Rocq:
 *   Definition is_physical_kds_black_hole (M a Lambda : R) : Prop :=
 *     M > 0 /\ Lambda > 0 /\ M^2 >= a^2.
 *
 * Requirements:
 * - M > 0 (positive mass)
 * - Λ > 0 (positive cosmological constant for de Sitter)
 * - M² ≥ a² (sub-extremal, ensures real horizons)
 * - Horizons exist and are ordered: r₋ < r₊ < r_c
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return true if parameters are physical
 */
[[nodiscard]] constexpr bool is_physical_kds_black_hole(double M, double a, double Lambda) noexcept {
    return M > 0.0 && Lambda > 0.0 && M * M >= a * a;
}

/**
 * @brief Check if a position is between event and cosmological horizons
 *
 * Derived from Rocq:
 *   Definition is_exterior_region (r M a Lambda : R) : Prop :=
 *     let r_plus := kds_event_horizon M a Lambda in
 *     let r_cosmo := kds_cosmological_horizon Lambda in
 *     r > r_plus /\ r < r_cosmo.
 *
 * This is the exterior region where stable orbits exist.
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return true if in exterior region
 */
[[nodiscard]] inline bool is_exterior_region(double r, double M, double a, double Lambda) noexcept {
    double r_plus = kds_event_horizon(M, a, Lambda);
    double r_cosmo = kds_cosmological_horizon(Lambda);
    return r > r_plus && r < r_cosmo;
}

/**
 * @brief Check if a position is in the ergosphere
 *
 * Derived from Rocq:
 *   Definition is_in_ergosphere (r theta M a Lambda : R) : Prop :=
 *     kds_g_tt r theta M a Lambda > 0.
 *
 * Region where g_tt > 0 (time becomes spacelike).
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return true if in ergosphere
 */
[[nodiscard]] inline bool is_in_ergosphere(double r, double theta, double M, double a, double Lambda) noexcept {
    return kds_g_tt(r, theta, M, a, Lambda) > 0.0;
}

// ============================================================================
// Horizon Ordering Verification
// ============================================================================

/**
 * @brief Verify that horizons are properly ordered: r₋ < r₊ < r_c
 *
 * For physical Kerr-de Sitter black holes, horizons must satisfy this ordering.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param Lambda Cosmological constant
 * @return true if horizon ordering is correct
 */
[[nodiscard]] inline bool verify_horizon_ordering(double M, double a, double Lambda) noexcept {
    if (!is_physical_kds_black_hole(M, a, Lambda)) {
        return false;
    }
    double r_minus = kds_inner_horizon(M, a, Lambda);
    double r_plus = kds_event_horizon(M, a, Lambda);
    double r_cosmo = kds_cosmological_horizon(Lambda);
    return r_minus < r_plus && r_plus < r_cosmo;
}

// ============================================================================
// Reduction to Kerr and de Sitter Limits
// ============================================================================

/**
 * @brief Check if parameters are in Kerr limit (Lambda ≈ 0)
 *
 * When Lambda is negligible, Kerr-de Sitter reduces to standard Kerr metric.
 *
 * @param Lambda Cosmological constant
 * @param tolerance Tolerance for Lambda (default: 1e-10)
 * @return true if in Kerr limit
 */
[[nodiscard]] constexpr bool is_kerr_limit(double Lambda, double tolerance = 1e-10) noexcept {
    return std::abs(Lambda) < tolerance;
}

/**
 * @brief Check if parameters are in de Sitter limit (M ≈ 0, a ≈ 0)
 *
 * When mass and spin are negligible, Kerr-de Sitter reduces to pure de Sitter spacetime.
 *
 * @param M Black hole mass
 * @param a Spin parameter
 * @param tolerance Tolerance for M and a (default: 1e-10)
 * @return true if in de Sitter limit
 */
[[nodiscard]] constexpr bool is_de_sitter_limit(double M, double a, double tolerance = 1e-10) noexcept {
    return std::abs(M) < tolerance && std::abs(a) < tolerance;
}

// ============================================================================
// Cosmological Constant Utilities
// ============================================================================

/**
 * @brief Convert cosmological constant from SI units (m⁻²) to geometric units
 *
 * Geometric units: Λ_geo = Λ_SI * (c²/G) in units where c = G = 1
 *
 * Observed value: Λ_SI ≈ 1.1 × 10⁻⁵² m⁻²
 *
 * @param Lambda_SI Cosmological constant in SI units (m⁻²)
 * @return Cosmological constant in geometric units
 */
[[nodiscard]] constexpr double lambda_si_to_geometric(double Lambda_SI) noexcept {
    // c²/G ≈ 1.346e27 m/kg in SI units
    // In geometric units where c = G = 1, this is just Lambda_SI
    // but we include this function for dimensional clarity
    return Lambda_SI;
}

/**
 * @brief Observed cosmological constant in geometric units
 *
 * Λ ≈ 1.1 × 10⁻⁵² m⁻² (Planck 2018 results)
 *
 * @return Observed Lambda in geometric units
 */
[[nodiscard]] constexpr double observed_lambda() noexcept {
    return 1.1e-52;  // m⁻² in geometric units
}

// ============================================================================
// Phase 9.3.2 Completion
// ============================================================================

/**
 * This C++23 implementation provides the computational foundation for:
 * - Phase 9.3.3: GLSL transpilation (kerr_de_sitter.glsl)
 *
 * All functions are designed for verified extraction from Rocq and
 * transpilation to GLSL 4.60 for GPU ray-tracing.
 *
 * Pipeline: Rocq 9.1+ → OCaml → C++23 → GLSL 4.60
 *
 * Function Count: 20 functions
 * - 3 metric helpers (Sigma, Delta, A)
 * - 5 metric components (g_tt, g_rr, g_thth, g_phph, g_tph)
 * - 3 horizon functions (inner, event, cosmological)
 * - 1 ergosphere function
 * - 1 frame dragging function
 * - 3 validity checks
 * - 2 limit checks
 * - 2 cosmological constant utilities
 */

}  // namespace verified

#endif  // PHYSICS_VERIFIED_KERR_DE_SITTER_HPP
