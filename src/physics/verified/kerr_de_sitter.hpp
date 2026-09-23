/**
 * @file verified/kerr_de_sitter.hpp
 * @brief Verified Kerr-de Sitter metric - rotating black hole with cosmological constant
 *
 * Maintained C++ reference for rocq/theories/Metrics/KerrDeSitter.v
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
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
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
[[nodiscard]] constexpr double kdsSigma(double r, double theta, double a) noexcept {
  double const cosTheta = std::cos(theta);
  return r * r + a * a * cosTheta * cosTheta;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant (Λ > 0 for de Sitter)
 * @return Delta value
 */
[[nodiscard]] constexpr double kdsDelta(double r, double m, double a, double lambda) noexcept {
  return r * r - 2.0 * m * r + a * a - lambda * r * r / 3.0;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return A value
 */
[[nodiscard]] inline double kdsA(double r, double theta, double m, double a,
                                 double lambda) noexcept {
  double const r2PlusA2 = r * r + a * a;
  double const sinTheta = std::sin(theta);
  double const delta = kdsDelta(r, m, a, lambda);
  return r2PlusA2 * r2PlusA2 - a * a * delta * sinTheta * sinTheta;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return g_tt component
 */
[[nodiscard]] inline double kdsGTt(double r, double theta, double m, double a,
                                   double lambda) noexcept {
  double const sigma = kdsSigma(r, theta, a);
  double const sinTheta = std::sin(theta);
  return -(1.0 - 2.0 * m * r / sigma + lambda * r * r * sinTheta * sinTheta / 3.0);
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return g_rr component
 */
[[nodiscard]] inline double kdsGRr(double r, double theta, double m, double a,
                                   double lambda) noexcept {
  return kdsSigma(r, theta, a) / kdsDelta(r, m, a, lambda);
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
[[nodiscard]] constexpr double kdsGThth(double r, double theta, double a) noexcept {
  return kdsSigma(r, theta, a);
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return g_φφ component
 */
[[nodiscard]] inline double kdsGPhph(double r, double theta, double m, double a,
                                     double lambda) noexcept {
  double const sigma = kdsSigma(r, theta, a);
  double const sinTheta = std::sin(theta);
  double const sin2 = sinTheta * sinTheta;
  return (r * r + a * a + 2.0 * m * r * a * a * sin2 / sigma -
          lambda * r * r * r * r * sin2 / 3.0) *
         sin2;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @return g_tφ component
 */
[[nodiscard]] inline double kdsGTph(double r, double theta, double m, double a) noexcept {
  double const sigma = kdsSigma(r, theta, a);
  double const sinTheta = std::sin(theta);
  return -2.0 * m * r * a * sinTheta * sinTheta / sigma;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return Inner horizon radius
 */
[[nodiscard]] inline double kdsInnerHorizon(double m, double a, double lambda) noexcept {
  double const delta = std::sqrt(m * m - a * a);
  double const rKerr = m - delta;
  return rKerr - lambda * rKerr * rKerr * rKerr / 3.0;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return Event horizon radius
 */
[[nodiscard]] inline double kdsEventHorizon(double m, double a, double lambda) noexcept {
  double const delta = std::sqrt(m * m - a * a);
  double const rKerr = m + delta;
  return rKerr + lambda * rKerr * rKerr * rKerr / 3.0;
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
 * @param lambda Cosmological constant (must be > 0)
 * @return Cosmological horizon radius
 */
[[nodiscard]] inline double kdsCosmologicalHorizon(double lambda) noexcept {
  return std::sqrt(3.0 / lambda);
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant (currently unused in approximation)
 * @return Ergosphere radius at angle theta
 */
[[nodiscard]] inline double kdsErgosphereRadius(double theta, double m, double a,
                                                double lambda) noexcept {
  (void)lambda; // Unused in this approximation
  double const cosTheta = std::cos(theta);
  return m + std::sqrt(m * m - a * a * cosTheta * cosTheta);
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return Frame dragging angular velocity
 */
[[nodiscard]] inline double kdsFrameDraggingOmega(double r, double theta, double m, double a,
                                                  double lambda) noexcept {
  double const gTph = kdsGTph(r, theta, m, a);
  double const gPhph = kdsGPhph(r, theta, m, a, lambda);
  return -gTph / gPhph;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return true if parameters are physical
 */
[[nodiscard]] constexpr bool isPhysicalKdsBlackHole(double m, double a, double lambda) noexcept {
  return m > 0.0 && lambda > 0.0 && m * m >= a * a;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return true if in exterior region
 */
[[nodiscard]] inline bool isExteriorRegion(double r, double m, double a, double lambda) noexcept {
  double const rPlus = kdsEventHorizon(m, a, lambda);
  double const rCosmo = kdsCosmologicalHorizon(lambda);
  return r > rPlus && r < rCosmo;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return true if in ergosphere
 */
[[nodiscard]] inline bool isInErgosphere(double r, double theta, double m, double a,
                                         double lambda) noexcept {
  return kdsGTt(r, theta, m, a, lambda) > 0.0;
}

// ============================================================================
// Horizon Ordering Verification
// ============================================================================

/**
 * @brief Verify that horizons are properly ordered: r₋ < r₊ < r_c
 *
 * For physical Kerr-de Sitter black holes, horizons must satisfy this ordering.
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @param lambda Cosmological constant
 * @return true if horizon ordering is correct
 */
[[nodiscard]] inline bool verifyHorizonOrdering(double m, double a, double lambda) noexcept {
  if (!isPhysicalKdsBlackHole(m, a, lambda)) {
    return false;
  }
  double const rMinus = kdsInnerHorizon(m, a, lambda);
  double const rPlus = kdsEventHorizon(m, a, lambda);
  double const rCosmo = kdsCosmologicalHorizon(lambda);
  return rMinus < rPlus && rPlus < rCosmo;
}

// ============================================================================
// Reduction to Kerr and de Sitter Limits
// ============================================================================

/**
 * @brief Check if parameters are in Kerr limit (Lambda ≈ 0)
 *
 * When Lambda is negligible, Kerr-de Sitter reduces to standard Kerr metric.
 *
 * @param lambda Cosmological constant
 * @param tolerance Tolerance for Lambda (default: 1e-10)
 * @return true if in Kerr limit
 */
[[nodiscard]] constexpr bool isKerrLimit(double lambda, double tolerance = 1e-10) noexcept {
  return std::abs(lambda) < tolerance;
}

/**
 * @brief Check if parameters are in de Sitter limit (M ≈ 0, a ≈ 0)
 *
 * When mass and spin are negligible, Kerr-de Sitter reduces to pure de Sitter spacetime.
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @param tolerance Tolerance for M and a (default: 1e-10)
 * @return true if in de Sitter limit
 */
[[nodiscard]] constexpr bool isDeSitterLimit(double m, double a,
                                             double tolerance = 1e-10) noexcept {
  return std::abs(m) < tolerance && std::abs(a) < tolerance;
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
 * @param LambdaSI Cosmological constant in SI units (m⁻²)
 * @return Cosmological constant in geometric units
 */
[[nodiscard]] constexpr double lambdaSiToGeometric(double lambdaSi) noexcept {
  // c²/G ≈ 1.346e27 m/kg in SI units
  // In geometric units where c = G = 1, this is just Lambda_SI
  // but we include this function for dimensional clarity
  return lambdaSi;
}

/**
 * @brief Observed cosmological constant in geometric units
 *
 * Λ ≈ 1.1 × 10⁻⁵² m⁻² (Planck 2018 results)
 *
 * @return Observed Lambda in geometric units
 */
[[nodiscard]] constexpr double observedLambda() noexcept {
  return 1.1e-52; // m⁻² in geometric units
}

// ============================================================================
// Phase 9.3.2 Completion
// ============================================================================

/**
 * The maintained C++ functions supply the GLSL transpiler input for
 * kerr_de_sitter.glsl. C++ tests check selected analytic limits.
 *
 * GLSL translation: scripts/cpp_to_glsl.py
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
