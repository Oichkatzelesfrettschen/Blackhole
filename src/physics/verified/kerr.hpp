/**
 * @file verified/kerr.hpp
 * @brief Verified Kerr metric functions - derived from Rocq formalization
 *
 * Maintained C++ reference for rocq/theories/Metrics/Kerr.v
 * Analytical reference: Bardeen-Press-Teukolsky (1972).
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
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
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
[[nodiscard]] inline double kerrSigma(double r, double theta, double a) noexcept {
  const double cosTheta = std::cos(theta);
  return r * r + a * a * cosTheta * cosTheta;
}

/**
 * @brief Delta = r^2 - 2Mr + a^2
 *
 * Derived from Rocq: Definition kerr_Delta (r M a : R) : R :=
 *   r^2 - 2 * M * r + a^2.
 *
 * @param r Radial coordinate
 * @param m Black hole mass
 * @param a Spin parameter (J/M)
 * @return Delta
 */
[[nodiscard]] constexpr double kerrDelta(double r, double m, double a) noexcept {
  return r * r - 2.0 * m * r + a * a;
}

/**
 * @brief A = (r^2 + a^2)^2 - a^2 Delta sin^2(theta)
 *
 * Derived from Rocq: Definition kerr_A (r theta M a : R) : R :=
 *   (r^2 + a^2)^2 - a^2 * kerr_Delta r M a * (sin theta)^2.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param m Black hole mass
 * @param a Spin parameter
 * @return A
 */
[[nodiscard]] inline double kerrA(double r, double theta, double m, double a) noexcept {
  const double r2PlusA2 = r * r + a * a;
  const double sinTheta = std::sin(theta);
  const double delta = kerrDelta(r, m, a);
  return r2PlusA2 * r2PlusA2 - a * a * delta * sinTheta * sinTheta;
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
 * @param m Black hole mass
 * @param a Spin parameter (|a| <= M for horizon to exist)
 * @return r_+ outer horizon radius
 */
[[nodiscard]] inline double outerHorizon(double m, double a) noexcept {
  return m + std::sqrt(m * m - a * a);
}

/**
 * @brief Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2)
 *
 * Derived from Rocq: Definition inner_horizon (M a : R) : R :=
 *   M - sqrt (M^2 - a^2).
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @return r_- inner horizon radius
 */
[[nodiscard]] inline double innerHorizon(double m, double a) noexcept {
  return m - std::sqrt(m * m - a * a);
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @return Ergosphere radius at angle theta
 */
[[nodiscard]] inline double ergosphereRadius(double theta, double m, double a) noexcept {
  const double cosTheta = std::cos(theta);
  return m + std::sqrt(m * m - a * a * cosTheta * cosTheta);
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @return Frame dragging angular velocity
 */
[[nodiscard]] inline double frameDraggingOmega(double r, double theta, double m,
                                               double a) noexcept {
  const double metricFactor = kerrA(r, theta, m, a);
  return 2.0 * m * r * a / metricFactor;
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
[[nodiscard]] inline double kerrZ1(double m, double a) noexcept {
  const double aOverM = a / m;
  const double oneMinusA2M2 = 1.0 - aOverM * aOverM;
  const double cbrtFactor = std::cbrt(oneMinusA2M2);
  const double cbrtPlus = std::cbrt(1.0 + aOverM);
  const double cbrtMinus = std::cbrt(1.0 - aOverM);
  return 1.0 + cbrtFactor * (cbrtPlus + cbrtMinus);
}

/**
 * @brief Z2 helper for ISCO calculation
 *
 * Derived from Rocq: Definition Z2 (M a : R) : R :=
 *   sqrt (3 * a^2 / M^2 + (Z1 M a)^2).
 */
[[nodiscard]] inline double kerrZ2(double m, double a) noexcept {
  const double aOverM = a / m;
  const double z1 = kerrZ1(m, a);
  return std::sqrt(3.0 * aOverM * aOverM + z1 * z1);
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
 * Signed spin, shared with photonOrbitPrograde and physics::kerrIscoRadius:
 * a > 0 rotates about +z and "prograde" names an orbit with angular momentum
 * along +z, so at a < 0 the prograde orbit counter-rotates and takes the plus
 * sign (8.7174 M at a = -0.9 M). The Rocq definition states the a >= 0 form;
 * Z1 and Z2 are even in a, and the sign of the square-root term carries the
 * reflection phi -> -phi.
 *
 * @param m Black hole mass
 * @param a Signed spin parameter
 * @return ISCO radius for angular momentum along +z
 */
[[nodiscard]] inline double kerrIscoPrograde(double m, double a) noexcept {
  const double z1 = kerrZ1(m, a);
  const double z2 = kerrZ2(m, a);
  const double sqrtTerm = std::sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2));
  return (a >= 0.0) ? m * (3.0 + z2 - sqrtTerm) : m * (3.0 + z2 + sqrtTerm);
}

/**
 * @brief Retrograde ISCO radius (Bardeen-Press-Teukolsky formula)
 *
 * Derived from Rocq: Definition kerr_isco_retrograde (M a : R) : R :=
 *   M * (3 + Z2 M a + sqrt ((3 - Z1 M a) * (3 + Z1 M a + 2 * Z2 M a))).
 *
 * For a = M: r_ISCO = 9M (extremal retrograde)
 *
 * Signed spin: the orbit with angular momentum along -z, equal to
 * kerrIscoPrograde(m, -a).
 *
 * @param m Black hole mass
 * @param a Signed spin parameter
 * @return ISCO radius for angular momentum along -z
 */
[[nodiscard]] inline double kerrIscoRetrograde(double m, double a) noexcept {
  return kerrIscoPrograde(m, -a);
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
 * Signed spin as in kerrIscoPrograde: angular momentum along +z.
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @return Prograde photon orbit radius
 */
[[nodiscard]] inline double photonOrbitPrograde(double m, double a) noexcept {
  return 2.0 * m * (1.0 + std::cos((2.0 / 3.0) * std::acos(-a / m)));
}

/**
 * @brief Retrograde photon orbit radius
 *
 * Derived from Rocq: Definition photon_orbit_retrograde (M a : R) : R :=
 *   2 * M * (1 + cos ((2/3) * acos (a / M))).
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @return Retrograde photon orbit radius
 */
[[nodiscard]] inline double photonOrbitRetrograde(double m, double a) noexcept {
  return 2.0 * m * (1.0 + std::cos((2.0 / 3.0) * std::acos(a / m)));
}

// ============================================================================
// Metric Components (from Rocq: kerr_metric, kerr_g_*)
// ============================================================================

/**
 * @brief Kerr g_tt component: g_tt = -(1 - 2Mr/Sigma)
 *
 * Derived from Rocq: kerr_metric returns mkMetric(-(1 - 2 * M * r / Sigma)...)
 */
[[nodiscard]] inline double kerrGTt(double r, double theta, double m, double a) noexcept {
  const double sigma = kerrSigma(r, theta, a);
  return -(1.0 - 2.0 * m * r / sigma);
}

/**
 * @brief Kerr g_rr component: g_rr = Sigma / Delta
 *
 * Derived from Rocq: g_rr := Sigma / Delta
 */
[[nodiscard]] inline double kerrGRr(double r, double theta, double m, double a) noexcept {
  const double sigma = kerrSigma(r, theta, a);
  const double delta = kerrDelta(r, m, a);
  return sigma / delta;
}

/**
 * @brief Kerr g_thth component: g_thth = Sigma
 *
 * Derived from Rocq: g_thth := Sigma
 */
[[nodiscard]] inline double kerrGThth(double r, double theta, double a) noexcept {
  return kerrSigma(r, theta, a);
}

/**
 * @brief Kerr g_phph component: g_phph = A sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_phph := A * sin2 / Sigma
 */
[[nodiscard]] inline double kerrGPhph(double r, double theta, double m, double a) noexcept {
  const double sigma = kerrSigma(r, theta, a);
  const double metricFactor = kerrA(r, theta, m, a);
  const double sinTheta = std::sin(theta);
  return metricFactor * sinTheta * sinTheta / sigma;
}

/**
 * @brief Kerr g_tph (cross term): g_tph = -2Mar sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_tph := - 2 * M * r * a * sin2 / Sigma
 * This is the frame dragging term.
 */
[[nodiscard]] inline double kerrGTph(double r, double theta, double m, double a) noexcept {
  const double sigma = kerrSigma(r, theta, a);
  const double sinTheta = std::sin(theta);
  return -2.0 * m * r * a * sinTheta * sinTheta / sigma;
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
[[nodiscard]] inline double kerrChristoffelTTr(double r, double theta, double m,
                                               double a) noexcept {
  const double sigma = kerrSigma(r, theta, a);
  const double delta = kerrDelta(r, m, a);
  const double cosTheta = std::cos(theta);
  const double r2MinusA2cos2 = r * r - a * a * cosTheta * cosTheta;
  const double r2PlusA2 = r * r + a * a;
  return m * r2MinusA2cos2 / (sigma * sigma * delta) * r2PlusA2;
}

/**
 * @brief Kerr Gamma^r_{tt}
 *
 * Derived from Rocq: Definition kerr_christoffel_r_tt (r theta M a : R) : R :=
 *   let Sigma := kerr_Sigma r theta a in
 *   let Delta := kerr_Delta r M a in
 *   M * Delta * (r^2 - a^2 * (cos theta)^2) / Sigma^3.
 */
[[nodiscard]] inline double kerrChristoffelRTt(double r, double theta, double m,
                                               double a) noexcept {
  const double sigma = kerrSigma(r, theta, a);
  const double delta = kerrDelta(r, m, a);
  const double cosTheta = std::cos(theta);
  const double r2MinusA2cos2 = r * r - a * a * cosTheta * cosTheta;
  const double sigma3 = sigma * sigma * sigma;
  return m * delta * r2MinusA2cos2 / sigma3;
}

// ============================================================================
// Helper Functions for Validation
// ============================================================================

/**
 * @brief Check if spin parameter is sub-extremal (|a| < M)
 */
[[nodiscard]] constexpr bool isSubextremal(double m, double a) noexcept {
  return std::abs(a) < m;
}

/**
 * @brief Check if point is outside the outer horizon
 */
[[nodiscard]] inline bool outsideOuterHorizon(double r, double m, double a) noexcept {
  return r > outerHorizon(m, a);
}

/**
 * @brief Check if point is inside the ergosphere but outside the horizon
 */
[[nodiscard]] inline bool inErgosphere(double r, double theta, double m, double a) noexcept {
  return r > outerHorizon(m, a) && r < ergosphereRadius(theta, m, a);
}

/**
 * @brief Schwarzschild limit: frame dragging vanishes for a = 0
 *
 * Proven in Rocq: Theorem no_frame_dragging_schwarzschild
 */
[[nodiscard]] constexpr bool hasFrameDragging(double a) noexcept {
  return a != 0.0;
}

} // namespace verified

#endif // PHYSICS_VERIFIED_KERR_HPP
