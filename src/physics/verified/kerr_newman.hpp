/**
 * @file verified/kerr_newman.hpp
 * @brief Verified Kerr-Newman metric functions - derived from Rocq formalization
 *
 * Maintained C++ reference for rocq/theories/Metrics/KerrNewman.v
 * Analytical reference: Newman et al. (1965).
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
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
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
[[nodiscard]] inline double knSigma(double r, double theta, double a) noexcept {
  const double cosTheta = std::cos(theta);
  return r * r + a * a * cosTheta * cosTheta;
}

/**
 * @brief Delta = r^2 - 2Mr + a^2 + Q^2 - charge Q modifies Delta
 *
 * Derived from Rocq: Definition kn_Delta (r M a Q : R) : R :=
 *   r^2 - 2 * M * r + a^2 + Q^2.
 *
 * @param r Radial coordinate
 * @param m Black hole mass
 * @param a Spin parameter (J/M)
 * @param q Electric charge (geometric units)
 * @return Delta
 */
[[nodiscard]] constexpr double knDelta(double r, double m, double a, double q) noexcept {
  return r * r - 2.0 * m * r + a * a + q * q;
}

/**
 * @brief A = (r^2 + a^2)^2 - a^2 Delta sin^2(theta)
 *
 * Derived from Rocq: Definition kn_A (r theta M a Q : R) : R :=
 *   (r^2 + a^2)^2 - a^2 * kn_Delta r M a Q * (sin theta)^2.
 *
 * @param r Radial coordinate
 * @param theta Polar angle
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return A
 */
[[nodiscard]] inline double knA(double r, double theta, double m, double a, double q) noexcept {
  const double r2PlusA2 = r * r + a * a;
  const double sinTheta = std::sin(theta);
  const double delta = knDelta(r, m, a, q);
  return r2PlusA2 * r2PlusA2 - a * a * delta * sinTheta * sinTheta;
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
 * @param m Black hole mass
 * @param a Spin parameter (|a| <= M for horizon to exist)
 * @param q Electric charge
 * @return r_+ outer horizon radius
 */
[[nodiscard]] inline double knOuterHorizon(double m, double a, double q) noexcept {
  return m + std::sqrt(m * m - a * a - q * q);
}

/**
 * @brief Inner (Cauchy) horizon: r_- = M - sqrt(M^2 - a^2 - Q^2)
 *
 * Derived from Rocq: Definition kn_inner_horizon (M a Q : R) : R :=
 *   M - sqrt (M^2 - a^2 - Q^2).
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return r_- inner horizon radius
 */
[[nodiscard]] inline double knInnerHorizon(double m, double a, double q) noexcept {
  return m - std::sqrt(m * m - a * a - q * q);
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
 * @param q Electric charge
 * @return A_t
 */
[[nodiscard]] inline double knPotentialT(double r, double theta, double a, double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  return -q * r / sigma;
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
 * @param q Electric charge
 * @return A_phi
 */
[[nodiscard]] inline double knPotentialPhi(double r, double theta, double a, double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  const double sinTheta = std::sin(theta);
  return -q * r * a * sinTheta * sinTheta / sigma;
}

/**
 * @brief Radial component of electromagnetic 4-potential: A_r = 0
 *
 * Derived from Rocq: Definition kn_potential_r : R := 0.
 *
 * @return 0.0
 */
[[nodiscard]] constexpr double knPotentialR() noexcept {
  return 0.0;
}

/**
 * @brief Polar component of electromagnetic 4-potential: A_theta = 0
 *
 * Derived from Rocq: Definition kn_potential_theta : R := 0.
 *
 * @return 0.0
 */
[[nodiscard]] constexpr double knPotentialTheta() noexcept {
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
 * @param q Electric charge
 * @return E_r
 */
[[nodiscard]] inline double knElectricFieldR(double r, double theta, double a, double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  const double sigma2 = sigma * sigma;
  return -q * (sigma - 2.0 * r * r) / sigma2;
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
 * @param q Electric charge
 * @return B (magnetic field component)
 */
[[nodiscard]] inline double knMagneticField(double r, double theta, double a, double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  const double sigma2 = sigma * sigma;
  const double cosTheta = std::cos(theta);
  return q * a * cosTheta / sigma2;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return Ergosphere radius at angle theta
 */
[[nodiscard]] inline double knErgosphereRadius(double theta, double m, double a,
                                               double q) noexcept {
  const double cosTheta = std::cos(theta);
  return m + std::sqrt(m * m - a * a * cosTheta * cosTheta - q * q);
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return Frame dragging angular velocity
 */
[[nodiscard]] inline double knFrameDraggingOmega(double r, double theta, double m, double a,
                                                 double q) noexcept {
  const double metricFactor = knA(r, theta, m, a, q);
  return 2.0 * m * r * a / metricFactor;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return Approximate equatorial photon sphere radius
 */
[[nodiscard]] inline double knPhotonSphereEquator(double m, double a, double q) noexcept {
  (void)q; // Charge appears in discriminant, simplified formula uses only a/M
  return 2.0 * m * (1.0 + std::cos(std::acos(a / m) / 3.0));
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
 * @param m Black hole mass
 * @param a Spin parameter (positive for prograde)
 * @param q Electric charge
 * @return Prograde ISCO radius
 */
[[nodiscard]] inline double knIscoRadiusPrograde(double m, double a, double q) noexcept {
  const double aOverM = a / m;
  const double oneMinusA2M2 = 1.0 - aOverM * aOverM;
  const double cbrtFactor = std::cbrt(oneMinusA2M2);
  const double cbrtPlus = std::cbrt(1.0 + aOverM);
  const double cbrtMinus = std::cbrt(1.0 - aOverM);
  const double z1 = 1.0 + cbrtFactor * (cbrtPlus + cbrtMinus);
  const double z2 = std::sqrt(3.0 * aOverM * aOverM + z1 * z1);
  const double sqrtTerm = std::sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2));
  const double correction = q * q / (2.0 * m * m);
  return m * (3.0 + z2 - sqrtTerm) + correction;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return Retrograde ISCO radius
 */
[[nodiscard]] inline double knIscoRadiusRetrograde(double m, double a, double q) noexcept {
  const double aOverM = a / m;
  const double oneMinusA2M2 = 1.0 - aOverM * aOverM;
  const double cbrtFactor = std::cbrt(oneMinusA2M2);
  const double cbrtPlus = std::cbrt(1.0 + aOverM);
  const double cbrtMinus = std::cbrt(1.0 - aOverM);
  const double z1 = 1.0 + cbrtFactor * (cbrtPlus + cbrtMinus);
  const double z2 = std::sqrt(3.0 * aOverM * aOverM + z1 * z1);
  const double sqrtTerm = std::sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2));
  const double correction = q * q / (2.0 * m * m);
  return m * (3.0 + z2 + sqrtTerm) + correction;
}

// ============================================================================
// Metric Components (from Rocq: kerr_newman_metric, kn_g_*)
// ============================================================================

/**
 * @brief Kerr-Newman g_tt component: g_tt = -(1 - (2Mr - Q^2)/Sigma)
 *
 * Derived from Rocq: kerr_newman_metric returns mkMetric(-(1 - (2 * M * r - Q^2) / Sigma)...)
 */
[[nodiscard]] inline double knGTt(double r, double theta, double m, double a, double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  return -(1.0 - (2.0 * m * r - q * q) / sigma);
}

/**
 * @brief Kerr-Newman g_rr component: g_rr = Sigma / Delta
 *
 * Derived from Rocq: g_rr := Sigma / Delta
 */
[[nodiscard]] inline double knGRr(double r, double theta, double m, double a, double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  const double delta = knDelta(r, m, a, q);
  return sigma / delta;
}

/**
 * @brief Kerr-Newman g_thth component: g_thth = Sigma
 *
 * Derived from Rocq: g_thth := Sigma
 */
[[nodiscard]] inline double knGThth(double r, double theta, double a) noexcept {
  return knSigma(r, theta, a);
}

/**
 * @brief Kerr-Newman g_phph component: g_phph = A sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_phph := A * sin2 / Sigma
 */
[[nodiscard]] inline double knGPhph(double r, double theta, double m, double a, double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  const double metricFactor = knA(r, theta, m, a, q);
  const double sinTheta = std::sin(theta);
  return metricFactor * sinTheta * sinTheta / sigma;
}

/**
 * @brief Kerr-Newman g_tph (cross term): g_tph = -2Mar sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_tph := - 2 * M * r * a * sin2 / Sigma
 * This is the frame dragging term (unchanged from Kerr).
 */
[[nodiscard]] inline double knGTph(double r, double theta, double m, double a) noexcept {
  const double sigma = knSigma(r, theta, a);
  const double sinTheta = std::sin(theta);
  return -2.0 * m * r * a * sinTheta * sinTheta / sigma;
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
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return true if sub-extremal
 */
[[nodiscard]] constexpr bool isSubExtremal(double m, double a, double q) noexcept {
  return m * m > a * a + q * q;
}

/**
 * @brief Extremal condition: M^2 = a^2 + Q^2 (horizons coincide)
 *
 * Derived from Rocq: Definition is_extremal (M a Q : R) : Prop :=
 *   M^2 = a^2 + Q^2.
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return true if extremal
 */
[[nodiscard]] constexpr bool isExtremal(double m, double a, double q) noexcept {
  return m * m == a * a + q * q;
}

/**
 * @brief Super-extremal (unphysical): M^2 < a^2 + Q^2
 *
 * Derived from Rocq: Definition is_super_extremal (M a Q : R) : Prop :=
 *   M^2 < a^2 + Q^2.
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return true if super-extremal (naked singularity)
 */
[[nodiscard]] constexpr bool isSuperExtremal(double m, double a, double q) noexcept {
  return m * m < a * a + q * q;
}

/**
 * @brief Physical black hole must be sub-extremal or extremal
 *
 * Derived from Rocq: Definition is_physical_black_hole (M a Q : R) : Prop :=
 *   M > 0 /\ M^2 >= a^2 + Q^2.
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return true if physical black hole
 */
[[nodiscard]] constexpr bool isPhysicalBlackHole(double m, double a, double q) noexcept {
  return m > 0.0 && m * m >= a * a + q * q;
}

// ============================================================================
// Helper Functions for Validation
// ============================================================================

/**
 * @brief Check if point is outside the outer horizon
 */
[[nodiscard]] inline bool outsideOuterHorizon(double r, double m, double a, double q) noexcept {
  return r > knOuterHorizon(m, a, q);
}

/**
 * @brief Check if point is inside the ergosphere but outside the horizon
 */
[[nodiscard]] inline bool inErgosphere(double r, double theta, double m, double a,
                                       double q) noexcept {
  return r > knOuterHorizon(m, a, q) && r < knErgosphereRadius(theta, m, a, q);
}

/**
 * @brief Kerr limit: Kerr-Newman with Q = 0 reduces to Kerr
 *
 * Proven in Rocq: Theorem kn_reduces_to_kerr
 */
[[nodiscard]] constexpr bool isKerrLimit(double q) noexcept {
  return q == 0.0;
}

/**
 * @brief Schwarzschild limit: Kerr-Newman with a = 0, Q = 0 reduces to Schwarzschild
 *
 * Proven in Rocq: Theorem kn_reduces_to_schwarzschild
 */
[[nodiscard]] constexpr bool isSchwarzschildLimit(double a, double q) noexcept {
  return a == 0.0 && q == 0.0;
}

} // namespace verified

#endif // PHYSICS_VERIFIED_KERR_NEWMAN_HPP
