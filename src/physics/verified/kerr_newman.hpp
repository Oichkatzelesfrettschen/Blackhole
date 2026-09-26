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
 *        - (2a (2Mr - Q^2) sin^2 theta / Sigma) dt dphi
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
 *   A_mu = -(Qr / Sigma) (dt - a sin^2 theta dphi)_mu
 *        = (-Qr / Sigma, 0, 0, +Qra sin^2 theta / Sigma)
 * The ratio A_phi / A_t = -a sin^2 theta is fixed by the Carter form of the
 * metric; physics::knMagneticPotentialPhi uses the same sign.
 *
 * Signed spin: a > 0 rotates about +z. "Prograde" names an orbit with angular
 * momentum along +z, so a prograde orbit at a < 0 counter-rotates with the
 * hole and knIscoRadiusPrograde(m, a, q) == knIscoRadiusRetrograde(m, -a, q).
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
#include <limits>

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
 * @brief Horizon discriminant M^2 - a^2 - Q^2, with rounding-level negatives read as zero
 *
 * The sequential subtraction rounds each term, so extremal inputs such as
 * M = 1, a = 0.6, Q = 0.8 (a^2 + Q^2 = M^2 exactly in the reals) evaluate to
 * -1.1e-16. A negative value within 4 epsilon of M^2 + a^2 + Q^2, the
 * magnitude of the terms, returns as exactly 0, so r_+ = r_- = M there; a
 * larger negative value marks a super-extremal input and passes through.
 * Every square root of this discriminant in the header goes through it.
 *
 * @param m Black hole mass
 * @param a Spin parameter (a cos(theta) for the ergosurface)
 * @param q Electric charge
 * @return M^2 - a^2 - Q^2, or 0 within rounding of zero
 */
[[nodiscard]] constexpr double knHorizonDiscriminant(double m, double a, double q) noexcept {
  const double discriminant = (m * m) - (a * a) - (q * q);
  const double roundingBound =
      4.0 * std::numeric_limits<double>::epsilon() * ((m * m) + (a * a) + (q * q));
  return (discriminant < 0.0 && -discriminant <= roundingBound) ? 0.0 : discriminant;
}

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
  return m + std::sqrt(knHorizonDiscriminant(m, a, q));
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
  return m - std::sqrt(knHorizonDiscriminant(m, a, q));
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
 * @brief Azimuthal component of electromagnetic 4-potential: A_phi = +Qra sin^2(theta) / Sigma
 *
 * Derived from Rocq: Definition kn_potential_phi (r theta a Q : R) : R :=
 *   Q * r * a * (sin theta)^2 / kn_Sigma r theta a.
 *
 * A_phi = -a sin^2(theta) A_t, the ratio carried by (dt - a sin^2 theta dphi).
 * The Einstein-Maxwell check in tests/kerr_newman_test.cpp fails R_tphi when
 * this sign flips relative to A_t.
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
  return q * r * a * sinTheta * sinTheta / sigma;
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
  return m + std::sqrt(knHorizonDiscriminant(m, a * cosTheta, q));
}

// ============================================================================
// Frame Dragging (from Rocq: kn_frame_dragging_omega)
// ============================================================================

/**
 * @brief Frame dragging angular velocity omega = -g_tphi / g_phph = a (2Mr - Q^2) / A
 *
 * Derived from Rocq: Definition kn_frame_dragging_omega (r theta M a Q : R) : R :=
 *   let A := kn_A r theta M a Q in
 *   a * (2 * M * r - Q^2) / A.
 *
 * This is the angular velocity of a zero-angular-momentum observer. The
 * charge enters both through Delta inside A and through the 2Mr - Q^2 factor
 * of g_tphi.
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
  return a * (2.0 * m * r - q * q) / metricFactor;
}

// ============================================================================
// Photon Orbit (from Rocq: kn_photon_orbit_function, kn_photon_sphere_equator_spec)
// ============================================================================

/**
 * @brief Circular-photon-orbit function of the equatorial KN metric
 *
 * Derived from Rocq: Definition kn_photon_orbit_function (r M a Q : R) : R :=
 *   r^2 - 3 * M * r + 2 * Q^2 + 2 * a * sqrt (M * r - Q^2).
 *
 * Timelike circular orbits with angular momentum along +z (signed a) have
 * u^t proportional to 1 / sqrt(f(r)); the orbit becomes null where f = 0. At
 * Q = 0 this is r^2 - 3Mr + 2a sqrt(Mr), whose root is the Bardeen-Press-
 * Teukolsky photon orbit 2M(1 + cos((2/3) acos(-a/M))); at a = 0 the root is
 * (3M + sqrt(9M^2 - 8Q^2)) / 2. f is positive outside the photon orbit.
 *
 * @param r Radial coordinate (requires M r >= Q^2)
 * @param m Black hole mass
 * @param a Signed spin parameter
 * @param q Electric charge
 * @return Photon-orbit function value
 */
[[nodiscard]] inline double knPhotonOrbitFunction(double r, double m, double a,
                                                  double q) noexcept {
  return r * r - 3.0 * m * r + 2.0 * q * q + 2.0 * a * std::sqrt(m * r - q * q);
}

/**
 * @brief Equatorial circular photon orbit with angular momentum along +z
 *
 * Derived from Rocq: Definition kn_photon_sphere_equator_spec (M a Q r : R) : Prop :=
 *   kn_photon_orbit_function r M a Q = 0 /\
 *   forall r', r' > r -> kn_photon_orbit_function r' M a Q > 0.
 *
 * The outermost zero of knPhotonOrbitFunction. The search starts at 5 M,
 * above the largest photon orbit of the family (4 M at a = -M, Q = 0), steps
 * inward by M/200 until f turns non-positive, and bisects to 1e-15 M. The
 * floor is max(r_+, Q^2/M); when f stays positive to the floor (extremal
 * limits) the floor is returned. A super-extremal or massless input returns
 * NaN. The retrograde orbit is knPhotonSphereEquator(m, -a, q).
 *
 * @param m Black hole mass (> 0)
 * @param a Signed spin parameter; a < 0 gives the counter-rotating orbit
 * @param q Electric charge
 * @return Photon orbit radius, or NaN when m <= 0 or a^2 + q^2 > m^2
 */
[[nodiscard]] inline double knPhotonSphereEquator(double m, double a, double q) noexcept {
  const double discriminant = knHorizonDiscriminant(m, a, q);
  if (!(m > 0.0) || discriminant < 0.0) {
    return std::nan("");
  }
  const double rFloor = std::fmax(m + std::sqrt(discriminant), q * q / m);
  const double step = 0.005 * m;
  double rOuter = 5.0 * m;
  double rInner = rOuter;
  bool bracketed = false;
  while (rOuter - step > rFloor) {
    rInner = rOuter - step;
    if (knPhotonOrbitFunction(rInner, m, a, q) <= 0.0) {
      bracketed = true;
      break;
    }
    rOuter = rInner;
  }
  if (!bracketed) {
    rInner = rFloor;
    if (knPhotonOrbitFunction(rInner, m, a, q) > 0.0) {
      return rFloor;
    }
  }
  // Invariant: f(rInner) <= 0 < f(rOuter).
  for (int iteration = 0; iteration < 200 && rOuter - rInner > 1.0e-15 * m; ++iteration) {
    const double rMid = 0.5 * (rInner + rOuter);
    if (knPhotonOrbitFunction(rMid, m, a, q) <= 0.0) {
      rInner = rMid;
    } else {
      rOuter = rMid;
    }
  }
  return 0.5 * (rInner + rOuter);
}

// ============================================================================
// ISCO - marginal stability of equatorial circular orbits (from Rocq: kn_isco_*)
// ============================================================================

/**
 * @brief Marginal-stability function of equatorial KN circular orbits
 *
 * Derived from Rocq: Definition kn_marginal_stability (r M a Q : R) : R :=
 *   r * (6 * M * r - r^2 - 9 * Q^2 + 3 * a^2) + 4 * Q^2 * (Q^2 - a^2) / M
 *   - 8 * a * (sqrt (M * r - Q^2))^3 / M.
 *
 * Zeros of this function are the radii where dE/dr = 0 for the circular-orbit
 * energy E(r) of the equatorial KN metric, with the orbit angular momentum
 * along +z (signed a). It is negative for large r, where circular orbits are
 * stable. At a = 0 it is -(r^3 - 6Mr^2 + 9Q^2 r - 4Q^4/M), the
 * Reissner-Nordstrom ISCO cubic; at Q = 0 it is -r (r^2 - 6Mr + 8a sqrt(Mr)
 * - 3a^2), the Bardeen-Press-Teukolsky condition. scripts/gen_kn_kds_reference.py
 * checks the zeros against a direct dE/dr = 0 root of the Carter-form metric.
 *
 * @param r Radial coordinate (requires M r >= Q^2)
 * @param m Black hole mass
 * @param a Signed spin parameter
 * @param q Electric charge
 * @return Marginal-stability function value
 */
[[nodiscard]] inline double knIscoMarginalStability(double r, double m, double a,
                                                    double q) noexcept {
  const double q2 = q * q;
  const double orbitTerm = m * r - q2;
  const double orbitRoot = std::sqrt(orbitTerm);
  return r * (6.0 * m * r - r * r - 9.0 * q2 + 3.0 * a * a) + 4.0 * q2 * (q2 - a * a) / m -
         8.0 * a * orbitTerm * orbitRoot / m;
}

/**
 * @brief ISCO radius for an equatorial orbit with angular momentum along +z
 *
 * Derived from Rocq: Definition kn_isco_prograde_spec (M a Q r : R) : Prop :=
 *   kn_marginal_stability r M a Q = 0 /\
 *   forall r', r' > r -> kn_marginal_stability r' M a Q < 0.
 *
 * The ISCO is the outermost zero of knIscoMarginalStability. The search starts
 * at 10 M, above the largest ISCO of the family (9 M at a = -M, Q = 0), steps
 * inward by M/200 until the function turns non-negative, and bisects the
 * bracket to a width of 1e-15 M. The search floor is max(r_+, Q^2/M): circular
 * orbits need M r > Q^2, and every exterior orbit lies above r_+. When the
 * function stays negative down to the floor, as at extremality, the floor is
 * the ISCO. A super-extremal or massless input returns NaN.
 *
 * @param m Black hole mass (> 0)
 * @param a Signed spin parameter; a < 0 gives the counter-rotating ISCO
 * @param q Electric charge
 * @return ISCO radius, or NaN when m <= 0 or a^2 + q^2 > m^2
 */
[[nodiscard]] inline double knIscoRadiusPrograde(double m, double a, double q) noexcept {
  const double discriminant = knHorizonDiscriminant(m, a, q);
  if (!(m > 0.0) || discriminant < 0.0) {
    return std::nan("");
  }
  const double rFloor = std::fmax(m + std::sqrt(discriminant), q * q / m);
  const double step = 0.005 * m;
  double rOuter = 10.0 * m;
  double rInner = rOuter;
  bool bracketed = false;
  while (rOuter - step > rFloor) {
    rInner = rOuter - step;
    if (knIscoMarginalStability(rInner, m, a, q) >= 0.0) {
      bracketed = true;
      break;
    }
    rOuter = rInner;
  }
  if (!bracketed) {
    rInner = rFloor;
    if (knIscoMarginalStability(rInner, m, a, q) < 0.0) {
      return rFloor;
    }
  }
  // Invariant: f(rInner) >= 0 > f(rOuter).
  for (int iteration = 0; iteration < 200 && rOuter - rInner > 1.0e-15 * m; ++iteration) {
    const double rMid = 0.5 * (rInner + rOuter);
    if (knIscoMarginalStability(rMid, m, a, q) >= 0.0) {
      rInner = rMid;
    } else {
      rOuter = rMid;
    }
  }
  return 0.5 * (rInner + rOuter);
}

/**
 * @brief ISCO radius for an equatorial orbit with angular momentum along -z
 *
 * Derived from Rocq: Definition kn_isco_retrograde_spec (M a Q r : R) : Prop :=
 *   kn_isco_prograde_spec M (- a) Q r.
 *
 * Reflecting phi -> -phi maps a -> -a and leaves Q unchanged, so the
 * retrograde ISCO at spin a is the prograde ISCO at spin -a.
 *
 * @param m Black hole mass
 * @param a Signed spin parameter
 * @param q Electric charge
 * @return Retrograde ISCO radius
 */
[[nodiscard]] inline double knIscoRadiusRetrograde(double m, double a, double q) noexcept {
  return knIscoRadiusPrograde(m, -a, q);
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
 * @brief Kerr-Newman g_tph (cross term): g_tph = -a (2Mr - Q^2) sin^2(theta) / Sigma
 *
 * Derived from Rocq: g_tph := - a * (2 * M * r - Q^2) * sin2 / Sigma
 * Expanding the Carter form -(Delta/Sigma)(dt - a sin^2 dphi)^2
 * + (sin^2/Sigma)((r^2 + a^2) dphi - a dt)^2 gives
 * g_tph = a sin^2 (Delta - r^2 - a^2) / Sigma, so the charge enters here.
 */
[[nodiscard]] inline double knGTph(double r, double theta, double m, double a,
                                   double q) noexcept {
  const double sigma = knSigma(r, theta, a);
  const double sinTheta = std::sin(theta);
  return -a * (2.0 * m * r - q * q) * sinTheta * sinTheta / sigma;
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
 * M^2 >= a^2 + Q^2 is read through knHorizonDiscriminant, so an input whose
 * discriminant rounds to within 4 epsilon below zero counts as extremal and
 * agrees with the horizon and orbit functions.
 *
 * @param m Black hole mass
 * @param a Spin parameter
 * @param q Electric charge
 * @return true if physical black hole
 */
[[nodiscard]] constexpr bool isPhysicalBlackHole(double m, double a, double q) noexcept {
  return m > 0.0 && knHorizonDiscriminant(m, a, q) >= 0.0;
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
