/**
 * @file verified/kerr_de_sitter.hpp
 * @brief Verified Kerr-de Sitter metric - rotating black hole with cosmological constant
 *
 * Maintained C++ reference for rocq/theories/Metrics/KerrDeSitter.v
 *
 * Carter (1968) form in Boyer-Lindquist coordinates (Griffiths & Podolsky 2009),
 * geometric units c = G = 1:
 *
 *   ds^2 = -(Delta_r / (Xi^2 Sigma)) (dt - a sin^2 theta dphi)^2
 *        + (Delta_theta sin^2 theta / (Xi^2 Sigma)) (a dt - (r^2 + a^2) dphi)^2
 *        + (Sigma / Delta_r) dr^2 + (Sigma / Delta_theta) dtheta^2
 *
 *   Sigma       = r^2 + a^2 cos^2 theta
 *   Delta_r     = (r^2 + a^2)(1 - Lambda r^2 / 3) - 2 M r
 *   Delta_theta = 1 + Lambda a^2 cos^2 theta / 3
 *   Xi          = 1 + Lambda a^2 / 3
 *
 * The metric satisfies R_mu_nu = Lambda g_mu_nu; tests/kerr_de_sitter_test.cpp
 * checks that with a finite-difference Ricci oracle. At a = 0 it is
 * Schwarzschild-de Sitter, g_tt = -(1 - 2M/r - Lambda r^2/3); at Lambda = 0 it
 * is Kerr.
 *
 * Horizons are the positive roots of the quartic Delta_r. For Lambda > 0 and
 * M > 0 in the black-hole range there are three: r_- (Cauchy) < r_+ (event)
 * < r_c (cosmological). The solver brackets each root between the positive
 * stationary points of Delta_r, which a trigonometric cubic formula gives in
 * closed form, and bisects. This holds for Lambda from 1e-10 (r_c ~ 1.7e5 M)
 * through the Nariai limit, where r_+ and r_c merge and the functions return
 * NaN.
 *
 * Signed spin: a > 0 rotates about +z. Every function here depends on a^2 or
 * on a in the frame-dragging terms only.
 *
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
 *
 * References:
 * - Carter, B. (1968). Commun. Math. Phys. 10, 280
 * - Griffiths, J. B. & Podolsky, J. (2009). Exact Space-Times in Einstein's
 *   General Relativity, Cambridge University Press
 */

#ifndef PHYSICS_VERIFIED_KERR_DE_SITTER_HPP
#define PHYSICS_VERIFIED_KERR_DE_SITTER_HPP

#include <cmath>
#include <limits>
#include <numbers>

namespace verified {

// ============================================================================
// Carter-form metric functions (from Rocq: kds_Sigma, kds_Delta, kds_Delta_theta, kds_Xi, kds_A)
// ============================================================================

/**
 * @brief Sigma = r^2 + a^2 cos^2(theta)
 *
 * Derived from Rocq: Definition kds_Sigma (r theta a : R) : R :=
 *   r^2 + a^2 * (cos theta)^2.
 */
[[nodiscard]] inline double kdsSigma(double r, double theta, double a) noexcept {
  double const cosTheta = std::cos(theta);
  return r * r + a * a * cosTheta * cosTheta;
}

/**
 * @brief Radial function Delta_r = (r^2 + a^2)(1 - Lambda r^2 / 3) - 2 M r
 *
 * Derived from Rocq: Definition kds_Delta (r M a Lambda : R) : R :=
 *   (r^2 + a^2) * (1 - Lambda * r^2 / 3) - 2 * M * r.
 *
 * A quartic in r whose positive roots are the horizons.
 */
[[nodiscard]] constexpr double kdsDelta(double r, double m, double a, double lambda) noexcept {
  return (r * r + a * a) * (1.0 - lambda * r * r / 3.0) - 2.0 * m * r;
}

/**
 * @brief Polar function Delta_theta = 1 + Lambda a^2 cos^2(theta) / 3
 *
 * Derived from Rocq: Definition kds_Delta_theta (theta a Lambda : R) : R :=
 *   1 + Lambda * a^2 * (cos theta)^2 / 3.
 */
[[nodiscard]] inline double kdsDeltaTheta(double theta, double a, double lambda) noexcept {
  double const cosTheta = std::cos(theta);
  return 1.0 + lambda * a * a * cosTheta * cosTheta / 3.0;
}

/**
 * @brief Xi = 1 + Lambda a^2 / 3, the normalization of the Carter time and azimuth
 *
 * Derived from Rocq: Definition kds_Xi (a Lambda : R) : R := 1 + Lambda * a^2 / 3.
 */
[[nodiscard]] constexpr double kdsXi(double a, double lambda) noexcept {
  return 1.0 + lambda * a * a / 3.0;
}

/**
 * @brief A = Delta_theta (r^2 + a^2)^2 - Delta_r a^2 sin^2(theta)
 *
 * Derived from Rocq: Definition kds_A (r theta M a Lambda : R) : R :=
 *   kds_Delta_theta theta a Lambda * (r^2 + a^2)^2
 *   - kds_Delta r M a Lambda * a^2 * (sin theta)^2.
 *
 * At Lambda = 0 this is the Kerr A.
 */
[[nodiscard]] inline double kdsA(double r, double theta, double m, double a,
                                 double lambda) noexcept {
  double const r2PlusA2 = r * r + a * a;
  double const sinTheta = std::sin(theta);
  return kdsDeltaTheta(theta, a, lambda) * r2PlusA2 * r2PlusA2 -
         kdsDelta(r, m, a, lambda) * a * a * sinTheta * sinTheta;
}

// ============================================================================
// Metric Components in Boyer-Lindquist Coordinates
// ============================================================================

/**
 * @brief g_tt = (-Delta_r + Delta_theta a^2 sin^2 theta) / (Xi^2 Sigma)
 *
 * Derived from Rocq: Definition kds_g_tt (r theta M a Lambda : R) : R :=
 *   (- kds_Delta r M a Lambda + kds_Delta_theta theta a Lambda * a^2 * (sin theta)^2)
 *   / ((kds_Xi a Lambda)^2 * kds_Sigma r theta a).
 *
 * At a = 0: g_tt = -(1 - 2M/r - Lambda r^2 / 3).
 */
[[nodiscard]] inline double kdsGTt(double r, double theta, double m, double a,
                                   double lambda) noexcept {
  double const sinTheta = std::sin(theta);
  double const xi = kdsXi(a, lambda);
  return (-kdsDelta(r, m, a, lambda) +
          kdsDeltaTheta(theta, a, lambda) * a * a * sinTheta * sinTheta) /
         (xi * xi * kdsSigma(r, theta, a));
}

/**
 * @brief g_rr = Sigma / Delta_r
 *
 * Derived from Rocq: Definition kds_g_rr (r theta M a Lambda : R) : R :=
 *   kds_Sigma r theta a / kds_Delta r M a Lambda.
 */
[[nodiscard]] inline double kdsGRr(double r, double theta, double m, double a,
                                   double lambda) noexcept {
  return kdsSigma(r, theta, a) / kdsDelta(r, m, a, lambda);
}

/**
 * @brief g_thth = Sigma / Delta_theta
 *
 * Derived from Rocq: Definition kds_g_thth (r theta a Lambda : R) : R :=
 *   kds_Sigma r theta a / kds_Delta_theta theta a Lambda.
 */
[[nodiscard]] inline double kdsGThth(double r, double theta, double a, double lambda) noexcept {
  return kdsSigma(r, theta, a) / kdsDeltaTheta(theta, a, lambda);
}

/**
 * @brief g_phph = sin^2 theta A / (Xi^2 Sigma)
 *
 * Derived from Rocq: Definition kds_g_phph (r theta M a Lambda : R) : R :=
 *   (sin theta)^2 * kds_A r theta M a Lambda / ((kds_Xi a Lambda)^2 * kds_Sigma r theta a).
 */
[[nodiscard]] inline double kdsGPhph(double r, double theta, double m, double a,
                                     double lambda) noexcept {
  double const sinTheta = std::sin(theta);
  double const xi = kdsXi(a, lambda);
  return sinTheta * sinTheta * kdsA(r, theta, m, a, lambda) / (xi * xi * kdsSigma(r, theta, a));
}

/**
 * @brief g_tph = a sin^2 theta (Delta_r - Delta_theta (r^2 + a^2)) / (Xi^2 Sigma)
 *
 * Derived from Rocq: Definition kds_g_tph (r theta M a Lambda : R) : R :=
 *   a * (sin theta)^2 * (kds_Delta r M a Lambda - kds_Delta_theta theta a Lambda * (r^2 + a^2))
 *   / ((kds_Xi a Lambda)^2 * kds_Sigma r theta a).
 *
 * At Lambda = 0 this is the Kerr term -2 M r a sin^2 theta / Sigma.
 */
[[nodiscard]] inline double kdsGTph(double r, double theta, double m, double a,
                                    double lambda) noexcept {
  double const sinTheta = std::sin(theta);
  double const xi = kdsXi(a, lambda);
  return a * sinTheta * sinTheta *
         (kdsDelta(r, m, a, lambda) - kdsDeltaTheta(theta, a, lambda) * (r * r + a * a)) /
         (xi * xi * kdsSigma(r, theta, a));
}

// ============================================================================
// Horizons: positive roots of Delta_r (from Rocq: kds_is_horizon)
// ============================================================================

/**
 * @brief Positive stationary point of Delta_r
 *
 * dDelta_r/dr = -(4 Lambda / 3) r^3 + 2 (1 - Lambda a^2 / 3) r - 2 M vanishes at
 * the roots of the depressed cubic r^3 + p r + q = 0 with
 * p = -3 (1 - Lambda a^2 / 3) / (2 Lambda) and q = 3 M / (2 Lambda). When it has
 * three real roots, one is negative and two are positive: the local minimum
 * r_a (upper = false) and the local maximum r_b (upper = true) of Delta_r.
 * Viete's trigonometric form gives them without cancellation at small Lambda.
 *
 * @param m Black hole mass (> 0)
 * @param a Spin parameter
 * @param lambda Cosmological constant (> 0)
 * @param upper true for the local maximum r_b, false for the local minimum r_a
 * @return Stationary radius, or NaN when Delta_r has no local maximum at r > 0
 */
[[nodiscard]] inline double kdsDeltaStationaryRadius(double m, double a, double lambda,
                                                     bool upper) noexcept {
  double const b = 1.0 - lambda * a * a / 3.0;
  if (!(lambda > 0.0) || !(m > 0.0) || !(b > 0.0)) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  double const p = -3.0 * b / (2.0 * lambda);
  double const q = 3.0 * m / (2.0 * lambda);
  double const cosArg = (3.0 * q / (2.0 * p)) * std::sqrt(-3.0 / p);
  if (!(cosArg > -1.0)) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  double const phi = std::acos(cosArg) / 3.0;
  double const amplitude = 2.0 * std::sqrt(-p / 3.0);
  double const shift = upper ? 0.0 : 2.0 * std::numbers::pi / 3.0;
  return amplitude * std::cos(phi - shift);
}

/**
 * @brief Bisect a sign change of Delta_r - offset on [lo, hi]
 *
 * Requires Delta_r(lo) - offset and Delta_r(hi) - offset of opposite sign.
 * Iterates until the midpoint equals an endpoint in double precision.
 */
[[nodiscard]] inline double kdsBisectDelta(double lo, double hi, double m, double a,
                                           double lambda, double offset) noexcept {
  bool const loPositive = kdsDelta(lo, m, a, lambda) - offset > 0.0;
  for (int iteration = 0; iteration < 256; ++iteration) {
    double const mid = 0.5 * (lo + hi);
    if (!(mid > lo && mid < hi)) {
      break;
    }
    if ((kdsDelta(mid, m, a, lambda) - offset > 0.0) == loPositive) {
      lo = mid;
    } else {
      hi = mid;
    }
  }
  return 0.5 * (lo + hi);
}

/**
 * @brief Inner (Cauchy) horizon r_-: smallest positive root of Delta_r
 *
 * Derived from Rocq: Definition kds_is_horizon (r M a Lambda : R) : Prop :=
 *   r > 0 /\ kds_Delta r M a Lambda = 0.
 *
 * Delta_r(0) = a^2, so at a = 0 the root sits at the curvature singularity
 * r = 0 and Schwarzschild-de Sitter has no Cauchy horizon; the function
 * returns 0 there. At Lambda = 0 it returns the Kerr value M - sqrt(M^2 - a^2).
 *
 * @return r_-, or NaN outside the black-hole parameter range
 */
[[nodiscard]] inline double kdsInnerHorizon(double m, double a, double lambda) noexcept {
  if (lambda == 0.0) {
    double const disc = m * m - a * a;
    return (m > 0.0 && disc >= 0.0) ? m - std::sqrt(disc)
                                    : std::numeric_limits<double>::quiet_NaN();
  }
  double const rMin = kdsDeltaStationaryRadius(m, a, lambda, false);
  if (!(kdsDelta(rMin, m, a, lambda) < 0.0)) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  if (a == 0.0) {
    return 0.0;
  }
  return kdsBisectDelta(0.0, rMin, m, a, lambda, 0.0);
}

/**
 * @brief Event horizon r_+: root of Delta_r between its local minimum and maximum
 *
 * At Lambda = 0 it returns the Kerr value M + sqrt(M^2 - a^2).
 *
 * @return r_+, or NaN outside the black-hole parameter range (naked
 *         singularity or beyond the Nariai limit)
 */
[[nodiscard]] inline double kdsEventHorizon(double m, double a, double lambda) noexcept {
  if (lambda == 0.0) {
    double const disc = m * m - a * a;
    return (m > 0.0 && disc >= 0.0) ? m + std::sqrt(disc)
                                    : std::numeric_limits<double>::quiet_NaN();
  }
  double const rMin = kdsDeltaStationaryRadius(m, a, lambda, false);
  double const rMax = kdsDeltaStationaryRadius(m, a, lambda, true);
  if (!(kdsDelta(rMin, m, a, lambda) < 0.0) || !(kdsDelta(rMax, m, a, lambda) > 0.0)) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return kdsBisectDelta(rMin, rMax, m, a, lambda, 0.0);
}

/**
 * @brief Cosmological horizon r_c: largest root of Delta_r
 *
 * Delta_r(sqrt(3/Lambda)) = -2 M sqrt(3/Lambda) < 0, so r_c lies between the
 * local maximum r_b of Delta_r and max(r_b, sqrt(3/Lambda)); the upper end
 * doubles until Delta_r is negative there. At Lambda = 0 there is
 * no cosmological horizon and the function returns +infinity.
 *
 * @return r_c, +infinity at Lambda = 0, or NaN outside the black-hole range
 */
[[nodiscard]] inline double kdsCosmologicalHorizon(double m, double a, double lambda) noexcept {
  if (lambda == 0.0) {
    return std::numeric_limits<double>::infinity();
  }
  double const rMin = kdsDeltaStationaryRadius(m, a, lambda, false);
  double const rMax = kdsDeltaStationaryRadius(m, a, lambda, true);
  if (!(kdsDelta(rMin, m, a, lambda) < 0.0) || !(kdsDelta(rMax, m, a, lambda) > 0.0)) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  double rHigh = std::fmax(rMax, std::sqrt(3.0 / lambda));
  for (int doubling = 0; doubling < 64 && !(kdsDelta(rHigh, m, a, lambda) < 0.0); ++doubling) {
    rHigh *= 2.0;
  }
  return kdsBisectDelta(rMax, rHigh, m, a, lambda, 0.0);
}

/**
 * @brief Black-hole ergosurface: outermost root of g_tt = 0 below the Delta_r maximum
 *
 * Derived from Rocq: Definition kds_is_ergosurface (r theta M a Lambda : R) : Prop :=
 *   r > 0 /\ kds_g_tt r theta M a Lambda = 0.
 *
 * g_tt = 0 where Delta_r = Delta_theta a^2 sin^2 theta. Between r_+ (where
 * Delta_r = 0) and the local maximum of Delta_r the left side rises
 * monotonically, so a bisection on that interval finds the surface around the
 * hole. A second, cosmological ergosurface near r_c lies outside that interval.
 * On the axis or at a = 0 the surface coincides with r_+.
 *
 * @return Ergosurface radius, or NaN when no static region separates the
 *         black-hole and cosmological ergosurfaces
 */
[[nodiscard]] inline double kdsErgosphereRadius(double theta, double m, double a,
                                                double lambda) noexcept {
  double const sinTheta = std::sin(theta);
  double const target = kdsDeltaTheta(theta, a, lambda) * a * a * sinTheta * sinTheta;
  double const rPlus = kdsEventHorizon(m, a, lambda);
  if (std::isnan(rPlus) || target == 0.0) {
    return rPlus;
  }
  double const rMax = (lambda == 0.0) ? 4.0 * m : kdsDeltaStationaryRadius(m, a, lambda, true);
  if (!(kdsDelta(rMax, m, a, lambda) > target)) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return kdsBisectDelta(rPlus, rMax, m, a, lambda, target);
}

// ============================================================================
// Frame Dragging and Angular Velocity
// ============================================================================

/**
 * @brief Frame dragging angular velocity: omega = -g_tph / g_phph
 *
 * Derived from Rocq: Definition kds_frame_dragging_omega (r theta M a Lambda : R) : R :=
 *   - kds_g_tph r theta M a Lambda / kds_g_phph r theta M a Lambda.
 *
 * Equals a (Delta_theta (r^2 + a^2) - Delta_r) / A; Xi cancels.
 */
[[nodiscard]] inline double kdsFrameDraggingOmega(double r, double theta, double m, double a,
                                                  double lambda) noexcept {
  return -kdsGTph(r, theta, m, a, lambda) / kdsGPhph(r, theta, m, a, lambda);
}

// ============================================================================
// Physical Validity Constraints
// ============================================================================

/**
 * @brief Check if parameters give a Kerr-de Sitter black hole with ordered horizons
 *
 * Derived from Rocq: Definition is_physical_kds_black_hole (M a Lambda : R) : Prop :=
 *   M > 0 /\ Lambda > 0 /\ exists horizons r_minus <= r_plus < r_c.
 *
 * Lambda = 0 (Kerr) is outside the predicate, which names the de Sitter case.
 *
 * @return true when M > 0, Lambda > 0, and r_- <= r_+ < r_c all exist
 */
[[nodiscard]] inline bool isPhysicalKdsBlackHole(double m, double a, double lambda) noexcept {
  if (!(m > 0.0) || !(lambda > 0.0)) {
    return false;
  }
  double const rMinus = kdsInnerHorizon(m, a, lambda);
  double const rPlus = kdsEventHorizon(m, a, lambda);
  double const rCosmo = kdsCosmologicalHorizon(m, a, lambda);
  return rMinus <= rPlus && rPlus < rCosmo;
}

/**
 * @brief Check if a position is between event and cosmological horizons
 *
 * Derived from Rocq: Definition is_exterior_region (r M a Lambda : R) : Prop :=
 *   r > r_plus /\ r < r_c for the event and cosmological horizons.
 */
[[nodiscard]] inline bool isExteriorRegion(double r, double m, double a, double lambda) noexcept {
  double const rPlus = kdsEventHorizon(m, a, lambda);
  double const rCosmo = kdsCosmologicalHorizon(m, a, lambda);
  return r > rPlus && r < rCosmo;
}

/**
 * @brief Check if d/dt is spacelike (g_tt > 0)
 *
 * Derived from Rocq: Definition is_in_ergosphere (r theta M a Lambda : R) : Prop :=
 *   kds_g_tt r theta M a Lambda > 0.
 *
 * True inside the black-hole ergoregion and beyond the cosmological
 * ergosurface.
 */
[[nodiscard]] inline bool isInErgosphere(double r, double theta, double m, double a,
                                         double lambda) noexcept {
  return kdsGTt(r, theta, m, a, lambda) > 0.0;
}

/**
 * @brief Verify that horizons are ordered: r_- <= r_+ < r_c
 *
 * r_- = r_+ only at extremality; r_- = 0 at a = 0.
 */
[[nodiscard]] inline bool verifyHorizonOrdering(double m, double a, double lambda) noexcept {
  return isPhysicalKdsBlackHole(m, a, lambda);
}

// ============================================================================
// Reduction to Kerr and de Sitter Limits
// ============================================================================

/**
 * @brief Check if parameters are in Kerr limit (Lambda ~ 0)
 */
[[nodiscard]] constexpr bool isKerrLimit(double lambda, double tolerance = 1e-10) noexcept {
  return std::abs(lambda) < tolerance;
}

/**
 * @brief Check if parameters are in de Sitter limit (M ~ 0, a ~ 0)
 */
[[nodiscard]] constexpr bool isDeSitterLimit(double m, double a,
                                             double tolerance = 1e-10) noexcept {
  return std::abs(m) < tolerance && std::abs(a) < tolerance;
}

// ============================================================================
// Cosmological Constant Utilities
// ============================================================================

/**
 * @brief Cosmological constant in inverse square meters, unchanged by c = G = 1
 *
 * Lambda carries dimension length^-2 in SI and in geometric units alike, so the
 * conversion is the identity. Callers that measure lengths in M rescale by M^2.
 */
[[nodiscard]] constexpr double lambdaSiToGeometric(double lambdaSi) noexcept {
  return lambdaSi;
}

/**
 * @brief Observed cosmological constant, Lambda ~ 1.1e-52 m^-2 (Planck 2018)
 */
[[nodiscard]] constexpr double observedLambda() noexcept {
  return 1.1e-52;
}

} // namespace verified

#endif // PHYSICS_VERIFIED_KERR_DE_SITTER_HPP
