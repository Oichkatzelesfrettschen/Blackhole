/**
 * @file johannsen_psaltis.h
 * @brief Johannsen-Psaltis parametric deviation metric for EHT no-hair tests.
 *
 * WHY: The EHT constrains deviations from the Kerr metric using the
 * Johannsen-Psaltis (JP) parametrization. When all deviation parameters
 * vanish (alpha_13 = alpha_22 = alpha_52 = 0), the metric reduces exactly
 * to Kerr. Non-zero values parameterize model-independent departures
 * from GR, enabling tests of the no-hair theorem.
 *
 * WHAT: The JP metric modifies the Kerr tt, rr, and tphi components:
 *   g_tt -> g_tt^Kerr * (1 + h(r, theta))
 * where h(r, theta) depends on deviation parameters alpha_{ij}.
 *
 * The metric preserves:
 *   - Stationarity and axisymmetry
 *   - Asymptotic flatness
 *   - Separability of Hamilton-Jacobi equation (integrability)
 *   - Correct Newtonian limit
 *
 * HOW: Compute JP metric components, ISCO, shadow radius with deviation
 * parameters. Compare shadow diameter shift with EHT constraints.
 *
 * References:
 *   - Johannsen & Psaltis (2011), PRD 83, 124015
 *   - Johannsen (2013), PRD 87, 124017 (revised parametrization)
 *   - EHT Collaboration Paper VI (2019): M87* no-hair constraints
 */

#ifndef PHYSICS_JOHANNSEN_PSALTIS_H
#define PHYSICS_JOHANNSEN_PSALTIS_H

#include <array>
#include <cmath>

namespace physics {

// ============================================================================
// JP Deviation Parameters
// ============================================================================

/**
 * @brief Johannsen-Psaltis deviation parameters.
 *
 * The deviation function h(r, theta) modifies the Kerr metric:
 *   h = sum_k epsilon_k * (M/r)^k * f_k(theta)
 *
 * In the Johannsen (2013) revised parametrization, the key parameters are:
 *   alpha_13: leading-order modification to g_tt (strongest EHT constraint)
 *   alpha_22: modification to g_rr
 *   alpha_52: higher-order modification
 *
 * All parameters = 0 recovers exact Kerr.
 */
struct JPParams {
  double alpha13 = 0.0;  // Leading tt deviation (EHT-constrained)
  double alpha22 = 0.0;  // rr deviation
  double alpha52 = 0.0;  // Higher-order deviation
  double epsilon3 = 0.0; // Alternative parametrization (Johannsen 2011)
};

// ============================================================================
// Deviation Functions
// ============================================================================

/**
 * @brief Johannsen (2013) A1 function.
 *
 * A1(r) = 1 + alpha_13 * (M/r)^3
 *
 * Modifies the tt and phi-phi components of the metric.
 * Must satisfy A1 > 0 outside the horizon for physical solutions.
 *
 * @param r Radial coordinate [geometric units]
 * @param M Geometric mass [geometric units]
 * @param alpha13 Deviation parameter
 * @return A1(r) value
 */
[[nodiscard]] inline double jpA1(double r, double mGeo, double alpha13) {
  const double mR = mGeo / r;
  return 1.0 + (alpha13 * mR * mR * mR);
}

/**
 * @brief Johannsen (2013) A2 function.
 *
 * A2(r) = 1 + alpha_22 * (M/r)^2
 *
 * Modifies the rr component of the metric.
 *
 * @param r Radial coordinate [geometric units]
 * @param M Geometric mass [geometric units]
 * @param alpha22 Deviation parameter
 * @return A2(r) value
 */
[[nodiscard]] inline double jpA2(double r, double mGeo, double alpha22) {
  const double mR = mGeo / r;
  return 1.0 + (alpha22 * mR * mR);
}

/**
 * @brief Johannsen (2013) A5 function.
 *
 * A5(r) = 1 + alpha_52 * (M/r)^2
 *
 * Higher-order modification.
 *
 * @param r Radial coordinate [geometric units]
 * @param M Geometric mass [geometric units]
 * @param alpha52 Deviation parameter
 * @return A5(r) value
 */
[[nodiscard]] inline double jpA5(double r, double mGeo, double alpha52) {
  const double mR = mGeo / r;
  return 1.0 + (alpha52 * mR * mR);
}

// ============================================================================
// JP Metric Components
// ============================================================================

/**
 * @brief JP metric in Boyer-Lindquist-like coordinates.
 *
 * The Johannsen (2013) metric modifies the Kerr metric components:
 *
 *   g_tt = -[1 - 2Mr/Sigma] * A1(r)^2 / A5(r)^2
 *          + a^2 sin^2(theta) * [A1(r)^2 - A5(r)^2] * 2Mr / (Sigma^2 * A5(r)^2)
 *
 * For simplicity and following the EHT analysis convention, we implement
 * the leading modification:
 *
 *   g_tt^JP = g_tt^Kerr * A1(r)^2
 *   g_rr^JP = g_rr^Kerr * A2(r) / A1(r)
 *   g_phiphi^JP = g_phiphi^Kerr * A1(r)
 *   g_tphi^JP = g_tphi^Kerr * A1(r)
 *
 * Returns [g_tt, g_rr, g_thth, g_phph, g_tph] (5 non-zero components).
 *
 * @param r Radial coordinate [geometric units]
 * @param theta Polar angle
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @param params JP deviation parameters
 * @return {g_tt, g_rr, g_thth, g_phph, g_tph}
 */
[[nodiscard]] inline std::array<double, 5> jpMetric(double r, double theta,
                                                     double mGeo, double a,
                                                     const JPParams& params) {
  const double cosTh = std::cos(theta);
  const double sinTh = std::sin(theta);
  const double sin2 = sinTh * sinTh;
  const double rS = 2.0 * mGeo;

  // Standard Kerr quantities
  const double sigma = (r * r) + (a * a * cosTh * cosTh);
  const double delta = (r * r) - (rS * r) + (a * a);

  // BL Kerr metric components
  const double gTtKerr = -(1.0 - ((rS * r) / sigma));
  const double gRrKerr = sigma / delta;
  const double gThth = sigma;
  const double gPhphKerr = ((r * r) + (a * a) + ((rS * r * a * a * sin2) / sigma)) * sin2;
  const double gTphKerr = -((rS * r * a * sin2) / sigma);

  // JP deviation functions
  const double a1Val = jpA1(r, mGeo, params.alpha13);
  const double a2Val = jpA2(r, mGeo, params.alpha22);

  // Modified metric components
  const double gTt = gTtKerr * a1Val * a1Val;
  const double gRr = (gRrKerr * a2Val) / a1Val;
  const double gPhph = gPhphKerr * a1Val;
  const double gTph = gTphKerr * a1Val;

  return {gTt, gRr, gThth, gPhph, gTph};
}

// ============================================================================
// Shadow and Observable Quantities
// ============================================================================

/**
 * @brief Approximate shadow radius modification from JP deviation.
 *
 * For small deviations, the fractional shadow radius change is:
 *   delta_r_sh / r_sh ~ alpha_13 / (2 * r_ph^3 / M^3)
 *
 * where r_ph is the photon orbit radius (3M for Schwarzschild).
 *
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @param alpha13 Leading deviation parameter
 * @return Fractional shadow radius change
 */
[[nodiscard]] inline double jpShadowFractionalShift(double mGeo, double a,
                                                    double alpha13) {
  // Photon orbit in Kerr (prograde, equatorial)
  // For Schwarzschild: r_ph = 3M, for Kerr: r_ph depends on spin
  // Use Schwarzschild approximation for small spin
  double rPh = 3.0 * mGeo;
  if (std::abs(a) > (0.01 * mGeo)) {
    // Bardeen formula for prograde photon orbit
    const double aStar = a / mGeo;
    rPh = 2.0 * mGeo * (1.0 + std::cos((2.0 / 3.0) *
           std::acos(-std::abs(aStar))));
  }

  const double mRatio = mGeo / rPh;
  return (alpha13 * mRatio * mRatio * mRatio) / 2.0;
}

/**
 * @brief Check if JP parameters are within EHT constraints.
 *
 * EHT M87* Paper VI (2019) constrains:
 *   |alpha_13| < ~2.0 (95% confidence, spin-dependent)
 *
 * @param params JP deviation parameters
 * @return true if within typical EHT bounds
 */
[[nodiscard]] inline bool jpWithinEhtBounds(const JPParams& params) {
  // Conservative bounds from EHT M87* analysis
  return (std::abs(params.alpha13) < 2.0) &&
         (std::abs(params.alpha22) < 5.0);
}

/**
 * @brief Verify JP metric reduces to Kerr when all deviations vanish.
 *
 * @param r Radial coordinate [geometric units]
 * @param theta Polar angle
 * @param M Geometric mass [geometric units]
 * @param a Spin parameter [geometric units]
 * @param tol Tolerance for comparison
 * @return true if JP(alpha=0) == Kerr within tolerance
 */
[[nodiscard]] inline bool jpKerrLimitCheck(double r, double theta,
                                            double mGeo, double a,
                                            double tol = 1e-14) {
  const JPParams zeroParams; // all zeros by default

  const auto jp = jpMetric(r, theta, mGeo, a, zeroParams);

  const double cosTheta = std::cos(theta);
  const double sinTheta = std::sin(theta);
  const double sin2 = sinTheta * sinTheta;
  const double sigma = (r * r) + (a * a * cosTheta * cosTheta);
  const double delta = (r * r) - (2.0 * mGeo * r) + (a * a);
  const double rS = 2.0 * mGeo;

  const double gTtKerr = -(1.0 - ((rS * r) / sigma));
  const double gRrKerr = sigma / delta;
  const double gPhphKerr = ((r * r) + (a * a) + ((rS * r * a * a * sin2) / sigma)) * sin2;
  const double gTphKerr = -((rS * r * a * sin2) / sigma);

  return (std::abs(jp.at(0) - gTtKerr) < tol) &&
         (std::abs(jp.at(1) - gRrKerr) < tol) &&
         (std::abs(jp.at(2) - sigma) < tol) &&
         (std::abs(jp.at(3) - gPhphKerr) < tol) &&
         (std::abs(jp.at(4) - gTphKerr) < tol);
}

} // namespace physics

#endif // PHYSICS_JOHANNSEN_PSALTIS_H
