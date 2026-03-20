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

#include "constants.h"
#include "kerr.h"
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
  double alpha_13 = 0.0;  // Leading tt deviation (EHT-constrained)
  double alpha_22 = 0.0;  // rr deviation
  double alpha_52 = 0.0;  // Higher-order deviation
  double epsilon_3 = 0.0; // Alternative parametrization (Johannsen 2011)
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
 * @param alpha_13 Deviation parameter
 * @return A1(r) value
 */
inline double jp_A1(double r, double M, double alpha_13) {
  double Mr = M / r;
  return 1.0 + alpha_13 * Mr * Mr * Mr;
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
 * @param alpha_22 Deviation parameter
 * @return A2(r) value
 */
inline double jp_A2(double r, double M, double alpha_22) {
  double Mr = M / r;
  return 1.0 + alpha_22 * Mr * Mr;
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
 * @param alpha_52 Deviation parameter
 * @return A5(r) value
 */
inline double jp_A5(double r, double M, double alpha_52) {
  double Mr = M / r;
  return 1.0 + alpha_52 * Mr * Mr;
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
inline std::array<double, 5> jp_metric(double r, double theta,
                                        double M, double a,
                                        const JPParams& params) {
  double cos_th = std::cos(theta);
  double sin_th = std::sin(theta);
  double sin2 = sin_th * sin_th;
  double r_s = 2.0 * M;

  // Standard Kerr quantities
  double sigma = r * r + a * a * cos_th * cos_th;
  double delta = r * r - r_s * r + a * a;

  // BL Kerr metric components
  double g_tt_kerr = -(1.0 - r_s * r / sigma);
  double g_rr_kerr = sigma / delta;
  double g_thth = sigma;
  double g_phph_kerr = (r * r + a * a + r_s * r * a * a * sin2 / sigma) * sin2;
  double g_tph_kerr = -r_s * r * a * sin2 / sigma;

  // JP deviation functions
  double A1 = jp_A1(r, M, params.alpha_13);
  double A2 = jp_A2(r, M, params.alpha_22);

  // Modified metric components
  double g_tt = g_tt_kerr * A1 * A1;
  double g_rr = g_rr_kerr * A2 / A1;
  double g_phph = g_phph_kerr * A1;
  double g_tph = g_tph_kerr * A1;

  return {g_tt, g_rr, g_thth, g_phph, g_tph};
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
 * @param alpha_13 Leading deviation parameter
 * @return Fractional shadow radius change
 */
inline double jp_shadow_fractional_shift(double M, double a,
                                          double alpha_13) {
  // Photon orbit in Kerr (prograde, equatorial)
  // For Schwarzschild: r_ph = 3M, for Kerr: r_ph depends on spin
  // Use Schwarzschild approximation for small spin
  double r_ph = 3.0 * M;
  if (std::abs(a) > 0.01 * M) {
    // Bardeen formula for prograde photon orbit
    double a_star = a / M;
    r_ph = 2.0 * M * (1.0 + std::cos(2.0 / 3.0 *
           std::acos(-std::abs(a_star))));
  }

  double Mr_ratio = M / r_ph;
  return alpha_13 * Mr_ratio * Mr_ratio * Mr_ratio / 2.0;
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
inline bool jp_within_eht_bounds(const JPParams& params) {
  // Conservative bounds from EHT M87* analysis
  return std::abs(params.alpha_13) < 2.0 &&
         std::abs(params.alpha_22) < 5.0;
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
inline bool jp_kerr_limit_check(double r, double theta,
                                 double M, double a,
                                 double tol = 1e-14) {
  JPParams zero_params; // all zeros

  auto jp = jp_metric(r, theta, M, a, zero_params);

  double sigma = r * r + a * a * std::cos(theta) * std::cos(theta);
  double delta = r * r - 2.0 * M * r + a * a;
  double sin2 = std::sin(theta) * std::sin(theta);
  double r_s = 2.0 * M;

  double g_tt_kerr = -(1.0 - r_s * r / sigma);
  double g_rr_kerr = sigma / delta;
  double g_phph_kerr = (r * r + a * a + r_s * r * a * a * sin2 / sigma) * sin2;
  double g_tph_kerr = -r_s * r * a * sin2 / sigma;

  return std::abs(jp[0] - g_tt_kerr) < tol &&
         std::abs(jp[1] - g_rr_kerr) < tol &&
         std::abs(jp[2] - sigma) < tol &&
         std::abs(jp[3] - g_phph_kerr) < tol &&
         std::abs(jp[4] - g_tph_kerr) < tol;
}

} // namespace physics

#endif // PHYSICS_JOHANNSEN_PSALTIS_H
