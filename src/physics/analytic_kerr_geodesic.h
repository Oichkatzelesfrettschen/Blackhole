/**
 * @file analytic_kerr_geodesic.h
 * @brief Analytic Kerr null geodesics via Jacobi elliptic functions.
 *
 * WHY: Numerical integration of Kerr geodesics is O(N) per ray where
 * N ~ 1000 steps for photon sphere orbits. Analytic solutions using
 * Jacobi elliptic functions give O(1) evaluation -- the position at
 * any affine parameter lambda is computed directly without stepping.
 * This is ~1000x faster for photon ring rays (n >= 1).
 *
 * WHAT: For Kerr null geodesics classified by impact parameters
 * (xi = L/E, eta = Q/E^2), the radial and polar motions separate
 * via the Carter constant. The radial motion r(lambda) involves
 * an elliptic integral that inverts to a Jacobi elliptic function.
 *
 * The key equations (Dyson 2023, arXiv:2302.03704):
 *
 * Radial motion (R(r) = 0 defines turning points):
 *   R(r) = (r^2 + a^2 - a*xi)^2 - Delta * (eta + (xi - a)^2)
 *        = r^4 + (a^2 - xi^2 - eta)*r^2 + 2M*(eta + (xi-a)^2)*r - a^2*eta
 *
 * The quartic R(r) is factored into (r - r1)(r - r2)(r - r3)(r - r4)
 * with roots r1 >= r2 >= r3 >= r4. The solution is:
 *   r(lambda) = r3 + (r2 - r3) * sn^2(u | m)
 * where sn is the Jacobi elliptic function, and m and u depend on
 * the roots.
 *
 * Polar motion similarly uses Jacobi functions for theta(lambda).
 *
 * HOW: Uses Boost.Math Jacobi elliptic functions (sn, cn, dn)
 * already available via boost/1.90.0.
 *
 * References:
 *   - Dyson (2023), arXiv:2302.03704 -- plunging geodesics
 *   - Gralla & Lupsasca (2020), PRD 101 -- null geodesic classification
 *   - Rauch & Blandford (1994) -- lensing formulas
 *   - Dexter & Agol (2009) -- fast ray tracing
 */

#ifndef PHYSICS_ANALYTIC_KERR_GEODESIC_H
#define PHYSICS_ANALYTIC_KERR_GEODESIC_H

#include "constants.h"
#include <array>
#include <cmath>
#include <complex>
#include <algorithm>

#ifdef __has_include
#  if __has_include(<boost/math/special_functions/jacobi_elliptic.hpp>)
#    include <boost/math/special_functions/jacobi_elliptic.hpp>
#    include <boost/math/special_functions/ellint_1.hpp>
#    include <boost/math/special_functions/ellint_2.hpp>
#    define PHYSICS_HAS_BOOST_JACOBI 1
#  endif
#endif

namespace physics {

// ============================================================================
// Geodesic Classification
// ============================================================================

/**
 * @brief Type of radial geodesic motion.
 */
enum class RadialMotionType {
  Transit,   // Ray passes through: two real turning points
  Plunge,    // Ray falls into the black hole: no outer turning point
  Scatter,   // Ray scatters off the potential barrier
  Orbit,     // Ray orbits at the photon sphere (unstable)
  Invalid    // Unphysical parameters
};

/**
 * @brief Impact parameters for Kerr null geodesics.
 *
 * xi = L_z / E (angular momentum per energy)
 * eta = Q / E^2 (Carter constant per energy squared)
 *
 * These two parameters, along with the spin a, completely
 * determine the geodesic trajectory.
 */
struct ImpactParams {
  double xi;   // L/E
  double eta;  // Q/E^2
};

/**
 * @brief Roots of the radial potential R(r).
 *
 * R(r) = r^4 + (a^2 - xi^2 - eta)*r^2 + 2M*(eta + (xi-a)^2)*r - a^2*eta
 *
 * For bound orbits, all four roots are real. For plunging orbits,
 * two roots may be complex conjugates.
 */
struct RadialRoots {
  std::array<std::complex<double>, 4> roots;
  int n_real = 0;        // Number of real roots
  RadialMotionType type = RadialMotionType::Invalid;
};

// ============================================================================
// Radial Potential
// ============================================================================

/**
 * @brief Evaluate the Kerr radial potential R(r).
 *
 * R(r) = (r^2 + a^2 - a*xi)^2 - Delta * [eta + (xi - a)^2]
 *
 * Roots of R(r) = 0 are the radial turning points.
 *
 * @param r Radial coordinate [geometric units, M=1]
 * @param a Spin parameter [geometric units]
 * @param xi Impact parameter L/E
 * @param eta Impact parameter Q/E^2
 * @return R(r) value
 */
inline double radial_potential(double r, double a, double xi, double eta) {
  double r2 = r * r;
  double a2 = a * a;
  double xi_a = xi - a;
  double delta = r2 - 2.0 * r + a2; // M=1

  double term1 = r2 + a2 - a * xi;
  return term1 * term1 - delta * (eta + xi_a * xi_a);
}

/**
 * @brief Coefficients of the quartic R(r) = r^4 + c3*r^3 + c2*r^2 + c1*r + c0.
 *
 * Expanding R(r) in standard form (with M=1):
 *   c3 = 0 (no cubic term in Kerr)
 *   ... actually R(r) expanded gives:
 *   R(r) = r^4 + (a^2 - xi^2 - eta)*r^2 + 2*(eta + (xi-a)^2)*r - a^2*eta
 *
 * Wait: let me be more careful. R(r) = (r^2+a^2-a*xi)^2 - (r^2-2r+a^2)(eta+(xi-a)^2)
 * Expanding:
 *   (r^2+a^2-a*xi)^2 = r^4 + 2r^2(a^2-a*xi) + (a^2-a*xi)^2
 *   (r^2-2r+a^2)(eta+(xi-a)^2) = (eta+xi_a^2)*r^2 - 2(eta+xi_a^2)*r + a^2(eta+xi_a^2)
 *
 * So: R = r^4 + [2(a^2-a*xi) - eta - xi_a^2]*r^2
 *       + 2(eta+xi_a^2)*r
 *       + [(a^2-a*xi)^2 - a^2(eta+xi_a^2)]
 *
 * Note: c3 = 0 (no r^3 term), which is correct.
 */
struct QuarticCoeffs {
  double c0, c1, c2; // R(r) = r^4 + c2*r^2 + c1*r + c0
};

inline QuarticCoeffs radial_quartic_coeffs(double a, double xi, double eta) {
  double a2 = a * a;
  double xi_a = xi - a;
  double xi_a2 = xi_a * xi_a;

  QuarticCoeffs c;
  c.c2 = 2.0 * (a2 - a * xi) - eta - xi_a2;
  c.c1 = 2.0 * (eta + xi_a2); // M=1
  c.c0 = (a2 - a * xi) * (a2 - a * xi) - a2 * (eta + xi_a2);

  return c;
}

// ============================================================================
// Root Finding (Depressed Quartic)
// ============================================================================

/**
 * @brief Find roots of the depressed quartic r^4 + c2*r^2 + c1*r + c0 = 0.
 *
 * Uses Ferrari's method to reduce to a resolvent cubic.
 *
 * @param c Quartic coefficients
 * @return RadialRoots with up to 4 roots
 */
inline RadialRoots find_radial_roots(const QuarticCoeffs& c) {
  RadialRoots result;

  // Ferrari's resolvent cubic: y^3 - c2*y^2 - 4*c0*y + (4*c2*c0 - c1^2) = 0
  // Substituting y = t + c2/3 to get depressed cubic t^3 + pt + q = 0
  double p_coeff = -c.c2 * c.c2 / 3.0 - 4.0 * c.c0;
  double q_coeff = -2.0 * c.c2 * c.c2 * c.c2 / 27.0
                 + 4.0 * c.c2 * c.c0 / 3.0 - c.c1 * c.c1;

  // Cardano's formula for the resolvent cubic
  double disc = q_coeff * q_coeff / 4.0 + p_coeff * p_coeff * p_coeff / 27.0;

  double y1;
  if (disc >= 0.0) {
    double sq = std::sqrt(disc);
    double u = std::cbrt(-q_coeff / 2.0 + sq);
    double v = std::cbrt(-q_coeff / 2.0 - sq);
    y1 = u + v + c.c2 / 3.0;
  } else {
    // Three real roots; use trigonometric form
    double r_val = std::sqrt(-p_coeff * p_coeff * p_coeff / 27.0);
    double phi = std::acos(-q_coeff / (2.0 * r_val));
    y1 = 2.0 * std::cbrt(r_val) * std::cos(phi / 3.0) + c.c2 / 3.0;
  }

  // Factor quartic using y1
  // r^4 + c2*r^2 + c1*r + c0 = (r^2 + y1/2)^2 - [(y1 + c2)*r^2 - c1*r + y1^2/4 - c0]
  // The second factor is a quadratic in r: A*r^2 + B*r + C
  double A = y1 + c.c2;
  double B = -c.c1;
  double C = y1 * y1 / 4.0 - c.c0;

  // Two quadratics: r^2 +/- sqrt(A)*r + (y1/2 +/- C/sqrt(A)) ... etc.
  // Actually, use the direct factorization:
  // r^4 + c2*r^2 + c1*r + c0 = (r^2 + alpha*r + beta)(r^2 - alpha*r + gamma)
  // where alpha^2 = y1 + c2, beta + gamma = c2 + alpha^2 = y1 + 2*c2, beta*gamma = c0, (gamma-beta)*alpha = c1

  if (A < 0.0) {
    // alpha is imaginary; all roots come in complex conjugate pairs
    result.n_real = 0;
    result.type = RadialMotionType::Plunge;
    return result;
  }

  double alpha = std::sqrt(A);
  double gamma, beta;

  if (std::abs(alpha) > 1e-15) {
    gamma = (c.c1 / alpha + y1) / 2.0 + c.c2 / 2.0 + A / 2.0;
    beta = (-c.c1 / alpha + y1) / 2.0 + c.c2 / 2.0 + A / 2.0;

    // More robust: beta + gamma = y1 + 2*c2 ... no, let me use the direct relations
    // gamma - beta = c1 / alpha, beta + gamma = c2 + alpha^2, beta * gamma = c0
    // From (gamma-beta) = c1/alpha and (gamma+beta) computed from the quartic:
    // Actually, let me just solve the two quadratics directly.
  } else {
    // alpha ~ 0: degenerate case
    double disc1 = -4.0 * c.c0;
    if (disc1 < 0.0) {
      result.n_real = 0;
      result.type = RadialMotionType::Plunge;
      return result;
    }
    double sq = std::sqrt(disc1);
    result.roots[0] = std::complex<double>(sq / 2.0, 0);
    result.roots[1] = std::complex<double>(-sq / 2.0, 0);
    result.roots[2] = result.roots[0];
    result.roots[3] = result.roots[1];
    result.n_real = 2;
    result.type = RadialMotionType::Transit;
    return result;
  }

  // Quadratic 1: r^2 + alpha*r + beta = 0
  // Use the robust relations:
  beta = y1 / 2.0 - c.c1 / (2.0 * alpha);
  gamma = y1 / 2.0 + c.c1 / (2.0 * alpha);

  double disc1 = alpha * alpha - 4.0 * beta;
  double disc2 = alpha * alpha - 4.0 * gamma;

  result.n_real = 0;

  if (disc1 >= 0.0) {
    double sq1 = std::sqrt(disc1);
    result.roots[0] = std::complex<double>((-alpha + sq1) / 2.0, 0);
    result.roots[1] = std::complex<double>((-alpha - sq1) / 2.0, 0);
    result.n_real += 2;
  } else {
    double sq1 = std::sqrt(-disc1);
    result.roots[0] = std::complex<double>(-alpha / 2.0, sq1 / 2.0);
    result.roots[1] = std::complex<double>(-alpha / 2.0, -sq1 / 2.0);
  }

  if (disc2 >= 0.0) {
    double sq2 = std::sqrt(disc2);
    result.roots[2] = std::complex<double>((alpha + sq2) / 2.0, 0);
    result.roots[3] = std::complex<double>((alpha - sq2) / 2.0, 0);
    result.n_real += 2;
  } else {
    double sq2 = std::sqrt(-disc2);
    result.roots[2] = std::complex<double>(alpha / 2.0, sq2 / 2.0);
    result.roots[3] = std::complex<double>(alpha / 2.0, -sq2 / 2.0);
  }

  // Classify motion type
  if (result.n_real == 4) {
    result.type = RadialMotionType::Transit;
  } else if (result.n_real == 2) {
    result.type = RadialMotionType::Scatter;
  } else {
    result.type = RadialMotionType::Plunge;
  }

  // Sort real roots in descending order
  if (result.n_real >= 2) {
    // Simple bubble sort on real parts
    for (int i = 0; i < 3; ++i) {
      for (int j = i + 1; j < 4; ++j) {
        if (result.roots[j].real() > result.roots[i].real()) {
          std::swap(result.roots[i], result.roots[j]);
        }
      }
    }
  }

  return result;
}

// ============================================================================
// Analytic Radial Solution
// ============================================================================

#ifdef PHYSICS_HAS_BOOST_JACOBI

/**
 * @brief Compute r(lambda) analytically using Jacobi elliptic functions.
 *
 * For a transit orbit with four real roots r1 >= r2 >= r3 >= r4,
 * the radial solution is:
 *
 *   r(lambda) = [r3*(r1-r4) - r4*(r1-r3)*sn^2(u|m)] / [(r1-r4) - (r1-r3)*sn^2(u|m)]
 *
 * where:
 *   m = (r2-r3)*(r1-r4) / [(r1-r3)*(r2-r4)]   (elliptic modulus squared)
 *   u = sqrt((r1-r3)*(r2-r4)) * lambda / 2
 *
 * @param lambda Affine parameter
 * @param roots RadialRoots from find_radial_roots()
 * @param lambda0 Initial affine parameter offset
 * @return Radial coordinate r
 */
inline double r_analytic(double lambda, const RadialRoots& roots,
                          double lambda0 = 0.0) {
  if (roots.n_real < 4) {
    return -1.0; // Not a transit orbit; analytic formula requires 4 real roots
  }

  double r1 = roots.roots[0].real();
  double r2 = roots.roots[1].real();
  double r3 = roots.roots[2].real();
  double r4 = roots.roots[3].real();

  // Elliptic modulus
  double num = (r2 - r3) * (r1 - r4);
  double den = (r1 - r3) * (r2 - r4);
  if (std::abs(den) < 1e-30) return r3;
  double m = num / den;

  // Argument
  double scale = std::sqrt(std::abs((r1 - r3) * (r2 - r4))) / 2.0;
  double u = scale * (lambda - lambda0);

  // Jacobi elliptic function sn(u | k) where k = sqrt(m)
  double k = std::sqrt(std::clamp(m, 0.0, 1.0));
  double sn_val = boost::math::jacobi_sn(k, u);
  double cn_val = boost::math::jacobi_cn(k, u);
  (void)cn_val; // unused but kept for symmetry

  double sn2 = sn_val * sn_val;

  // r(lambda)
  double a_coeff = r3 * (r1 - r4) - r4 * (r1 - r3) * sn2;
  double b_coeff = (r1 - r4) - (r1 - r3) * sn2;

  if (std::abs(b_coeff) < 1e-30) return r1; // At turning point
  return a_coeff / b_coeff;
}

/**
 * @brief Compute the half-period of radial oscillation.
 *
 * The radial motion has period 2*K(m)/scale in the affine parameter,
 * where K(m) is the complete elliptic integral of the first kind.
 *
 * @param roots Radial roots
 * @return Half-period in affine parameter
 */
inline double radial_half_period(const RadialRoots& roots) {
  if (roots.n_real < 4) return 0.0;

  double r1 = roots.roots[0].real();
  double r2 = roots.roots[1].real();
  double r3 = roots.roots[2].real();
  double r4 = roots.roots[3].real();

  double num = (r2 - r3) * (r1 - r4);
  double den = (r1 - r3) * (r2 - r4);
  if (std::abs(den) < 1e-30) return 0.0;
  double m = num / den;

  double scale = std::sqrt(std::abs((r1 - r3) * (r2 - r4))) / 2.0;
  if (scale < 1e-30) return 0.0;

  double k = std::sqrt(std::clamp(m, 0.0, 1.0));
  double K = boost::math::ellint_1(k);
  return K / scale;
}

#endif // PHYSICS_HAS_BOOST_JACOBI

// ============================================================================
// Critical Curves (Photon Sphere)
// ============================================================================

/**
 * @brief Critical impact parameters for the Kerr photon sphere.
 *
 * The photon sphere consists of unstable circular orbits at radius r_ph.
 * The critical impact parameters are:
 *   xi_c = -(r_ph^2 + a^2) / a + 2*r_ph / a   (prograde)
 *   eta_c = r_ph^2 * (4*Delta'(r_ph) - r_ph*Delta''(r_ph)) / (a^2*Delta'(r_ph)^2)
 *
 * Simplified for M=1:
 *   xi_c(r) = (r^2 + a^2 - 2*r*Delta/Delta') / a
 *           = -(r^3 - 3r + 2a^2) / (a*(r-1))   [for M=1]
 *
 * @param r_ph Photon orbit radius [geometric units, M=1]
 * @param a Spin parameter
 * @return Impact parameters {xi, eta}
 */
inline ImpactParams critical_impact_params(double r_ph, double a) {
  double r2 = r_ph * r_ph;
  double a2 = a * a;
  double delta = r2 - 2.0 * r_ph + a2;
  double delta_prime = 2.0 * r_ph - 2.0; // d(Delta)/dr

  ImpactParams ip;

  if (std::abs(a) < 1e-15) {
    // Schwarzschild: xi = 0 (by symmetry), eta = 27*M^2 at r=3M
    ip.xi = 0.0;
    ip.eta = r2 * r_ph * (4.0 * delta_prime - r_ph * 2.0) /
             (1e-30); // degenerate for a=0
    // Use known result: eta = 27 at r=3 for M=1
    ip.eta = 27.0;
    return ip;
  }

  // xi_c = (r^2*(r-3) + a^2*(r+1)) / (a*(1-r))  [Chandrasekhar]
  // For M=1: xi = -(r^2 + a^2)/a + 2*r*delta/(a*delta_prime)
  if (std::abs(delta_prime) < 1e-15) {
    ip.xi = 0.0;
    ip.eta = 0.0;
    return ip;
  }

  ip.xi = (r2 + a2) / a - 2.0 * r_ph * delta / (a * delta_prime);

  // eta_c from Chandrasekhar:
  // eta = r^2 * (4*delta*delta_prime' - (delta_prime)^2*r) / (a^2 * delta_prime^2)
  // With delta'' = 2:
  double eta_num = r2 * (4.0 * delta * 2.0 -
                   delta_prime * delta_prime * r_ph);
  ip.eta = eta_num / (a2 * delta_prime * delta_prime);

  // Simpler formula: eta = r^2 * [4*M*Delta - r*(r-M)^2] / (a^2 * (r-M)^2)
  // With M=1: eta = r^2 * [4*delta - r*(r-1)^2] / (a^2 * (r-1)^2)
  double rm1 = r_ph - 1.0;
  if (std::abs(rm1) > 1e-15) {
    ip.eta = r2 * (4.0 * delta - r_ph * rm1 * rm1) / (a2 * rm1 * rm1);
  }

  return ip;
}

/**
 * @brief Prograde photon orbit radius in Kerr.
 *
 * r_ph = 2 * (1 + cos(2/3 * arccos(-|a|)))   for M=1
 *
 * Range: r_ph = 3 (Schwarzschild) to r_ph = 1 (extremal Kerr prograde).
 *
 * @param a Spin parameter (|a| <= 1 for M=1)
 * @return Prograde photon orbit radius
 */
inline double prograde_photon_orbit(double a) {
  return 2.0 * (1.0 + std::cos(2.0 / 3.0 * std::acos(-std::abs(a))));
}

/**
 * @brief Retrograde photon orbit radius in Kerr.
 *
 * r_ph = 2 * (1 + cos(2/3 * arccos(|a|)))   for M=1
 *
 * Range: r_ph = 3 (Schwarzschild) to r_ph = 4 (extremal Kerr retrograde).
 */
inline double retrograde_photon_orbit(double a) {
  return 2.0 * (1.0 + std::cos(2.0 / 3.0 * std::acos(std::abs(a))));
}

} // namespace physics

#endif // PHYSICS_ANALYTIC_KERR_GEODESIC_H
