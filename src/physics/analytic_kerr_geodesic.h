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

#include <array>
#include <cmath>
#include <complex>
#include <algorithm>

#ifdef __has_include
#  if __has_include(<boost/math/special_functions/jacobi_elliptic.hpp>)
#    include <boost/math/special_functions/jacobi_elliptic.hpp>
#    include <boost/math/special_functions/ellint_1.hpp>
#define PHYSICS_HAS_BOOST_JACOBI 1 // NOLINT(cppcoreguidelines-macro-usage) -- feature-detection flag, not a constant
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
  double xi  = 0.0; // L/E
  double eta = 0.0; // Q/E^2
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
  std::array<std::complex<double>, 4> roots{};
  int nReal            = 0;                     // Number of real roots
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
[[nodiscard]] inline double radialPotential(double r, double a, double xi, double eta) {
  const double r2   = r * r;
  const double a2   = a * a;
  const double xiA  = xi - a;
  const double delta = (r2 - (2.0 * r)) + a2; // M=1

  const double term1 = (r2 + a2) - (a * xi);
  return (term1 * term1) - (delta * (eta + (xiA * xiA)));
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
  double c0 = 0.0; // constant term
  double c1 = 0.0; // linear coefficient
  double c2 = 0.0; // quadratic coefficient (R(r) = r^4 + c2*r^2 + c1*r + c0)
};

[[nodiscard]] inline QuarticCoeffs radialQuarticCoeffs(double a, double xi, double eta) {
  const double a2   = a * a;
  const double xiA  = xi - a;
  const double xiA2 = xiA * xiA;
  const double aXi  = a2 - (a * xi);

  QuarticCoeffs c;
  c.c2 = (2.0 * aXi) - eta - xiA2;
  c.c1 = 2.0 * (eta + xiA2); // M=1
  c.c0 = (aXi * aXi) - (a2 * (eta + xiA2));

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
[[nodiscard]] inline RadialRoots findRadialRoots(const QuarticCoeffs& c) {
  RadialRoots result;

  // Ferrari's resolvent cubic: y^3 - c2*y^2 - 4*c0*y + (4*c2*c0 - c1^2) = 0
  // Substituting y = t + c2/3 to get depressed cubic t^3 + pt + q = 0
  const double pCoeff = (-(c.c2 * c.c2) / 3.0) - (4.0 * c.c0);
  const double qCoeff = ((-2.0 * c.c2 * c.c2 * c.c2) / 27.0)
                      + ((4.0 * c.c2 * c.c0) / 3.0) - (c.c1 * c.c1);

  // Cardano's formula for the resolvent cubic
  const double disc = ((qCoeff * qCoeff) / 4.0) + ((pCoeff * pCoeff * pCoeff) / 27.0);

  double y1 = 0.0;
  if (disc >= 0.0) {
    const double sq = std::sqrt(disc);
    const double u  = std::cbrt((-qCoeff / 2.0) + sq);
    const double v  = std::cbrt((-qCoeff / 2.0) - sq);
    y1 = u + v + (c.c2 / 3.0);
  } else {
    // Three real roots; use trigonometric form
    const double rVal = std::sqrt(-(pCoeff * pCoeff * pCoeff) / 27.0);
    const double phi  = std::acos(-qCoeff / (2.0 * rVal));
    y1 = (2.0 * std::cbrt(rVal) * std::cos(phi / 3.0)) + (c.c2 / 3.0);
  }

  // Factor quartic: r^4 + c2*r^2 + c1*r + c0 = (r^2+alpha*r+beta)(r^2-alpha*r+gamma)
  const double a = y1 + c.c2;

  if (a < 0.0) {
    // alpha is imaginary; all roots come in complex conjugate pairs
    result.nReal = 0;
    result.type  = RadialMotionType::Plunge;
    return result;
  }

  const double alpha = std::sqrt(a);
  double beta = 0.0;
  double gamma = 0.0;

  if (std::abs(alpha) > 1e-15) {
    // Quadratic 1: r^2 + alpha*r + beta = 0; use robust relations
    beta  = (y1 / 2.0) - (c.c1 / (2.0 * alpha));
    gamma = (y1 / 2.0) + (c.c1 / (2.0 * alpha));
  } else {
    // alpha ~ 0: degenerate case
    const double disc1 = -4.0 * c.c0;
    if (disc1 < 0.0) {
      result.nReal = 0;
      result.type  = RadialMotionType::Plunge;
      return result;
    }
    const double sq = std::sqrt(disc1);
    result.roots.at(0) = std::complex<double>(sq / 2.0, 0);
    result.roots.at(1) = std::complex<double>(-sq / 2.0, 0);
    result.roots.at(2) = result.roots.at(0);
    result.roots.at(3) = result.roots.at(1);
    result.nReal = 2;
    result.type  = RadialMotionType::Transit;
    return result;
  }

  const double disc1 = (alpha * alpha) - (4.0 * beta);
  const double disc2 = (alpha * alpha) - (4.0 * gamma);

  result.nReal = 0;

  if (disc1 >= 0.0) {
    const double sq1 = std::sqrt(disc1);
    result.roots.at(0) = std::complex<double>((-alpha + sq1) / 2.0, 0);
    result.roots.at(1) = std::complex<double>((-alpha - sq1) / 2.0, 0);
    result.nReal += 2;
  } else {
    const double sq1 = std::sqrt(-disc1);
    result.roots.at(0) = std::complex<double>(-alpha / 2.0,  sq1 / 2.0);
    result.roots.at(1) = std::complex<double>(-alpha / 2.0, -sq1 / 2.0);
  }

  if (disc2 >= 0.0) {
    const double sq2 = std::sqrt(disc2);
    result.roots.at(2) = std::complex<double>((alpha + sq2) / 2.0, 0);
    result.roots.at(3) = std::complex<double>((alpha - sq2) / 2.0, 0);
    result.nReal += 2;
  } else {
    const double sq2 = std::sqrt(-disc2);
    result.roots.at(2) = std::complex<double>(alpha / 2.0,  sq2 / 2.0);
    result.roots.at(3) = std::complex<double>(alpha / 2.0, -sq2 / 2.0);
  }

  // Classify motion type
  if (result.nReal == 4) {
    result.type = RadialMotionType::Transit;
  } else if (result.nReal == 2) {
    result.type = RadialMotionType::Scatter;
  } else {
    result.type = RadialMotionType::Plunge;
  }

  // Sort real roots in descending order
  if (result.nReal >= 2) {
    for (std::size_t i = 0; i < 3; ++i) {
      for (std::size_t j = i + 1; j < 4; ++j) {
        if (result.roots.at(j).real() > result.roots.at(i).real()) {
          std::swap(result.roots.at(i), result.roots.at(j));
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
[[nodiscard]] inline double rAnalytic(double lambda, const RadialRoots& roots,
                                       double lambda0 = 0.0) {
  if (roots.nReal < 4) {
    return -1.0; // Not a transit orbit; analytic formula requires 4 real roots
  }

  const double r1 = roots.roots.at(0).real();
  const double r2 = roots.roots.at(1).real();
  const double r3 = roots.roots.at(2).real();
  const double r4 = roots.roots.at(3).real();

  // Elliptic modulus
  const double num = (r2 - r3) * (r1 - r4);
  const double den = (r1 - r3) * (r2 - r4);
  if (std::abs(den) < 1e-30) { return r3; }
  const double m = num / den;

  // Argument
  const double scale = std::sqrt(std::abs((r1 - r3) * (r2 - r4))) / 2.0;
  const double u     = scale * (lambda - lambda0);

  // Jacobi elliptic function sn(u | k) where k = sqrt(m)
  const double k     = std::sqrt(std::clamp(m, 0.0, 1.0));
  const double snVal = boost::math::jacobi_sn(k, u);
  (void)boost::math::jacobi_cn(k, u); // unused but kept for symmetry

  const double sn2    = snVal * snVal;
  const double aCoeff = (r3 * (r1 - r4)) - (r4 * (r1 - r3) * sn2);
  const double bCoeff = (r1 - r4) - ((r1 - r3) * sn2);

  if (std::abs(bCoeff) < 1e-30) { return r1; } // At turning point
  return aCoeff / bCoeff;
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
[[nodiscard]] inline double radialHalfPeriod(const RadialRoots& roots) {
  if (roots.nReal < 4) { return 0.0; }

  const double r1 = roots.roots.at(0).real();
  const double r2 = roots.roots.at(1).real();
  const double r3 = roots.roots.at(2).real();
  const double r4 = roots.roots.at(3).real();

  const double num = (r2 - r3) * (r1 - r4);
  const double den = (r1 - r3) * (r2 - r4);
  if (std::abs(den) < 1e-30) { return 0.0; }
  const double m = num / den;

  const double scale = std::sqrt(std::abs((r1 - r3) * (r2 - r4))) / 2.0;
  if (scale < 1e-30) { return 0.0; }

  const double k         = std::sqrt(std::clamp(m, 0.0, 1.0));
  const double kComplete = boost::math::ellint_1(k);
  return kComplete / scale;
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
[[nodiscard]] inline ImpactParams criticalImpactParams(double rPh, double a) {
  const double r2         = rPh * rPh;
  const double a2         = a * a;
  const double delta      = (r2 - (2.0 * rPh)) + a2;
  const double deltaPrime = (2.0 * rPh) - 2.0; // d(Delta)/dr

  ImpactParams ip;

  if (std::abs(a) < 1e-15) {
    // Schwarzschild: xi = 0 (by symmetry), eta = 27 at r=3 for M=1
    ip.xi  = 0.0;
    ip.eta = 27.0;
    return ip;
  }

  if (std::abs(deltaPrime) < 1e-15) {
    ip.xi  = 0.0;
    ip.eta = 0.0;
    return ip;
  }

  // From R(r_ph)=0 and R'(r_ph)=0 simultaneously (Gralla & Lupsasca 2020, M=1):
  //   R'=0 => r^2+a^2-a*xi = 4r*Delta/Delta'  => xi_c = (r^2+a^2)/a - 4r*Delta/(a*Delta')
  //   R =0  => eta_c = 16r^2*Delta/Delta'^2 - (xi_c - a)^2
  // Note: factor is 4 (not 2) in the xi formula.
  ip.xi = ((r2 + a2) / a) - ((4.0 * rPh * delta) / (a * deltaPrime));

  const double dp2   = deltaPrime * deltaPrime;
  const double xiA   = ip.xi - a;
  ip.eta = ((16.0 * r2 * delta) / dp2) - (xiA * xiA);

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
[[nodiscard]] inline double progradePhotonOrbit(double a) {
  return 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(-std::abs(a))));
}

/**
 * @brief Retrograde photon orbit radius in Kerr.
 *
 * r_ph = 2 * (1 + cos(2/3 * arccos(|a|)))   for M=1
 *
 * Range: r_ph = 3 (Schwarzschild) to r_ph = 4 (extremal Kerr retrograde).
 */
[[nodiscard]] inline double retrogradePhotonOrbit(double a) {
  return 2.0 * (1.0 + std::cos((2.0 / 3.0) * std::acos(std::abs(a))));
}

} // namespace physics

#endif // PHYSICS_ANALYTIC_KERR_GEODESIC_H
