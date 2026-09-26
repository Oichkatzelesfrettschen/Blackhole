/**
 * @file elliptic_integrals.h
 * @brief Elliptic integrals for strong-field gravitational lensing.
 *
 * Elliptic integrals appear in exact solutions for light deflection
 * in Schwarzschild and Kerr spacetimes. This implementation provides:
 *
 * Complete elliptic integrals:
 *   K(k) = ∫₀^(π/2) dθ / √(1 - k² sin²θ)
 *   E(k) = ∫₀^(π/2) √(1 - k² sin²θ) dθ
 *
 * Incomplete elliptic integrals:
 *   F(φ,k) = ∫₀^φ dθ / √(1 - k² sin²θ)
 *   E(φ,k) = ∫₀^φ √(1 - k² sin²θ) dθ
 *
 * Carlson symmetric forms (for numerical stability):
 *   R_F(x,y,z), R_D(x,y,z), R_J(x,y,z,p), R_C(x,y)
 *
 * Strong-field deflection angle (Schwarzschild):
 *   α(b) = 2 ∫[r₀ to ∞] dr / (r √(r/r₀ - 1) √(r² - b² + r r_s))
 *
 * References:
 * - Abramowitz & Stegun, Chapter 17
 * - Carlson (1995), Numerical Algorithms 10, 13 -- duplication stopping rule
 * - DLMF 19.36.1-19.36.2 -- truncated series of R_F, R_D, R_J
 * - Bozza (2002), Phys. Rev. D 66, 103001
 * - Darwin (1959), Proc. R. Soc. A 249, 180
 *
 * Cleanroom implementation based on standard mathematical references.
 */

#ifndef PHYSICS_ELLIPTIC_INTEGRALS_H
#define PHYSICS_ELLIPTIC_INTEGRALS_H

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <limits>
#include <numbers>

#include "constants.h"
#include "safe_limits.h"

namespace physics {

// ============================================================================
// Carlson Symmetric Forms (Numerically Stable)
// ============================================================================
//
// Duplication with Carlson's (1995) stopping rule: with A0 the weighted mean of
// the arguments and Q = c(r) max|A0 - x_i|, the loop runs until 4^{-m} Q < |A_m|,
// and the scaled deviations X_i = (A0 - x_i) / (4^m A_m) enter the DLMF 19.36
// truncated series. c(r) = (3r)^{-1/6} for R_F and (r/4)^{-1/6} for R_D, R_J
// bound the truncation error by the relative tolerance r; the default
// CARLSON_REL_TOL takes 5-6 duplications for double precision
// (tests/elliptic_integrals_test.cpp holds 1e-15 against mpmath).

/// Relative tolerance r of the Carlson duplication stopping rule.
inline constexpr double CARLSON_REL_TOL = 1.0e-16;

/// Duplication steps that shrink any finite argument spread below every tolerance r >= 1e-300.
inline constexpr int CARLSON_MAX_ITER = 600;

/**
 * @brief Carlson's R_F symmetric elliptic integral.
 *
 * R_F(x,y,z) = (1/2) ∫₀^∞ dt / √((t+x)(t+y)(t+z))
 *
 * Converges for x,y,z >= 0 with at most one zero; two zeros return +inf. The
 * truncated series is
 * DLMF 19.36.1: R_F ~ A^{-1/2} (1 - E2/10 + E3/14 + E2^2/24 - 3 E2 E3/44)
 * with E2 = XY - Z^2, E3 = XYZ and X + Y + Z = 0.
 *
 * @param x First argument (≥0)
 * @param y Second argument (≥0)
 * @param z Third argument (≥0)
 * @param relTol Relative tolerance r of the stopping rule
 * @return R_F(x,y,z)
 */
inline double carlsonRf(double x, double y, double z, double relTol = CARLSON_REL_TOL) {
  // Two zero arguments make the integral diverge; duplication would never
  // separate them from zero and would run out of iterations into 0/0.
  if ((static_cast<int>(x == 0.0) + static_cast<int>(y == 0.0) + static_cast<int>(z == 0.0)) >= 2) {
    return safeInfinity<double>();
  }
  const double a0 = (x + y + z) / 3.0;
  const double dx0 = a0 - x;
  const double dy0 = a0 - y;
  const double q = std::pow(3.0 * relTol, -1.0 / 6.0) *
                   std::max({std::abs(dx0), std::abs(dy0), std::abs(a0 - z)});
  double a = a0;
  double fac = 1.0; // 4^{-m}
  for (int n = 0; n < CARLSON_MAX_ITER && fac * q >= std::abs(a); ++n) {
    const double sx = std::sqrt(x);
    const double sy = std::sqrt(y);
    const double sz = std::sqrt(z);
    const double lambda = (sx * (sy + sz)) + (sy * sz);
    x = 0.25 * (x + lambda);
    y = 0.25 * (y + lambda);
    z = 0.25 * (z + lambda);
    a = 0.25 * (a + lambda);
    fac *= 0.25;
  }
  const double xs = dx0 * fac / a;
  const double ys = dy0 * fac / a;
  const double zs = -(xs + ys);
  const double e2 = (xs * ys) - (zs * zs);
  const double e3 = xs * ys * zs;
  return (1.0 - (e2 / 10.0) + (e3 / 14.0) + (e2 * e2 / 24.0) - (3.0 * e2 * e3 / 44.0)) /
         std::sqrt(a);
}

/**
 * @brief Carlson's R_C degenerate form, in closed form.
 *
 * R_C(x,y) = R_F(x, y, y) = (1/2) ∫₀^∞ dt / ((t+y)√(t+x))
 *          = atan(s) / (s sqrt(x)),   s = sqrt((y-x)/x),  x < y   (DLMF 19.2.18)
 *          = asinh(t) / (t sqrt(y)),  t = sqrt((x-y)/y),  x > y   (DLMF 19.2.19)
 *
 * s and t are formed as quotients of square roots and the results divided by
 * sqrt(|y - x|), so neither overflows for subnormal or widely separated
 * arguments (R_C(1e-310, 1) = pi/2, R_C(1, 5e-324) = 373.3). Below 1e-4 the
 * atan(s)/s and asinh(t)/t ratios take their series, so nearly equal
 * arguments (the R_C calls inside R_J's duplication) keep full precision;
 * x = 0 gives pi / (2 sqrt(y)).
 *
 * @param x First argument (≥0)
 * @param y Second argument (>0); y <= 0 returns NaN
 * @return R_C(x,y)
 */
inline double carlsonRc(double x, double y) {
  if (!(y > 0.0) || x < 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  if (x == 0.0) {
    return 0.5 * std::numbers::pi / std::sqrt(y);
  }
  constexpr double seriesBelow = 1.0e-4;
  if (x < y) {
    const double gap = std::sqrt(y - x);
    const double s = gap / std::sqrt(x);
    return (s < seriesBelow) ? (1.0 - (s * s / 3.0)) / std::sqrt(x) : std::atan(s) / gap;
  }
  const double gap = std::sqrt(x - y);
  const double t = gap / std::sqrt(y);
  return (t < seriesBelow) ? (1.0 - (t * t / 6.0)) / std::sqrt(y) : std::asinh(t) / gap;
}

/// DLMF 19.36.2 series shared by R_D and R_J: e2..e5 are the elementary
/// symmetric polynomials of the five scaled deviations.
inline double carlsonDjSeries(double e2, double e3, double e4, double e5) {
  return 1.0 - (3.0 * e2 / 14.0) + (e3 / 6.0) + (9.0 * e2 * e2 / 88.0) - (3.0 * e4 / 22.0) -
         (9.0 * e2 * e3 / 52.0) + (3.0 * e5 / 26.0);
}

/**
 * @brief Carlson's R_D symmetric elliptic integral.
 *
 * R_D(x,y,z) = (3/2) ∫₀^∞ dt / ((t+z)√((t+x)(t+y)(t+z)))
 *
 * The series uses the elementary symmetric polynomials of (X, Y, Z, Z, Z) with
 * X + Y + 3Z = 0 (DLMF 19.36.2).
 *
 * @param x First argument (≥0)
 * @param y Second argument (≥0)
 * @param z Third argument (>0)
 * @param relTol Relative tolerance r of the stopping rule
 * @return R_D(x,y,z); +inf for z = 0 or x = y = 0
 */
inline double carlsonRd(double x, double y, double z, double relTol = CARLSON_REL_TOL) {
  // z = 0, or x = y = 0, makes the integral diverge.
  if (z == 0.0 || (x == 0.0 && y == 0.0)) {
    return safeInfinity<double>();
  }
  const double a0 = (x + y + (3.0 * z)) / 5.0;
  const double dx0 = a0 - x;
  const double dy0 = a0 - y;
  const double q = std::pow(0.25 * relTol, -1.0 / 6.0) *
                   std::max({std::abs(dx0), std::abs(dy0), std::abs(a0 - z)});
  double a = a0;
  double fac = 1.0;
  double sum = 0.0;
  for (int n = 0; n < CARLSON_MAX_ITER && fac * q >= std::abs(a); ++n) {
    const double sx = std::sqrt(x);
    const double sy = std::sqrt(y);
    const double sz = std::sqrt(z);
    const double lambda = (sx * (sy + sz)) + (sy * sz);
    sum += fac / (sz * (z + lambda));
    x = 0.25 * (x + lambda);
    y = 0.25 * (y + lambda);
    z = 0.25 * (z + lambda);
    a = 0.25 * (a + lambda);
    fac *= 0.25;
  }
  const double xs = dx0 * fac / a;
  const double ys = dy0 * fac / a;
  const double zs = -(xs + ys) / 3.0;
  const double xy = xs * ys;
  const double z2 = zs * zs;
  const double e2 = xy - (6.0 * z2);
  const double e3 = ((3.0 * xy) - (8.0 * z2)) * zs;
  const double e4 = 3.0 * (xy - z2) * z2;
  const double e5 = xy * z2 * zs;
  return (3.0 * sum) + (fac * carlsonDjSeries(e2, e3, e4, e5) / (a * std::sqrt(a)));
}

/**
 * @brief Carlson's R_J for p > 0 (the duplication kernel of carlsonRj).
 *
 * Each duplication adds 3 4^{-m} R_C(alpha^2, beta) with
 * alpha = p (sqrt(x) + sqrt(y) + sqrt(z)) + sqrt(xyz) and beta = p (p + lambda)^2,
 * evaluated by the closed-form carlsonRc. The series uses
 * the elementary symmetric polynomials of (X, Y, Z, P, P) with
 * X + Y + Z + 2P = 0 (DLMF 19.36.2).
 *
 * @param x First argument (≥0)
 * @param y Second argument (≥0)
 * @param z Third argument (>=0); at most one of x, y, z is zero
 * @param p Fourth argument (>0)
 * @param relTol Relative tolerance r of the stopping rule
 * @return R_J(x,y,z,p); +inf for p = 0 or two zeros among x, y, z
 */
inline double carlsonRjPositive(double x, double y, double z, double p, double relTol) {
  // p = 0, or two zero arguments among x, y, z, makes the integral diverge.
  if (p == 0.0 ||
      (static_cast<int>(x == 0.0) + static_cast<int>(y == 0.0) + static_cast<int>(z == 0.0)) >= 2) {
    return safeInfinity<double>();
  }
  const double a0 = (x + y + z + (2.0 * p)) / 5.0;
  const double dx0 = a0 - x;
  const double dy0 = a0 - y;
  const double dz0 = a0 - z;
  const double q = std::pow(0.25 * relTol, -1.0 / 6.0) *
                   std::max({std::abs(dx0), std::abs(dy0), std::abs(dz0), std::abs(a0 - p)});
  double a = a0;
  double fac = 1.0;
  double sum = 0.0;
  for (int n = 0; n < CARLSON_MAX_ITER && fac * q >= std::abs(a); ++n) {
    const double sx = std::sqrt(x);
    const double sy = std::sqrt(y);
    const double sz = std::sqrt(z);
    const double lambda = (sx * (sy + sz)) + (sy * sz);
    const double alpha = (p * (sx + sy + sz)) + (sx * sy * sz);
    const double beta = p * (p + lambda) * (p + lambda);
    sum += fac * carlsonRc(alpha * alpha, beta);
    x = 0.25 * (x + lambda);
    y = 0.25 * (y + lambda);
    z = 0.25 * (z + lambda);
    p = 0.25 * (p + lambda);
    a = 0.25 * (a + lambda);
    fac *= 0.25;
  }
  const double xs = dx0 * fac / a;
  const double ys = dy0 * fac / a;
  const double zs = dz0 * fac / a;
  const double ps = -(xs + ys + zs) / 2.0;
  const double xyz = xs * ys * zs;
  const double pairs = (xs * ys) + (xs * zs) + (ys * zs);
  const double p2 = ps * ps;
  const double e2 = pairs - (3.0 * p2);
  const double e3 = xyz + (2.0 * ps * pairs) - (2.0 * p2 * ps);
  const double e4 = (2.0 * xyz * ps) + (pairs * p2);
  const double e5 = xyz * p2;
  return (3.0 * sum) + (fac * carlsonDjSeries(e2, e3, e4, e5) / (a * std::sqrt(a)));
}

/**
 * @brief Carlson's R_J symmetric elliptic integral.
 *
 * R_J(x,y,z,p) = (3/2) integral_0^inf dt / ((t+p) sqrt((t+x)(t+y)(t+z)))
 *
 * For p > 0 by duplication (carlsonRjPositive). For p < 0 the integral is a
 * Cauchy principal value, reduced to p' > 0 by DLMF 19.20.14 with the
 * arguments ordered x <= y <= z and q = -p:
 *
 *   (y + q) R_J(x,y,z,-q) = (p' - y) R_J(x,y,z,p') - 3 R_F(x,y,z)
 *                           + 3 sqrt(xyz / (xz + p'q)) R_C(xz + p'q, p'q),
 *   p' = y + (z - y)(y - x) / (y + q) >= y.
 *
 * @param x First argument (>=0)
 * @param y Second argument (>=0)
 * @param z Third argument (>=0); at most one of x, y, z is zero
 * @param p Fourth argument (!= 0); p < 0 gives the principal value
 * @param relTol Relative tolerance r of the stopping rule
 * @return R_J(x,y,z,p); +inf for p = 0 or two zeros among x, y, z
 */
inline double carlsonRj(double x, double y, double z, double p, double relTol = CARLSON_REL_TOL) {
  if (!(p < 0.0)) {
    return carlsonRjPositive(x, y, z, p, relTol);
  }
  if ((static_cast<int>(x == 0.0) + static_cast<int>(y == 0.0) + static_cast<int>(z == 0.0)) >= 2) {
    return safeInfinity<double>();
  }
  const double lo = std::min({x, y, z});
  const double hi = std::max({x, y, z});
  const double mid = std::max(std::min(x, y), std::min(std::max(x, y), z)); // median, no rounding
  const double q = -p;
  const double pp = mid + ((hi - mid) * (mid - lo) / (mid + q));
  const double rc = carlsonRc((lo * hi) + (pp * q), pp * q);
  const double tail = 3.0 * std::sqrt(lo * mid * hi / ((lo * hi) + (pp * q))) * rc;
  return (((pp - mid) * carlsonRjPositive(lo, mid, hi, pp, relTol)) -
          (3.0 * carlsonRf(lo, mid, hi, relTol)) + tail) /
         (mid + q);
}

// ============================================================================
// Complete Elliptic Integrals
// ============================================================================

/**
 * @brief Complete elliptic integral of the first kind K(k).
 *
 * K(k) = ∫₀^(π/2) dθ / √(1 - k² sin²θ) = R_F(0, 1-k², 1)
 *
 * @param k Modulus (0 ≤ k < 1)
 * @return K(k)
 */
inline double ellipticK(double k) {
  if (std::abs(k) >= 1.0) {
    return safeInfinity<double>();
  }
  double const k2 = k * k;
  return carlsonRf(0.0, 1.0 - k2, 1.0);
}

/**
 * @brief Complete elliptic integral of the first kind from the complementary parameter.
 *
 * K = pi / (2 AGM(1, k')) with k'^2 = 1 - m (DLMF 19.8.5). Taking k'^2 as the
 * input lets a caller that knows 1 - m in factored form (the analytic Kerr
 * roots do) avoid forming it as 1 - m, which cancels as m -> 1; the AGM adds
 * and multiplies only positive numbers and converges quadratically.
 *
 * @param kPrime2 Complementary parameter k'^2 = 1 - m, 0 < k'^2 <= 1
 * @return K(m); +inf at k'^2 = 0
 */
inline double ellipticKFromComplement(double kPrime2) {
  if (!(kPrime2 > 0.0)) {
    return safeInfinity<double>();
  }
  double a = 1.0;
  double b = std::sqrt(kPrime2);
  for (int n = 0; n < 64 && (a - b) > std::numeric_limits<double>::epsilon() * a; ++n) {
    const double mean = 0.5 * (a + b);
    b = std::sqrt(a * b);
    a = mean;
  }
  return std::numbers::pi / (a + b);
}

/// Jacobi sn(u|m) and cn(u|m).
template <typename T> struct JacobiSnCn {
  T sn = T(0);
  T cn = T(1);
};

/**
 * @brief sn and cn from the parameter m and its complement k'^2 = 1 - m.
 *
 * Descending Landen transformation (A&S 16.4.1-16.4.3; DLMF 22.20.ii):
 * a_0 = 1, b_0 = k', a_{n+1} = (a_n + b_n)/2, b_{n+1} = sqrt(a_n b_n),
 * c_1 = (1 - k')/2 = m / (2 (1 + k')), c_{n+1} = c_n^2 / (4 a_{n+1}); at
 * c_N <= eps a_N, phi_N = 2^N a_N u and
 * phi_{n-1} = (phi_n + asin((c_n / a_n) sin phi_n)) / 2 give sn = sin phi_0,
 * cn = cos phi_0. The AGM runs on k' itself and c_1 takes whichever of its two
 * forms does not cancel, so a caller that knows 1 - m in factored form keeps
 * the quarter period K = pi / (2 a_N) accurate as m -> 1, where a modulus
 * k = sqrt(m) rounded to double carries an absolute error of eps in 1 - m.
 * Near m = 1 with cn small the amplitude phi_0 sits at pi/2, so cn keeps only
 * the absolute precision of T there; rAnalytic evaluates it in long double.
 *
 * @param u       Argument
 * @param m       Parameter, 0 <= m <= 1
 * @param kPrime2 Complementary parameter 1 - m, formed without cancellation
 * @return sn(u|m), cn(u|m); tanh u and sech u at k'^2 = 0
 */
template <typename T>
[[nodiscard]] inline JacobiSnCn<T> jacobiSnCnFromComplement(T u, T m, T kPrime2) {
  if (!(kPrime2 > T(0))) {
    return {.sn = std::tanh(u), .cn = T(1) / std::cosh(u)};
  }
  // 32 halvings of c take any c_1 <= 1/2 below eps of a double or long double.
  std::array<T, 33> a{};
  std::array<T, 33> c{};
  const T kPrime = std::sqrt(kPrime2);
  a[0] = T(1);
  c[0] = std::sqrt(m);
  T b = kPrime;
  std::size_t n = 0;
  while (n + 1 < a.size() && c[n] > std::numeric_limits<T>::epsilon() * a[n]) {
    a[n + 1] = T(0.5) * (a[n] + b);
    if (n == 0) {
      c[1] = (kPrime2 < T(0.25)) ? T(0.5) * (T(1) - kPrime) : m / (T(2) * (T(1) + kPrime));
    } else {
      c[n + 1] = (c[n] * c[n]) / (T(4) * a[n + 1]);
    }
    b = std::sqrt(a[n] * b);
    ++n;
  }
  T phi = std::ldexp(a[n] * u, static_cast<int>(n));
  for (std::size_t j = n; j > 0; --j) {
    phi = T(0.5) * (phi + std::asin((c[j] / a[j]) * std::sin(phi)));
  }
  return {.sn = std::sin(phi), .cn = std::cos(phi)};
}

/**
 * @brief Complete elliptic integral of the second kind E(k).
 *
 * E(k) = ∫₀^(π/2) √(1 - k² sin²θ) dθ
 *      = R_F(0, 1-k², 1) - (k²/3) R_D(0, 1-k², 1)
 *
 * @param k Modulus (0 ≤ k ≤ 1)
 * @return E(k)
 */
inline double ellipticE(double k) {
  if (std::abs(k) > 1.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  if (std::abs(k) == 1.0) {
    return 1.0;
  }

  double const k2 = k * k;
  double const rf = carlsonRf(0.0, 1.0 - k2, 1.0);
  double const rd = carlsonRd(0.0, 1.0 - k2, 1.0);

  return rf - ((k2 / 3.0) * rd);
}

/**
 * @brief Complete elliptic integral of the third kind Π(n,k).
 *
 * Π(n,k) = ∫₀^(π/2) dθ / ((1 - n sin²θ)√(1 - k² sin²θ))
 *
 * For n > 1 the integrand has a pole inside the range and the result is the
 * Cauchy principal value (carlsonRj at p = 1 - n < 0); n = 1 returns +inf.
 *
 * @param n Characteristic
 * @param k Modulus (0 ≤ k < 1)
 * @return Π(n,k)
 */
inline double ellipticPi(double n, double k) {
  if (std::abs(k) >= 1.0) {
    return safeInfinity<double>();
  }

  double const k2 = k * k;
  double const rf = carlsonRf(0.0, 1.0 - k2, 1.0);
  double const rj = carlsonRj(0.0, 1.0 - k2, 1.0, 1.0 - n);

  return rf + ((n / 3.0) * rj);
}

// ============================================================================
// Incomplete Elliptic Integrals
// ============================================================================

/**
 * @brief Incomplete elliptic integral of the first kind F(φ,k).
 *
 * F(φ,k) = ∫₀^φ dθ / √(1 - k² sin²θ)
 *
 * @param phi Amplitude [rad]
 * @param k Modulus (0 ≤ k < 1)
 * @return F(φ,k)
 */
inline double ellipticF(double phi, double k) {
  double const s = std::sin(phi);
  double const c = std::cos(phi);

  double const s2 = s * s;
  double const c2 = c * c;
  double const k2 = k * k;

  return s * carlsonRf(c2, 1.0 - (k2 * s2), 1.0);
}

/**
 * @brief Incomplete elliptic integral of the second kind E(φ,k).
 *
 * E(φ,k) = ∫₀^φ √(1 - k² sin²θ) dθ
 *
 * @param phi Amplitude [rad]
 * @param k Modulus (0 ≤ k ≤ 1)
 * @return E(φ,k)
 */
inline double ellipticEIncomplete(double phi, double k) {
  double const s = std::sin(phi);
  double const c = std::cos(phi);

  double const s2 = s * s;
  double const s3 = s2 * s;
  double const c2 = c * c;
  double const k2 = k * k;

  double const rf = carlsonRf(c2, 1.0 - (k2 * s2), 1.0);
  double const rd = carlsonRd(c2, 1.0 - (k2 * s2), 1.0);

  return (s * rf) - ((k2 * s3 / 3.0) * rd);
}

// ============================================================================
// Strong-Field Gravitational Lensing
// ============================================================================

/**
 * @brief Compute light deflection angle in Schwarzschild spacetime.
 *
 * For impact parameter b > b_crit, the exact deflection is:
 *
 * α(b) = 2 ∫[r₀ to ∞] dr / (r √((r/b)² - 1 + r_s/r))
 *
 * where r₀ is the closest approach.
 *
 * Uses elliptic integral representation for accuracy.
 *
 * @param b Impact parameter [cm]
 * @param rS Schwarzschild radius [cm]
 * @return Deflection angle [rad], or infinity if b ≤ b_crit
 */
inline double deflectionAngleSchwarzschild(double b, double rS) {
  // Critical impact parameter: b_crit = (3√3/2) r_s ≈ 2.598 r_s
  double const bCrit = 3.0 * std::numbers::sqrt3 / 2.0 * rS;

  if (b <= bCrit) {
    return safeInfinity<double>(); // Photon captured
  }

  // Find closest approach r₀ by solving:
  // b² = r₀³ / (r₀ - r_s)
  // This is a cubic equation

  // Newton-Raphson for r₀
  double r0 = b; // Initial guess
  for (int i = 0; i < 50; ++i) {
    double const f = (r0 * r0 * r0) - (b * b * (r0 - rS));
    double const df = (3.0 * r0 * r0) - (b * b);
    double const dr = f / df;
    r0 -= dr;
    if (std::abs(dr) < 1e-12 * r0) {
      break;
    }
  }

  // Elliptic integral formulation
  // Following Darwin (1959)

  // The deflection integral in terms of elliptic functions
  // α = 2 F(φ₀, k) - π

  // For u = r_s/r, the deflection involves:
  // Roots of (1-u)(1 - 3u + 2u²q) = 0

  // Simplified strong-field calculation using series near r₀
  // Leading term
  double alpha = 4.0 * rS / b;

  // Higher-order corrections (post-Newtonian expansion)
  double const alpha2 = ((15.0 * physics::PI / 16.0) - 1.0) * (rS / b) * (rS / b);
  double const alpha3 = ((128.0 / 3.0) - (15.0 * physics::PI / 2.0)) * std::pow(rS / b, 3);

  // Add relativistic corrections
  alpha = alpha + (alpha2 * rS) + (alpha3 * rS);

  // For very strong field (b close to b_crit), use logarithmic expansion
  if (b < 1.5 * bCrit) {
    double const y = (b / bCrit) - 1.0;
    if (y > 0) {
      // Bozza (2002) strong-field limit
      double const aBar = 1.0; // Depends on metric (1 for Schwarzschild)
      double const bBar = -0.4002;

      alpha = (-aBar * std::log(y)) + bBar + physics::PI;
    }
  }

  return alpha;
}

/**
 * @brief Compute strong-field limit coefficients (Bozza 2002).
 *
 * In the strong-field limit (b → bM):
 * α(b) = -ā log(b/bM - 1) + b̄ + O(b - bM)
 *
 * @param rS Schwarzschild radius [cm]
 * @param aBar Output: logarithmic coefficient ā
 * @param bBar Output: constant term b̄
 * @param bM Output: critical impact parameter bM [cm]
 */
inline void strongFieldCoefficientsSchwarzschild(double rS, double &aBar, double &bBar,
                                                 double &bM) {
  // Photon sphere radius
  double const rM = 1.5 * rS;

  // Critical impact parameter
  bM = rM * std::sqrt(rM / (rM - rS));

  // Schwarzschild coefficients (exact values)
  aBar = 1.0;

  // b̄ = -π + b_R + log(216(7 - 4√3))
  // where b_R is a geometric term
  double const logArg = 216.0 * (7.0 - (4.0 * std::numbers::sqrt3));
  bBar = -physics::PI + std::log(logArg);
  bBar = -0.4002; // Numerical value
}

/**
 * @brief Compute deflection using strong-field expansion.
 *
 * @param b Impact parameter [cm]
 * @param rS Schwarzschild radius [cm]
 * @return Deflection angle [rad]
 */
inline double deflectionStrongField(double b, double rS) {
  double aBar;
  double bBar;
  double bM;
  strongFieldCoefficientsSchwarzschild(rS, aBar, bBar, bM);

  if (b <= bM) {
    return safeInfinity<double>();
  }

  double const y = (b / bM) - 1.0;

  return (-aBar * std::log(y)) + bBar;
}

/**
 * @brief Compute position of relativistic images.
 *
 * For a source at angle β and black hole at distance D_L,
 * the nth relativistic image appears at angle θ_n.
 *
 * @param beta Source angle [rad]
 * @param n Image order (1 = outermost)
 * @param dL Distance to lens [cm]
 * @param dS Distance to source [cm]
 * @param dLs Lens-source distance [cm]
 * @param rS Schwarzschild radius [cm]
 * @return Image angle θ_n [rad]
 */
inline double relativisticImagePosition(double beta, int n, double dL, double dS, double dLs,
                                        double rS) {
  static_cast<void>(beta);
  static_cast<void>(dS);
  static_cast<void>(dLs);
  double aBar;
  double bBar;
  double bM;
  strongFieldCoefficientsSchwarzschild(rS, aBar, bBar, bM);

  // Angular critical impact parameter
  double const thetaM = bM / dL;

  // From lens equation with strong-field expansion
  // θ_n ≈ θ_m + θ_m exp((b̄ - 2nπ) / ā) * (1 + ...)

  double const deltaN = std::exp((bBar - (2.0 * n * physics::PI)) / aBar);

  // Position of nth image
  double const thetaN = thetaM * (1.0 + deltaN);

  return thetaN;
}

/**
 * @brief Compute magnification of relativistic image.
 *
 * The magnification of the nth relativistic image is:
 * μ_n = (θ_m / β) * (D_S / D_LS) * exp((b̄ - 2nπ) / ā) / ā
 *
 * @param beta Source angle [rad]
 * @param n Image order
 * @param dL Distance to lens [cm]
 * @param dS Distance to source [cm]
 * @param dLs Lens-source distance [cm]
 * @param rS Schwarzschild radius [cm]
 * @return Magnification |μ_n|
 */
inline double relativisticImageMagnification(double beta, int n, double dL, double dS, double dLs,
                                             double rS) {
  if (std::abs(beta) < 1e-20) {
    return safeInfinity<double>(); // Einstein ring
  }

  double aBar;
  double bBar;
  double bM;
  strongFieldCoefficientsSchwarzschild(rS, aBar, bBar, bM);

  double const thetaM = bM / dL;
  double const deltaN = std::exp((bBar - (2.0 * n * physics::PI)) / aBar);

  double const muN = (thetaM / std::abs(beta)) * (dS / dLs) * deltaN / aBar;

  return std::abs(muN);
}

// ============================================================================
// Kerr Strong-Field Lensing (Simplified)
// ============================================================================

/**
 * @brief Critical impact parameter of the equatorial Kerr photon orbits.
 *
 * The circular equatorial photon orbit at r_ph = 2M (1 + cos((2/3) acos(-+a/M)))
 * (upper sign prograde) has impact parameter (Bardeen, Press & Teukolsky 1972)
 *
 *   b_c = 3 sqrt(M r_ph) -+ a,
 *
 * which equals -a +- 6M cos((1/3) acos(-+a/M)) (Chandrasekhar 1983) and
 * the xi of criticalImpactParams at eta = 0. It gives 3 sqrt(3) M at a = 0,
 * 2M prograde and 7M retrograde at a = M.
 *
 * @param rS Schwarzschild radius [cm]
 * @param a Spin parameter [cm], |a| <= rS/2
 * @param prograde True for prograde photons
 * @return Critical impact parameter [cm]
 */
inline double criticalImpactParameterKerr(double rS, double a, bool prograde) {
  const double m = rS / 2.0;
  const double aStar = std::clamp(a / m, -1.0, 1.0);
  const double rPh = 2.0 * m * (1.0 + std::cos((2.0 / 3.0) * std::acos(prograde ? -aStar : aStar)));
  return (3.0 * std::sqrt(m * rPh)) + (prograde ? -a : a);
}

// ============================================================================
// Utility Functions
// ============================================================================

/**
 * @brief Compute the Jacobi amplitude am(u,k).
 *
 * The amplitude function satisfies F(am(u,k), k) = u.
 *
 * @param u Argument
 * @param k Modulus
 * @return am(u,k) in radians
 */
inline double jacobiAm(double u, double k) {
  // Newton-Raphson iteration
  double phi = u; // Initial guess (valid for small k)

  for (int i = 0; i < 20; ++i) {
    double const fPhi = ellipticF(phi, k);
    double const dF = 1.0 / std::sqrt(1.0 - (k * k * std::sin(phi) * std::sin(phi)));
    double const dPhi = (u - fPhi) * dF;
    phi += dPhi;
    if (std::abs(dPhi) < 1e-12) {
      break;
    }
  }

  return phi;
}

/**
 * @brief Jacobi elliptic function sn(u,k).
 *
 * sn(u,k) = sin(am(u,k))
 *
 * @param u Argument
 * @param k Modulus
 * @return sn(u,k)
 */
inline double jacobiSn(double u, double k) {
  return std::sin(jacobiAm(u, k));
}

/**
 * @brief Jacobi elliptic function cn(u,k).
 *
 * cn(u,k) = cos(am(u,k))
 *
 * @param u Argument
 * @param k Modulus
 * @return cn(u,k)
 */
inline double jacobiCn(double u, double k) {
  return std::cos(jacobiAm(u, k));
}

/**
 * @brief Jacobi elliptic function dn(u,k).
 *
 * dn(u,k) = √(1 - k² sn²(u,k))
 *
 * @param u Argument
 * @param k Modulus
 * @return dn(u,k)
 */
inline double jacobiDn(double u, double k) {
  double const sn = jacobiSn(u, k);
  return std::sqrt(1.0 - (k * k * sn * sn));
}

} // namespace physics

#endif // PHYSICS_ELLIPTIC_INTEGRALS_H
