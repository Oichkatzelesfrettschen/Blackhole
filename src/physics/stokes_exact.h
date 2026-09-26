/**
 * @file stokes_exact.h
 * @brief Closed-form propagator of the polarized transfer equation over a
 *        constant-coefficient segment.
 *
 * The polarized transfer equation dS/ds = J - K S has the propagation matrix
 *
 *   K = alpha_I 1 + K',   K' = | 0    eta^T    |
 *                              | eta  -[rho]_x |
 *
 * with the dichroism vector eta = (alpha_Q, alpha_U, alpha_V) and the Faraday
 * vector rho = (rho_Q, rho_U, rho_V). K' is a generator of the Lorentz group
 * SO(1,3): eta boosts and rho rotates. Written out in the (I, Q, U, V) basis,
 *
 *   K = | alpha_I  alpha_Q  alpha_U  alpha_V |
 *       | alpha_Q  alpha_I  rho_V   -rho_U   |
 *       | alpha_U -rho_V    alpha_I  rho_Q   |
 *       | alpha_V  rho_U   -rho_Q    alpha_I |
 *
 * which is the matrix of stokes_transport.h.
 *
 * With the complex vector w = eta + i rho, the eigenvalues of K' are +-x1 and
 * +-i x2, where
 *
 *   (x1 + i x2)^2 = w.w = |eta|^2 - |rho|^2 + 2 i eta.rho,
 *
 * so one complex square root replaces a 4x4 matrix exponential. The minimal
 * polynomial (K'^2 - x1^2)(K'^2 + x2^2) makes every analytic function of K' a
 * cubic in K' (Landi Degl'Innocenti & Landi Degl'Innocenti 1985):
 *
 *   f(K') = c0 - c1 K' + c2 K'^2 - c3 K'^3.
 *
 * The segment solution is
 *
 *   S(s) = e^{-alpha_I s} e^{-K' s} S0 + (integral_0^s e^{-alpha_I t} e^{-K' t} dt) J,
 *
 * evaluated here in optical-depth units: tau = alpha_I s, and x1, x2 are the
 * eigenvalue magnitudes of K' s. The homogeneous coefficients are
 *
 *   c0 = (x2^2 cosh x1 + x1^2 cos x2) / D,        D = x1^2 + x2^2
 *   c1 = (x2^2 sinh(x1)/x1 + x1^2 sin(x2)/x2) / D
 *   c2 = (cosh x1 - cos x2) / D
 *   c3 = (sinh(x1)/x1 - sin(x2)/x2) / D
 *
 * and the source coefficients are the same functions of u x1, u x2 integrated
 * against e^{-tau u} over u in [0, 1]. Every cancellation-prone combination has
 * a second evaluation that avoids it:
 *   - max(x1, x2) < 0.1, which includes w.w = 0 (K'^3 = 0 for a null
 *     rotation), uses the polynomial series in a = x1^2, b = x2^2 with the
 *     decay moments M_n = integral_0^1 u^n e^{-tau u} du; nothing divides by D.
 *   - The difference (Ich - Ic)/D and its odd twin use a D-free closed form
 *     once tau >= max(1, 2 x1).
 *   - x1 and x2 come from the stable complex square root: the larger of the two
 *     takes sqrt((|w.w| + |Re w.w|)/2) and the smaller is |Im w.w| divided by
 *     twice it, so neither suffers the h + sqrt(h^2 + (eta.rho)^2) cancellation.
 *   - The decay factor e^{-tau} is folded into cosh and sinh before they are
 *     formed, so an optically thick segment with large x1 never forms inf * 0.
 *   - Once an eigenvalue reaches 1 and the generator is far from null, the
 *     cubic's odd terms c1 K' and c3 K'^3 cancel to O(1) from size x2 (pure
 *     Faraday rotation by 1e12 rad lost 1e-4). There the step splits K' into
 *     commuting unit boost and rotation generators A, B (lorentzAxes) and
 *     applies cosh, sinh, cos and sin of x1 and x2 to O(1) matrices, so a
 *     Faraday depth of 1e15 along one axis stays within a few ulp; along a
 *     general axis the rounding of |rho| ds itself limits the angle to about
 *     eps x2.
 *
 * alpha_I < 0 (gain, as in masers) is supported: the decay moments switch to
 * series that stay positive for tau < 0, the closed forms over tau^2 - x1^2
 * require tau >= 1, and the split form requires tau >= 0.1, so a gain segment
 * always takes the direct integral's cancellation-free branches.
 *
 * StokesSourceForm::DirectIntegral is the default and holds a 1e-12 relative
 * gate against a 5x5 matrix-exponential referee in every tested regime,
 * including optically thin Faraday-thick segments, gain down to tau = -40 and w.w = 0
 * (tests/stokes_exact_test.cpp, scripts/gen_stokes_reference.py).
 * StokesSourceForm::SteadyStateSplit evaluates S = S_inf + e^{-K s}(S0 - S_inf)
 * with S_inf = K^{-1} J. Its contract is a 1e-9 budget for alpha_I s >= 0.1
 * through Faraday depth 1000, where the tests gate it: S_inf ~ J / alpha_I
 * cancels against S0, so its rounding error grows as 1 / (alpha_I s). Below
 * that optical depth, or where K is singular, it evaluates the direct integral.
 *
 * References:
 *   - Landi Degl'Innocenti & Landi Degl'Innocenti (1985), Solar Phys. 97, 239.
 *   - Landi Degl'Innocenti & Landolfi (2004), Polarization in Spectral Lines, 8.3.
 */

#ifndef PHYSICS_STOKES_EXACT_H
#define PHYSICS_STOKES_EXACT_H

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>

namespace physics {

/// Stokes-space four-vector (I, Q, U, V) or emission vector (jI, jQ, jU, jV).
using StokesArray = std::array<double, 4>;

/**
 * @brief Propagation-matrix coefficients: alpha_I 1 plus the Lorentz generator.
 *
 * Absorption coefficients in [cm^-1], Faraday coefficients in [rad/cm]; any
 * consistent inverse-length unit works because the propagator only sees their
 * products with the segment length.
 */
struct StokesGenerator {
  double alphaI = 0.0; ///< Total absorption
  double alphaQ = 0.0; ///< Linear dichroism, Q axis
  double alphaU = 0.0; ///< Linear dichroism, U axis
  double alphaV = 0.0; ///< Circular dichroism
  double rhoQ = 0.0;   ///< Faraday conversion, Q axis
  double rhoU = 0.0;   ///< Faraday conversion, U axis
  double rhoV = 0.0;   ///< Faraday rotation
};

/// Evaluation of the emission term of the segment solution.
enum class StokesSourceForm {
  DirectIntegral,  ///< integral_0^s e^{-K t} dt J; accurate at every optical depth
  SteadyStateSplit ///< K^{-1} J split; 1e-9 budget for alpha_I s >= 0.1
};

namespace stokes_exact_detail {

/// Highest decay moment the small-generator series reads.
inline constexpr std::size_t MOMENT_COUNT = 12;

/// Series and closed forms switch at this eigenvalue magnitude.
inline constexpr double SMALL_EIGENVALUE = 0.1;

/// Above this optical depth the upward moment recurrence is stable for every order used.
inline constexpr double MOMENT_UPWARD_TAU = 30.0;

using Moments = std::array<double, MOMENT_COUNT>;

/// 1 / n! for n < MOMENT_COUNT; the series multiply by it rather than divide.
inline constexpr std::array<double, MOMENT_COUNT> INV_FACTORIAL = {
    1.0,         1.0,          1.0 / 2.0,     1.0 / 6.0,      1.0 / 24.0,      1.0 / 120.0,
    1.0 / 720.0, 1.0 / 5040.0, 1.0 / 40320.0, 1.0 / 362880.0, 1.0 / 3628800.0, 1.0 / 39916800.0};

/// Cubic-in-K' coefficients of f(K') = c0 - c1 K' + c2 K'^2 - c3 K'^3.
struct CubicCoeffs {
  double c0 = 0.0;
  double c1 = 0.0;
  double c2 = 0.0;
  double c3 = 0.0;
};

/// Lorentz part K' applied to v, for a generator already scaled by the segment length.
[[nodiscard]] inline StokesArray applyLorentzPart(const StokesGenerator &k,
                                                  const StokesArray &v) noexcept {
  return {(k.alphaQ * v[1]) + (k.alphaU * v[2]) + (k.alphaV * v[3]),
          (k.alphaQ * v[0]) + (k.rhoV * v[2]) - (k.rhoU * v[3]),
          (k.alphaU * v[0]) - (k.rhoV * v[1]) + (k.rhoQ * v[3]),
          (k.alphaV * v[0]) + (k.rhoU * v[1]) - (k.rhoQ * v[2])};
}

/// sinh(x)/x - 1 without cancellation near x = 0.
[[nodiscard]] inline double sinhcMinusOne(double x) noexcept {
  const double x2 = x * x;
  if (std::abs(x) < SMALL_EIGENVALUE) {
    return (x2 / 6.0) *
           (1.0 +
            ((x2 / 20.0) * (1.0 + ((x2 / 42.0) * (1.0 + ((x2 / 72.0) * (1.0 + (x2 / 110.0))))))));
  }
  return (std::sinh(x) / x) - 1.0;
}

/// sin(x)/x - 1 without cancellation near x = 0.
[[nodiscard]] inline double sincMinusOne(double x) noexcept {
  const double x2 = x * x;
  if (std::abs(x) < SMALL_EIGENVALUE) {
    return -(x2 / 6.0) *
           (1.0 -
            ((x2 / 20.0) * (1.0 - ((x2 / 42.0) * (1.0 - ((x2 / 72.0) * (1.0 - (x2 / 110.0))))))));
  }
  return (std::sin(x) / x) - 1.0;
}

/// (1 - e^{-y}) / y, the decay integral over a unit segment at rate y.
[[nodiscard]] inline double decayIntegral(double y) noexcept {
  if (std::abs(y) < 1.0e-8) {
    return 1.0 - (0.5 * y);
  }
  return -std::expm1(-y) / y;
}

/**
 * @brief Decay moments M_n = integral_0^1 u^n e^{-tau u} du, n = 0..11.
 *
 * tau < 0 is a gain segment (stimulated emission, masers). Every branch adds
 * or subtracts only terms that cannot cancel:
 *   - 0 <= tau <= 30: the top moment from its positive series
 *     M_11 = e^{-tau} sum_k tau^k / (12 * 13 * ... * (12 + k)), then the
 *     downward recurrence M_{n-1} = (tau M_n + e^{-tau}) / n, all positive.
 *   - -30 <= tau < 0: each moment from its positive series in g = -tau,
 *     M_n = sum_k g^k / (k! (n + k + 1)); the tau >= 0 series alternates here.
 *   - |tau| > 30: the upward recurrence M_n = (n M_{n-1} - e^{-tau}) / tau
 *     from M_0 = (1 - e^{-tau}) / tau. For tau > 30 e^{-tau} is negligible;
 *     for tau < -30 it reads M_n = (e^g - n M_{n-1}) / g with
 *     n M_{n-1} <= (11/30) e^g, so the subtraction loses under one bit.
 */
[[nodiscard]] inline Moments decayMoments(double tau) noexcept {
  Moments m{};
  const double e = std::exp(-tau);
  if (std::abs(tau) > MOMENT_UPWARD_TAU) {
    m[0] = -std::expm1(-tau) / tau;
    for (std::size_t n = 1; n < MOMENT_COUNT; ++n) {
      m[n] = ((static_cast<double>(n) * m[n - 1]) - e) / tau;
    }
    return m;
  }
  if (tau < 0.0) {
    const double g = -tau;
    double power = 1.0; // g^k / k!
    for (int k = 0; k < 400; ++k) {
      for (std::size_t n = 0; n < MOMENT_COUNT; ++n) {
        m[n] += power / (static_cast<double>(n) + static_cast<double>(k) + 1.0);
      }
      power *= g / static_cast<double>(k + 1);
      // M_11 is the smallest moment. Past k = 2g successive terms at least
      // halve, so every remaining tail is below 2 * power.
      if (power <= 1.0e-17 * m[MOMENT_COUNT - 1] && static_cast<double>(k) > 2.0 * g) {
        break;
      }
    }
    return m;
  }
  constexpr auto topOrder = static_cast<double>(MOMENT_COUNT - 1);
  double term = 1.0 / (topOrder + 1.0);
  double sum = term;
  for (int k = 1; k < 400; ++k) {
    term *= tau / (topOrder + 1.0 + static_cast<double>(k));
    sum += term;
    if (term <= 1.0e-17 * sum) {
      break;
    }
  }
  m[MOMENT_COUNT - 1] = e * sum;
  for (std::size_t n = MOMENT_COUNT - 1; n > 0; --n) {
    m[n - 1] = ((tau * m[n]) + e) / static_cast<double>(n);
  }
  return m;
}

/// Unit moments: evaluating the series with M_n = 1 gives the homogeneous coefficients.
[[nodiscard]] inline Moments unitMoments() noexcept {
  Moments m{};
  m.fill(1.0);
  return m;
}

/**
 * @brief Small-generator series of the cubic coefficients, max(x1, x2) < 0.1.
 *
 * With a = x1^2, b = x2^2, f_n = M_n / n! and the polynomials
 * p_0 = 0, p_1 = 1, p_{k+1} = (a - b) p_k + a b p_{k-1}
 * (p_k = (a^k - (-b)^k) / (a + b) without the division):
 *
 *   c0 = f_0 + a b sum_{k>=2} p_{k-1} f_{2k}
 *   c1 = f_1 + a b sum_{k>=2} p_{k-1} f_{2k+1}
 *   c2 = sum_{k>=1} p_k f_{2k}
 *   c3 = sum_{k>=1} p_k f_{2k+1}
 *
 * Terms through k = 5 leave a truncation below 1e-18 relative at x < 0.1.
 */
[[nodiscard]] inline CubicCoeffs smallGeneratorSeries(double a, double b,
                                                      const Moments &m) noexcept {
  std::array<double, 6> p{};
  p[1] = 1.0;
  for (std::size_t k = 1; k + 1 < p.size(); ++k) {
    p[k + 1] = ((a - b) * p[k]) + (a * b * p[k - 1]);
  }
  CubicCoeffs c{.c0 = m[0], .c1 = m[1], .c2 = 0.0, .c3 = 0.0};
  double evenTail = 0.0;
  double oddTail = 0.0;
  for (std::size_t k = 1; k <= 5; ++k) {
    c.c2 += p[k] * m[2 * k] * INV_FACTORIAL[2 * k];
    c.c3 += p[k] * m[(2 * k) + 1] * INV_FACTORIAL[(2 * k) + 1];
    if (k >= 2) {
      evenTail += p[k - 1] * m[2 * k] * INV_FACTORIAL[2 * k];
      oddTail += p[k - 1] * m[(2 * k) + 1] * INV_FACTORIAL[(2 * k) + 1];
    }
  }
  c.c0 += a * b * evenTail;
  c.c1 += a * b * oddTail;
  return c;
}

/**
 * @brief Elementary functions of one segment, each evaluated once.
 *
 * The hyperbolic values carry the decay factor e^{-tau}: below x1 = 20 they
 * come from sinh(x1/2), above it from e^{x1 - tau}, so an optically thick
 * segment with a large real eigenvalue never forms cosh(x1) alone.
 */
struct SegmentFunctions {
  double tau = 0.0;
  double e = 1.0; ///< e^{-tau}
  double x1 = 0.0;
  double x2 = 0.0;
  double a = 0.0;              ///< x1^2
  double b = 0.0;              ///< x2^2
  double eCoshMinusOne = 0.0;  ///< e^{-tau} (cosh x1 - 1)
  double eSinhc = 1.0;         ///< e^{-tau} sinh(x1) / x1
  double eSinhcMinusOne = 0.0; ///< e^{-tau} (sinh(x1) / x1 - 1)
  double cosX2 = 1.0;
  double sinX2 = 0.0;
  double oneMinusCosX2 = 0.0;
  double sincMinusOneX2 = 0.0; ///< sin(x2) / x2 - 1
};

[[nodiscard]] inline SegmentFunctions segmentFunctions(double tau, double x1, double x2) noexcept {
  constexpr double largeArgument = 20.0;
  SegmentFunctions f{
      .tau = tau, .e = std::exp(-tau), .x1 = x1, .x2 = x2, .a = x1 * x1, .b = x2 * x2};
  if (x1 < largeArgument) {
    const double sh = std::sinh(0.5 * x1);
    const double scm1 =
        (x1 < SMALL_EIGENVALUE)
            ? sinhcMinusOne(x1)
            : ((2.0 * sh * std::sqrt(1.0 + (sh * sh))) / std::max(x1, SMALL_EIGENVALUE)) - 1.0;
    f.eCoshMinusOne = f.e * 2.0 * sh * sh;
    f.eSinhc = f.e * (1.0 + scm1);
    f.eSinhcMinusOne = f.e * scm1;
  } else {
    const double half = 0.5 * std::exp(x1 - tau);
    const double em = std::exp(-x1);
    f.eCoshMinusOne = half * (1.0 - em) * (1.0 - em);
    f.eSinhc = half * (1.0 - (em * em)) / std::max(x1, largeArgument);
    f.eSinhcMinusOne = f.eSinhc - f.e;
  }
  const double s = std::sin(0.5 * x2);
  const double c = std::cos(0.5 * x2);
  f.sinX2 = 2.0 * s * c;
  f.cosX2 = (c - s) * (c + s);
  f.oneMinusCosX2 = 2.0 * s * s;
  f.sincMinusOneX2 =
      (x2 < SMALL_EIGENVALUE) ? sincMinusOne(x2) : (f.sinX2 / std::max(x2, SMALL_EIGENVALUE)) - 1.0;
  return f;
}

/// e^{-tau} times the homogeneous coefficients of e^{-K' s}.
[[nodiscard]] inline CubicCoeffs dampedHomogeneous(const SegmentFunctions &f) noexcept {
  if (std::max(f.x1, f.x2) < SMALL_EIGENVALUE) {
    const CubicCoeffs c = smallGeneratorSeries(f.a, f.b, unitMoments());
    return {.c0 = f.e * c.c0, .c1 = f.e * c.c1, .c2 = f.e * c.c2, .c3 = f.e * c.c3};
  }
  // One scalar reciprocal: a vectorized division by d can carry a zero padding lane.
  const double invD = 1.0 / std::max(f.a + f.b, SMALL_EIGENVALUE * SMALL_EIGENVALUE);
  return {.c0 = f.e + (((f.b * f.eCoshMinusOne) - (f.a * f.e * f.oneMinusCosX2)) * invD),
          .c1 = ((f.b * f.eSinhc) + (f.a * f.e * (1.0 + f.sincMinusOneX2))) * invD,
          .c2 = (f.eCoshMinusOne + (f.e * f.oneMinusCosX2)) * invD,
          .c3 = (f.eSinhcMinusOne - (f.e * f.sincMinusOneX2)) * invD};
}

/// Integrals over u in [0,1] of e^{-tau u} times cosh, sinh/x, cos, sin/x of the eigenvalues.
struct DecayIntegrals {
  double coshInt = 0.0; ///< integral e^{-tau u} cosh(x1 u)
  double sinhInt = 0.0; ///< integral e^{-tau u} sinh(x1 u) / x1
  double cosInt = 0.0;  ///< integral e^{-tau u} cos(x2 u)
  double sinInt = 0.0;  ///< integral e^{-tau u} sin(x2 u) / x2
};

/// True where tau >= max(1, 2 x1): the closed forms over tau^2 - x1^2 hold full precision.
[[nodiscard]] inline bool opticallyThick(const SegmentFunctions &f) noexcept {
  return f.tau >= std::max(1.0, 2.0 * f.x1);
}

[[nodiscard]] inline DecayIntegrals decayIntegrals(const SegmentFunctions &f,
                                                   const Moments &m) noexcept {
  DecayIntegrals r;
  // Every branch is chosen before it divides, and each divisor is clamped to
  // the range its branch guarantees, so no 0/0 or x/0 is formed even when a
  // later branch overwrites the value or the compiler evaluates both arms of a
  // select (x1 = 0 would otherwise raise FE_INVALID).
  const bool thick = opticallyThick(f);
  if (thick) {
    const double p = (f.tau * f.tau) - f.a;
    const double eCosh = f.eCoshMinusOne + f.e;
    r.coshInt = (f.tau - ((f.tau * eCosh) + (f.a * f.eSinhc))) / std::max(p, 0.5);
    if (f.x1 >= SMALL_EIGENVALUE) {
      r.sinhInt = (1.0 - (eCosh + (f.tau * f.eSinhc))) / std::max(p, 0.5);
    }
  } else {
    const double lo = decayIntegral(f.tau - f.x1);
    const double hi = decayIntegral(f.tau + f.x1);
    r.coshInt = 0.5 * (lo + hi);
    if (f.x1 >= SMALL_EIGENVALUE) {
      r.sinhInt = (lo - hi) / (2.0 * std::max(f.x1, SMALL_EIGENVALUE));
    }
  }
  if (f.x1 < SMALL_EIGENVALUE) {
    double pw = 1.0;
    for (std::size_t k = 0; k <= 5; ++k) {
      r.sinhInt += pw * m[(2 * k) + 1] * INV_FACTORIAL[(2 * k) + 1];
      pw *= f.a;
    }
  }
  if (f.x2 < SMALL_EIGENVALUE) {
    double pw = 1.0;
    for (std::size_t k = 0; k <= 5; ++k) {
      r.cosInt += pw * m[2 * k] * INV_FACTORIAL[2 * k];
      r.sinInt += pw * m[(2 * k) + 1] * INV_FACTORIAL[(2 * k) + 1];
      pw *= -f.b;
    }
  } else {
    const double oneMinusEC = (-std::expm1(-f.tau) * f.cosX2) + f.oneMinusCosX2;
    const double den = std::max((f.tau * f.tau) + f.b, SMALL_EIGENVALUE * SMALL_EIGENVALUE);
    r.cosInt = ((f.tau * oneMinusEC) + (f.x2 * f.e * f.sinX2)) / den;
    r.sinInt = (oneMinusEC - (f.tau * f.e * (1.0 + f.sincMinusOneX2))) / den;
  }
  return r;
}

/// Coefficients of integral_0^1 e^{-tau u} e^{-K' s u} du as a cubic in K' s.
[[nodiscard]] inline CubicCoeffs integratedCoeffs(const SegmentFunctions &f) noexcept {
  // The moments feed only the series branches, taken when an eigenvalue is small.
  const Moments m = (std::min(f.x1, f.x2) < SMALL_EIGENVALUE) ? decayMoments(f.tau) : Moments{};
  if (std::max(f.x1, f.x2) < SMALL_EIGENVALUE) {
    return smallGeneratorSeries(f.a, f.b, m);
  }
  const double d = std::max(f.a + f.b, SMALL_EIGENVALUE * SMALL_EIGENVALUE);
  const DecayIntegrals r = decayIntegrals(f, m);
  CubicCoeffs c{.c0 = ((f.b * r.coshInt) + (f.a * r.cosInt)) / d,
                .c1 = ((f.b * r.sinhInt) + (f.a * r.sinInt)) / d,
                .c2 = 0.0,
                .c3 = 0.0};
  if (opticallyThick(f)) {
    // (Ich - Ic)/D and (Ish - Is)/D with the D-free parts tau/(P Qd) and
    // 1/(P Qd) separated from the e^{-tau} brackets, P = tau^2 - a, Qd = tau^2 + b.
    const double p = (f.tau * f.tau) - f.a;
    const double qd = (f.tau * f.tau) + f.b;
    const double eCosh = f.eCoshMinusOne + f.e;
    const double eCos = f.e * f.cosX2;
    const double eSin = f.e * f.sinX2;
    const double eSinc = f.e * (1.0 + f.sincMinusOneX2);
    const double evenBracket =
        (((f.tau * eCosh) + (f.a * f.eSinhc)) * qd) - (((f.tau * eCos) - (f.x2 * eSin)) * p);
    const double oddBracket = ((eCosh + (f.tau * f.eSinhc)) * qd) - ((eCos + (f.tau * eSinc)) * p);
    const double pq = std::max(p * qd, 0.5);
    c.c2 = (f.tau - (evenBracket / d)) / pq;
    c.c3 = (1.0 - (oddBracket / d)) / pq;
  } else {
    c.c2 = (r.coshInt - r.cosInt) / d;
    c.c3 = (r.sinhInt - r.sinInt) / d;
  }
  return c;
}

/// Eigenvalue magnitudes x1 (real pair) and x2 (imaginary pair) of the scaled generator.
struct LorentzEigenvalues {
  double x1 = 0.0;
  double x2 = 0.0;
};

[[nodiscard]] inline LorentzEigenvalues lorentzEigenvalues(const StokesGenerator &k) noexcept {
  const double eta2 = (k.alphaQ * k.alphaQ) + (k.alphaU * k.alphaU) + (k.alphaV * k.alphaV);
  const double rho2 = (k.rhoQ * k.rhoQ) + (k.rhoU * k.rhoU) + (k.rhoV * k.rhoV);
  const double etaRho = (k.alphaQ * k.rhoQ) + (k.alphaU * k.rhoU) + (k.alphaV * k.rhoV);
  const double re = eta2 - rho2;
  const double im = 2.0 * etaRho;
  const double t = std::sqrt(0.5 * (std::hypot(re, im) + std::abs(re)));
  if (t == 0.0) {
    return {};
  }
  const double other = std::abs(im) / (2.0 * ((t > 0.0) ? t : 1.0));
  return (re >= 0.0) ? LorentzEigenvalues{.x1 = t, .x2 = other}
                     : LorentzEigenvalues{.x1 = other, .x2 = t};
}

/**
 * @brief Commuting unit generators A, B with K' s = x1 A + x2 B.
 *
 * With w = eta + i rho scaled by s and (x1 + i x2)^2 = w.w, the unit complex
 * vector n = w / (x1 + i x2) = p + i q gives A = K'(eta = p, rho = q) and
 * B = K'(eta = -q, rho = p), the generators of n and i n. A acts as a unit
 * boost on the plane of its +-1 eigenvalues and B as a unit rotation on the
 * complementary plane of its +-i ones, so AB = BA = 0, A^3 = A, B^3 = -B, and
 * P1 = A^2, P2 = -B^2 are complementary projectors. Every function of K' is
 * then F1(x1) on P1 and F2(x2) on P2,
 *
 *   f(K') = f_even(x1) P1 - f_odd(x1) A + f_even(i x2) P2 - f_odd(x2) B,
 *
 * which multiplies O(1) matrices by bounded coefficients, where the cubic in
 * K' cancels terms of size x2 (pure Faraday rotation by 1e12 rad lost 1e-4).
 * The entries of A and B grow with kappa = (|eta|^2 + |rho|^2) / |w.w|, so
 * this form serves where kappa is small against the eigenvalues.
 */
struct LorentzAxes {
  StokesGenerator a;
  StokesGenerator b;
};

[[nodiscard]] inline LorentzAxes lorentzAxes(const StokesGenerator &k, double x1,
                                             double x2) noexcept {
  const double etaRho = (k.alphaQ * k.rhoQ) + (k.alphaU * k.rhoU) + (k.alphaV * k.rhoV);
  // sqrt(w.w) = x1 + i x2s with x1 x2s = eta.rho; x1, x2 are magnitudes.
  const double x2s = (etaRho < 0.0) ? -x2 : x2;
  const double dRaw = (x1 * x1) + (x2 * x2);
  const double d = (dRaw > 0.0) ? dRaw : 1.0;
  const std::array<double, 3> eta = {k.alphaQ, k.alphaU, k.alphaV};
  const std::array<double, 3> rho = {k.rhoQ, k.rhoU, k.rhoV};
  std::array<double, 3> p{};
  std::array<double, 3> q{};
  for (std::size_t i = 0; i < 3; ++i) {
    p[i] = ((x1 * eta[i]) + (x2s * rho[i])) / d;
    q[i] = ((x1 * rho[i]) - (x2s * eta[i])) / d;
  }
  // K' = x1 A + x2s B_n with B_n = K'(-q, p); B = sign(x2s) B_n keeps x2 >= 0.
  const double sb = (etaRho < 0.0) ? -1.0 : 1.0;
  return {.a = {.alphaQ = p[0],
                .alphaU = p[1],
                .alphaV = p[2],
                .rhoQ = q[0],
                .rhoU = q[1],
                .rhoV = q[2]},
          .b = {.alphaQ = -sb * q[0],
                .alphaU = -sb * q[1],
                .alphaV = -sb * q[2],
                .rhoQ = sb * p[0],
                .rhoU = sb * p[1],
                .rhoV = sb * p[2]}};
}

/// Coefficients of f(K') = cP1 P1 - cA A + cP2 P2 - cB B.
struct AxisCoeffs {
  double cP1 = 0.0;
  double cA = 0.0;
  double cP2 = 0.0;
  double cB = 0.0;
};

[[nodiscard]] inline StokesArray applyAxes(const AxisCoeffs &c, const LorentzAxes &ax,
                                           const StokesArray &v) noexcept {
  const StokesArray av = applyLorentzPart(ax.a, v);
  const StokesArray aav = applyLorentzPart(ax.a, av);
  const StokesArray bv = applyLorentzPart(ax.b, v);
  const StokesArray bbv = applyLorentzPart(ax.b, bv);
  StokesArray o{};
  for (std::size_t i = 0; i < o.size(); ++i) {
    o[i] = (c.cP1 * aav[i]) - (c.cA * av[i]) - (c.cP2 * bbv[i]) - (c.cB * bv[i]);
  }
  return o;
}

/// True where the axis form is the better conditioned: an eigenvalue of at
/// least 1 and kappa below it (the cubic loses ~ eps x2, the axis form ~ eps kappa).
[[nodiscard]] inline bool useAxisForm(const StokesGenerator &k, double x1, double x2) noexcept {
  const double big = std::max(x1, x2);
  if (!(big >= 1.0)) {
    return false;
  }
  const double norm2 = (k.alphaQ * k.alphaQ) + (k.alphaU * k.alphaU) + (k.alphaV * k.alphaV) +
                       (k.rhoQ * k.rhoQ) + (k.rhoU * k.rhoU) + (k.rhoV * k.rhoV);
  return norm2 < big * ((x1 * x1) + (x2 * x2));
}

/// f(K') v = c0 v - c1 K'v + c2 K'^2 v - c3 K'^3 v from precomputed powers.
[[nodiscard]] inline StokesArray applyCubic(const CubicCoeffs &c, const StokesArray &v,
                                            const StokesArray &v1, const StokesArray &v2,
                                            const StokesArray &v3) noexcept {
  StokesArray o{};
  for (std::size_t i = 0; i < o.size(); ++i) {
    o[i] = (c.c0 * v[i]) - (c.c1 * v1[i]) + (c.c2 * v2[i]) - (c.c3 * v3[i]);
  }
  return o;
}

/// K' s scaled copy of a generator (alpha_I dropped).
[[nodiscard]] inline StokesGenerator scaledLorentzPart(const StokesGenerator &k,
                                                       double ds) noexcept {
  return {.alphaI = 0.0,
          .alphaQ = k.alphaQ * ds,
          .alphaU = k.alphaU * ds,
          .alphaV = k.alphaV * ds,
          .rhoQ = k.rhoQ * ds,
          .rhoU = k.rhoU * ds,
          .rhoV = k.rhoV * ds};
}

} // namespace stokes_exact_detail

/**
 * @brief Exact solution of dS/ds = J - K S over a segment with constant K and J.
 *
 * @param s0       Stokes vector entering the segment
 * @param emission Emission vector J (same units as S per unit length)
 * @param k        Propagation-matrix coefficients
 * @param ds       Segment length (same length unit as the coefficients)
 * @param form     Source-term evaluation; DirectIntegral unless the caller's
 *                 budget is 1e-9 and alpha_I ds >= 0.1
 * @return Stokes vector leaving the segment
 */
[[nodiscard]] inline StokesArray
stokesPropagateExact(const StokesArray &s0, const StokesArray &emission, const StokesGenerator &k,
                     double ds, StokesSourceForm form = StokesSourceForm::DirectIntegral) noexcept {
  namespace detail = stokes_exact_detail;
  if (!(ds > 0.0)) {
    return s0;
  }
  const StokesGenerator kp = detail::scaledLorentzPart(k, ds);
  const double tau = k.alphaI * ds;
  const detail::LorentzEigenvalues ev = detail::lorentzEigenvalues(kp);
  const detail::SegmentFunctions f = detail::segmentFunctions(tau, ev.x1, ev.x2);
  const bool axisForm = detail::useAxisForm(kp, ev.x1, ev.x2);
  const detail::LorentzAxes axes =
      axisForm ? detail::lorentzAxes(kp, ev.x1, ev.x2) : detail::LorentzAxes{};
  const double a = ev.x1 * ev.x1;
  const double b = ev.x2 * ev.x2;
  // e^{-tau} e^{-K's} = e^{-tau} (cosh x1 P1 - sinh x1 A + cos x2 P2 - sin x2 B).
  const detail::AxisCoeffs homAxes{.cP1 = f.eCoshMinusOne + f.e,
                                   .cA = ev.x1 * f.eSinhc,
                                   .cP2 = f.e * f.cosX2,
                                   .cB = f.e * f.sinX2};
  auto homogeneous = [&](const StokesArray &v) {
    if (axisForm) {
      return detail::applyAxes(homAxes, axes, v);
    }
    const StokesArray v1 = detail::applyLorentzPart(kp, v);
    const StokesArray v2 = detail::applyLorentzPart(kp, v1);
    const StokesArray v3 = detail::applyLorentzPart(kp, v2);
    return detail::applyCubic(detail::dampedHomogeneous(f), v, v1, v2, v3);
  };

  const double p = (tau * tau) - a;
  if (form == StokesSourceForm::SteadyStateSplit && tau >= 0.1 && p >= 0.01 * tau * tau) {
    // S_inf = (tau + K's)^{-1} J ds; nothing divides by D.
    const double qd = (tau * tau) + b;
    const double pSafe = (p > 0.0) ? p : 1.0;
    const double qdSafe = (qd > 0.0) ? qd : 1.0;
    StokesArray sInf{};
    if (axisForm) {
      const detail::AxisCoeffs inv{
          .cP1 = tau / pSafe, .cA = ev.x1 / pSafe, .cP2 = tau / qdSafe, .cB = ev.x2 / qdSafe};
      sInf = detail::applyAxes(inv, axes, emission);
    } else {
      const double w = ((tau * tau) + b - a) / (pSafe * qdSafe);
      const detail::CubicCoeffs inv{
          .c0 = tau * w, .c1 = w, .c2 = tau / (pSafe * qdSafe), .c3 = 1.0 / (pSafe * qdSafe)};
      const StokesArray j1 = detail::applyLorentzPart(kp, emission);
      const StokesArray j2 = detail::applyLorentzPart(kp, j1);
      const StokesArray j3 = detail::applyLorentzPart(kp, j2);
      sInf = detail::applyCubic(inv, emission, j1, j2, j3);
    }
    StokesArray dev{};
    for (std::size_t i = 0; i < dev.size(); ++i) {
      sInf[i] *= ds;
      dev[i] = s0[i] - sInf[i];
    }
    const StokesArray decayed = homogeneous(dev);
    StokesArray out{};
    for (std::size_t i = 0; i < out.size(); ++i) {
      out[i] = sInf[i] + decayed[i];
    }
    return out;
  }

  StokesArray srcPart{};
  if (axisForm) {
    const detail::Moments m = (std::min(ev.x1, ev.x2) < detail::SMALL_EIGENVALUE)
                                  ? detail::decayMoments(tau)
                                  : detail::Moments{};
    const detail::DecayIntegrals r = detail::decayIntegrals(f, m);
    const detail::AxisCoeffs src{
        .cP1 = r.coshInt, .cA = ev.x1 * r.sinhInt, .cP2 = r.cosInt, .cB = ev.x2 * r.sinInt};
    srcPart = detail::applyAxes(src, axes, emission);
  } else {
    const detail::CubicCoeffs src = detail::integratedCoeffs(f);
    const StokesArray j1 = detail::applyLorentzPart(kp, emission);
    const StokesArray j2 = detail::applyLorentzPart(kp, j1);
    const StokesArray j3 = detail::applyLorentzPart(kp, j2);
    srcPart = detail::applyCubic(src, emission, j1, j2, j3);
  }
  const StokesArray homPart = homogeneous(s0);
  StokesArray out{};
  for (std::size_t i = 0; i < out.size(); ++i) {
    out[i] = homPart[i] + (ds * srcPart[i]);
  }
  return out;
}

} // namespace physics

#endif // PHYSICS_STOKES_EXACT_H
