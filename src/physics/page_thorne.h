/**
 * @file page_thorne.h
 * @brief Page-Thorne radiative flux of a Novikov-Thorne thin disk in Kerr.
 *
 * Geometric units G = c = M = 1; aStar is the signed dimensionless spin. The
 * disk orbits in +phi: aStar > 0 is a prograde disk, aStar < 0 a retrograde
 * one. Every function takes and returns M = 1 quantities.
 *
 * The flux leaving one face of the disk (Page & Thorne 1974, ApJ 191, 499)
 * is
 *
 *   F(r) = -(Mdot / 4 pi sqrt(-g)) Omega_,r / (E - Omega L)^2
 *          * integral_{r_isco}^{r} (E - Omega L) L_,r dr,
 *
 * with sqrt(-g) = r in the equatorial plane and E, L, Omega the circular
 * geodesic constants. With x = sqrt(r), x0 = sqrt(r_isco) and x1, x2, x3
 * the roots of x^3 - 3x + 2a = 0, the integral has the closed form
 *
 *   F(r) = (3 Mdot / 8 pi) * S(x),
 *   S(x) = 1 / (x^4 (x^3 - 3x + 2a))
 *          * [x - x0 - (3/2) a ln(x/x0)
 *             - sum_i 3 (x_i - a)^2 / (x_i (x_i - x_j)(x_i - x_k))
 *                     * ln((x - x_i)/(x0 - x_i))],
 *   x1 = 2 cos(acos(a)/3 - pi/3), x2 = 2 cos(acos(a)/3 + pi/3),
 *   x3 = -2 cos(acos(a)/3).
 *
 * S(x) tends to 1/r^3 at large r, so F tends to the Newtonian 3 Mdot /
 * (8 pi r^3). scripts/gen_page_thorne_reference.py evaluates both the closed
 * form and the quadrature at 30 digits; tests/page_thorne_test.cpp holds the
 * double-precision form to the quadrature and pins the flux peak radii.
 *
 * At |aStar| = 1 the roots x1 and x2 coincide and the closed form divides by
 * zero, so every function here evaluates at pageThorneSpin(aStar), the spin
 * clamped to |aStar| <= 0.9999, the clamp isco_radius (disk_profile.glsl),
 * dtPageThorneShape and the CUDA twins apply.
 *
 * The header compiles as C++17 so nvcc-built tests can include it as the host
 * reference for the device twins in src/cuda/device_disk_transfer.cuh.
 */

#ifndef PHYSICS_PAGE_THORNE_H
#define PHYSICS_PAGE_THORNE_H

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>

namespace physics {

/** @brief Largest |aStar| the Page-Thorne closed form is evaluated at. */
inline constexpr double K_PAGE_THORNE_MAX_SPIN = 0.9999;

/** @brief aStar clamped to [-K_PAGE_THORNE_MAX_SPIN, K_PAGE_THORNE_MAX_SPIN]. */
[[nodiscard]] inline double pageThorneSpin(double aStar) noexcept {
  return std::clamp(aStar, -K_PAGE_THORNE_MAX_SPIN, K_PAGE_THORNE_MAX_SPIN);
}

/**
 * @brief ISCO radius in units of M for a disk orbiting in +phi.
 *
 * Bardeen, Press & Teukolsky (1972) eq. 2.21: aStar > 0 gives the prograde
 * ISCO (6 M at aStar = 0, 1.237 M at 0.998), aStar < 0 the retrograde one.
 * The spin is clamped by pageThorneSpin.
 */
[[nodiscard]] inline double pageThorneIscoRadius(double aStarIn) noexcept {
  double const aStar = pageThorneSpin(aStarIn);
  double const z1 =
      1.0 + (std::cbrt(1.0 - (aStar * aStar)) * (std::cbrt(1.0 + aStar) + std::cbrt(1.0 - aStar)));
  double const z2 = std::sqrt((3.0 * aStar * aStar) + (z1 * z1));
  double const root = std::sqrt((3.0 - z1) * (3.0 + z1 + (2.0 * z2)));
  return aStar >= 0.0 ? 3.0 + z2 - root : 3.0 + z2 + root;
}

/** @brief Conserved constants of a circular equatorial geodesic (M = 1). */
struct KerrCircularOrbit {
  double energy = 0.0;          ///< Specific energy E = -u_t
  double angularMomentum = 0.0; ///< Specific angular momentum L = u_phi
  double omega = 0.0;           ///< Angular velocity Omega = dphi/dt
};

/**
 * @brief E, L, Omega of the circular equatorial orbit at radius r (M = 1).
 *
 * Bardeen, Press & Teukolsky (1972) eq. 2.12-2.16 with x = sqrt(r):
 *   E = (x^3 - 2x + a) / (x^{3/2} sqrt(x^3 - 3x + 2a)),
 *   L = (x^4 - 2ax + a^2) / (x^{3/2} sqrt(x^3 - 3x + 2a)),
 *   Omega = 1 / (x^3 + a).
 * Returns zeros where no timelike circular orbit exists (x^3 - 3x + 2a <= 0).
 */
[[nodiscard]] inline KerrCircularOrbit kerrCircularOrbit(double r, double aStar) noexcept {
  KerrCircularOrbit orbit;
  double const x = std::sqrt(r);
  double const q = (x * x * x) - (3.0 * x) + (2.0 * aStar);
  if (!(q > 0.0)) {
    return orbit;
  }
  double const denom = x * std::sqrt(x) * std::sqrt(q);
  orbit.energy = ((x * x * x) - (2.0 * x) + aStar) / denom;
  orbit.angularMomentum = ((x * x * x * x) - (2.0 * aStar * x) + (aStar * aStar)) / denom;
  orbit.omega = 1.0 / ((x * x * x) + aStar);
  return orbit;
}

/**
 * @brief Novikov-Thorne radiative efficiency eta = 1 - E(r_isco).
 *
 * 0.0572 at aStar = 0, 0.1558 at 0.9, 0.3210 at 0.998.
 */
[[nodiscard]] inline double novikovThorneEfficiency(double aStarIn) noexcept {
  double const aStar = pageThorneSpin(aStarIn);
  return 1.0 - kerrCircularOrbit(pageThorneIscoRadius(aStar), aStar).energy;
}

/**
 * @brief Spin-only terms of the Page-Thorne flux shape S(r), M = 1.
 *
 * The clamped spin, the ISCO radius x0^2, the roots x_i of x^3 - 3x + 2a and
 * their log coefficients depend on aStar alone. A radial sweep at one spin
 * (diskFluxBatch, pageThorneFluxPeakRadius) builds the profile once, and
 * shape(r) then costs one square root and four logarithms per radius instead
 * of also three cube roots, an arccosine and three cosines. shape(r) runs the
 * same operations in the same order as pageThorneFluxShape, which delegates
 * to it, so both return identical doubles.
 *
 * A root with |x_i| < 1e-14 carries no term: its term vanishes in the limit
 * x_i -> 0, which is the root x2 at aStar = 0.
 */
class PageThorneProfile {
public:
  explicit PageThorneProfile(double aStarIn) noexcept
      : aStar_(pageThorneSpin(aStarIn)), rIsco_(pageThorneIscoRadius(aStar_)),
        x0_(std::sqrt(rIsco_)) {
    double const theta = std::acos(aStar_) / 3.0;
    constexpr double kThird = 1.047197551196597746154214461093; // pi / 3
    roots_ = {2.0 * std::cos(theta - kThird), 2.0 * std::cos(theta + kThird),
              -2.0 * std::cos(theta)};
    for (std::size_t i = 0; i < roots_.size(); ++i) {
      double const xi = roots_.at(i);
      double const xj = roots_.at((i + 1) % 3);
      double const xk = roots_.at((i + 2) % 3);
      active_.at(i) = !(std::abs(xi) < 1e-14);
      coeffs_.at(i) =
          active_.at(i) ? 3.0 * (xi - aStar_) * (xi - aStar_) / (xi * (xi - xj) * (xi - xk)) : 0.0;
    }
  }

  /** @brief Clamped spin the profile evaluates at (pageThorneSpin). */
  [[nodiscard]] double spin() const noexcept { return aStar_; }

  /** @brief ISCO radius in units of M (pageThorneIscoRadius). */
  [[nodiscard]] double iscoRadius() const noexcept { return rIsco_; }

  /** @brief S(r) = F(r) * 8 pi / (3 Mdot) at radius r [M]; zero at and inside the ISCO. */
  [[nodiscard]] double shape(double r) const noexcept {
    if (!(r > rIsco_)) {
      return 0.0;
    }
    double const x = std::sqrt(r);
    double bracket = x - x0_ - (1.5 * aStar_ * std::log(x / x0_));
    for (std::size_t i = 0; i < roots_.size(); ++i) {
      if (!active_.at(i)) {
        continue;
      }
      double const xi = roots_.at(i);
      bracket -= coeffs_.at(i) * std::log((x - xi) / (x0_ - xi));
    }
    double const x4 = x * x * x * x;
    double const q = (x * x * x) - (3.0 * x) + (2.0 * aStar_);
    return bracket / (x4 * q);
  }

private:
  double aStar_;
  double rIsco_;
  double x0_;
  std::array<double, 3> roots_{};
  std::array<double, 3> coeffs_{};
  std::array<bool, 3> active_{};
};

/**
 * @brief Page-Thorne flux shape S(r) = F(r) * 8 pi / (3 Mdot), M = 1.
 *
 * Zero at and inside the ISCO. A sweep over r at one spin reuses a
 * PageThorneProfile instead.
 */
[[nodiscard]] inline double pageThorneFluxShape(double r, double aStarIn) noexcept {
  return PageThorneProfile(aStarIn).shape(r);
}

/**
 * @brief Relativistic factor f(r) with F = (3 Mdot / 8 pi r^3) f(r), M = 1.
 *
 * f = r^3 S(r) -> 1 at large r; f = 0 at the ISCO (zero-torque edge).
 */
[[nodiscard]] inline double pageThorneRelativisticFactor(double r, double aStar) noexcept {
  return r * r * r * pageThorneFluxShape(r, aStar);
}

/**
 * @brief Radius (M = 1) of the Page-Thorne flux maximum.
 *
 * Golden-section search on (r_isco, 4 r_isco]; the flux is unimodal there.
 * 9.551 M at aStar = 0 (1.592 r_isco), 1.483 r_isco at 0.9, 1.278 r_isco at
 * 0.998.
 */
[[nodiscard]] inline double pageThorneFluxPeakRadius(double aStar) noexcept {
  PageThorneProfile const profile(aStar);
  double const rIsco = pageThorneIscoRadius(aStar);
  double lo = rIsco;
  double hi = 4.0 * rIsco;
  double const invPhi = 0.5 * (std::sqrt(5.0) - 1.0);
  double c = hi - (invPhi * (hi - lo));
  double d = lo + (invPhi * (hi - lo));
  double fc = profile.shape(c);
  double fd = profile.shape(d);
  for (int iter = 0; iter < 200 && (hi - lo) > 1e-12 * rIsco; ++iter) {
    if (fc > fd) {
      hi = d;
      d = c;
      fd = fc;
      c = hi - (invPhi * (hi - lo));
      fc = profile.shape(c);
    } else {
      lo = c;
      c = d;
      fc = fd;
      d = lo + (invPhi * (hi - lo));
      fd = profile.shape(d);
    }
  }
  return 0.5 * (lo + hi);
}

/** @brief Peak value of pageThorneFluxShape, the normalization of the disk flux. */
[[nodiscard]] inline double pageThorneFluxPeak(double aStar) noexcept {
  return pageThorneFluxShape(pageThorneFluxPeakRadius(aStar), aStar);
}

} // namespace physics

#endif // PHYSICS_PAGE_THORNE_H
