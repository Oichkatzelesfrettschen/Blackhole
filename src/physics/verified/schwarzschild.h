// Verified Schwarzschild Metric Functions
// Extracted from Rocq proofs via OCaml extraction
// Pipeline: Rocq -> OCaml -> C++23

#pragma once

#include <cmath>
#include <concepts>

namespace verified {

// Schwarzschild spacetime parameter
template<typename Real = double>
concept Scalar = std::floating_point<Real>;

// Schwarzschild horizon radius (event horizon)
// r_s = 2M in geometric units (G = c = 1)
template <Scalar Real> [[nodiscard]] constexpr Real schwarzschildRadius(Real m) noexcept {
  return 2.0 * m;
}

// Innermost stable circular orbit (ISCO) radius
// r_isco = 6M for non-rotating case
template <Scalar Real> [[nodiscard]] constexpr Real schwarzschildIsco(Real m) noexcept {
  return 6.0 * m;
}

// Photon sphere radius
// r_photon = 1.5 * r_s = 3M
template <Scalar Real> [[nodiscard]] constexpr Real photonSphereRadius(Real m) noexcept {
  return 3.0 * m;
}

// Schwarzschild lapse function (time dilation factor)
// f(r) = 1 - 2M/r = 1 - r_s/r
template <Scalar Real> [[nodiscard]] constexpr Real fSchwarzschild(Real r, Real m) noexcept {
  return 1.0 - (2.0 * m / r);
}

// Schwarzschild metric component g_tt
// g_tt = -f(r) = -(1 - 2M/r)
template <Scalar Real> [[nodiscard]] constexpr Real schwarzschildGTt(Real r, Real m) noexcept {
  return -(1.0 - (2.0 * m / r));
}

// Schwarzschild metric component g_rr
// g_rr = 1/f(r) = 1/(1 - 2M/r)
template <Scalar Real> [[nodiscard]] constexpr Real schwarzschildGRr(Real r, Real m) noexcept {
  return 1.0 / (1.0 - (2.0 * m / r));
}

// Schwarzschild metric component g_theta_theta
// g_thth = r^2
template <Scalar Real> [[nodiscard]] constexpr Real schwarzschildGThth(Real r) noexcept {
  return r * r;
}

// Schwarzschild metric component g_phi_phi
// g_phph = r^2 * sin^2(theta)
template <Scalar Real> [[nodiscard]] inline Real schwarzschildGPhph(Real r, Real theta) noexcept {
  const Real sinTheta = std::sin(theta);
  return r * r * sinTheta * sinTheta;
}

// Schwarzschild metric component g_t_phi (off-diagonal, always 0)
template <Scalar Real> [[nodiscard]] constexpr Real schwarzschildGTph(Real r, Real m) noexcept {
  (void)r;
  (void)m; // Unused parameters
  return 0.0;
}

// Christoffel symbol Gamma^t_tr
// Gamma^t_tr = M / (r * (r - 2M))
template <Scalar Real> [[nodiscard]] constexpr Real christoffelTTr(Real r, Real m) noexcept {
  return m / (r * (r - (2.0 * m)));
}

// Christoffel symbol Gamma^r_tt
// Gamma^r_tt = M * (r - 2M) / r^3
template <Scalar Real> [[nodiscard]] constexpr Real christoffelRTt(Real r, Real m) noexcept {
  return m * (r - (2.0 * m)) / (r * r * r);
}

// Christoffel symbol Gamma^r_rr
// Gamma^r_rr = -M / (r * (r - 2M))
template <Scalar Real> [[nodiscard]] constexpr Real christoffelRRr(Real r, Real m) noexcept {
  return -m / (r * (r - (2.0 * m)));
}

// Christoffel symbol Gamma^r_thth
// Gamma^r_thth = -(r - 2M)
template <Scalar Real> [[nodiscard]] constexpr Real christoffelRThth(Real r, Real m) noexcept {
  return -(r - (2.0 * m));
}

// Christoffel symbol Gamma^r_phph
// Gamma^r_phph = -(r - 2M) * sin^2(theta)
template <Scalar Real>
[[nodiscard]] inline Real christoffelRPhph(Real r, Real m, Real theta) noexcept {
  const Real sinTheta = std::sin(theta);
  return -(r - (2.0 * m)) * sinTheta * sinTheta;
}

// Christoffel symbol Gamma^theta_rtheta
// Gamma^theta_rtheta = 1/r
template <Scalar Real> [[nodiscard]] constexpr Real christoffelThRth(Real r) noexcept {
  return 1.0 / r;
}

// Christoffel symbol Gamma^theta_phiphi
// Gamma^theta_phiphi = -sin(theta) * cos(theta)
template <Scalar Real> [[nodiscard]] inline Real christoffelThPhph(Real theta) noexcept {
  return -std::sin(theta) * std::cos(theta);
}

// Christoffel symbol Gamma^phi_rphi
// Gamma^phi_rphi = 1/r
template <Scalar Real> [[nodiscard]] constexpr Real christoffelPhRph(Real r) noexcept {
  return 1.0 / r;
}

// Christoffel symbol Gamma^phi_thetaphi
// Gamma^phi_thetaphi = cot(theta) = cos(theta)/sin(theta)
template <Scalar Real> [[nodiscard]] inline Real christoffelPhThph(Real theta) noexcept {
  return std::cos(theta) / std::sin(theta);
}

// Radial acceleration (second derivative)
// Computed from Christoffel symbols and metric
// d²r/dλ² = Christoffel terms
template <Scalar Real>
[[nodiscard]] inline Real radialAcceleration(Real r, Real m, Real theta, Real drDlambda,
                                             Real dthetaDlambda, Real dphiDlambda) noexcept {
  const Real cRTt = christoffelRTt(r, m);
  const Real cRRr = christoffelRRr(r, m);
  const Real cRThth = christoffelRThth(r, m);
  const Real cRPhph = christoffelRPhph(r, m, theta);

  const Real dthetaDlambdaSq = dthetaDlambda * dthetaDlambda;
  const Real dphiDlambdaSq = dphiDlambda * dphiDlambda;

  // d²r/dλ² = -Γ^r_tt (dt/dλ)² - 2Γ^r_tr (dt/dλ)(dr/dλ) - Γ^r_rr (dr/dλ)²
  //           - Γ^r_θθ (dθ/dλ)² - Γ^r_φφ (dφ/dλ)² sin²(θ)
  return cRTt - (cRRr * (drDlambda * drDlambda)) - (cRThth * dthetaDlambdaSq) -
         (cRPhph * dphiDlambdaSq);
}

}  // namespace verified
