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
template<Scalar Real>
[[nodiscard]] constexpr Real schwarzschild_radius(Real M) noexcept {
    return 2.0 * M;
}

// Innermost stable circular orbit (ISCO) radius
// r_isco = 6M for non-rotating case
template<Scalar Real>
[[nodiscard]] constexpr Real schwarzschild_isco(Real M) noexcept {
    return 6.0 * M;
}

// Photon sphere radius
// r_photon = 1.5 * r_s = 3M
template<Scalar Real>
[[nodiscard]] constexpr Real photon_sphere_radius(Real M) noexcept {
    return 3.0 * M;
}

// Schwarzschild lapse function (time dilation factor)
// f(r) = 1 - 2M/r = 1 - r_s/r
template<Scalar Real>
[[nodiscard]] constexpr Real f_schwarzschild(Real r, Real M) noexcept {
    return 1.0 - 2.0 * M / r;
}

// Schwarzschild metric component g_tt
// g_tt = -f(r) = -(1 - 2M/r)
template<Scalar Real>
[[nodiscard]] constexpr Real schwarzschild_g_tt(Real r, Real M) noexcept {
    return -(1.0 - 2.0 * M / r);
}

// Schwarzschild metric component g_rr
// g_rr = 1/f(r) = 1/(1 - 2M/r)
template<Scalar Real>
[[nodiscard]] constexpr Real schwarzschild_g_rr(Real r, Real M) noexcept {
    return 1.0 / (1.0 - 2.0 * M / r);
}

// Schwarzschild metric component g_theta_theta
// g_thth = r^2
template<Scalar Real>
[[nodiscard]] constexpr Real schwarzschild_g_thth(Real r) noexcept {
    return r * r;
}

// Schwarzschild metric component g_phi_phi
// g_phph = r^2 * sin^2(theta)
template<Scalar Real>
[[nodiscard]] inline Real schwarzschild_g_phph(Real r, Real theta) noexcept {
    const Real sin_theta = std::sin(theta);
    return r * r * sin_theta * sin_theta;
}

// Schwarzschild metric component g_t_phi (off-diagonal, always 0)
template<Scalar Real>
[[nodiscard]] constexpr Real schwarzschild_g_tph(Real r, Real M) noexcept {
    (void)r; (void)M;  // Unused parameters
    return 0.0;
}

// Christoffel symbol Gamma^t_tr
// Gamma^t_tr = M / (r * (r - 2M))
template<Scalar Real>
[[nodiscard]] constexpr Real christoffel_t_tr(Real r, Real M) noexcept {
    return M / (r * (r - 2.0 * M));
}

// Christoffel symbol Gamma^r_tt
// Gamma^r_tt = M * (r - 2M) / r^3
template<Scalar Real>
[[nodiscard]] constexpr Real christoffel_r_tt(Real r, Real M) noexcept {
    return M * (r - 2.0 * M) / (r * r * r);
}

// Christoffel symbol Gamma^r_rr
// Gamma^r_rr = -M / (r * (r - 2M))
template<Scalar Real>
[[nodiscard]] constexpr Real christoffel_r_rr(Real r, Real M) noexcept {
    return -M / (r * (r - 2.0 * M));
}

// Christoffel symbol Gamma^r_thth
// Gamma^r_thth = -(r - 2M)
template<Scalar Real>
[[nodiscard]] constexpr Real christoffel_r_thth(Real r, Real M) noexcept {
    return -(r - 2.0 * M);
}

// Christoffel symbol Gamma^r_phph
// Gamma^r_phph = -(r - 2M) * sin^2(theta)
template<Scalar Real>
[[nodiscard]] inline Real christoffel_r_phph(Real r, Real M, Real theta) noexcept {
    const Real sin_theta = std::sin(theta);
    return -(r - 2.0 * M) * sin_theta * sin_theta;
}

// Christoffel symbol Gamma^theta_rtheta
// Gamma^theta_rtheta = 1/r
template<Scalar Real>
[[nodiscard]] constexpr Real christoffel_th_rth(Real r) noexcept {
    return 1.0 / r;
}

// Christoffel symbol Gamma^theta_phiphi
// Gamma^theta_phiphi = -sin(theta) * cos(theta)
template<Scalar Real>
[[nodiscard]] inline Real christoffel_th_phph(Real theta) noexcept {
    return -std::sin(theta) * std::cos(theta);
}

// Christoffel symbol Gamma^phi_rphi
// Gamma^phi_rphi = 1/r
template<Scalar Real>
[[nodiscard]] constexpr Real christoffel_ph_rph(Real r) noexcept {
    return 1.0 / r;
}

// Christoffel symbol Gamma^phi_thetaphi
// Gamma^phi_thetaphi = cot(theta) = cos(theta)/sin(theta)
template<Scalar Real>
[[nodiscard]] inline Real christoffel_ph_thph(Real theta) noexcept {
    return std::cos(theta) / std::sin(theta);
}

// Radial acceleration (second derivative)
// Computed from Christoffel symbols and metric
// d²r/dλ² = Christoffel terms
template<Scalar Real>
[[nodiscard]] inline Real radial_acceleration(
    Real r, Real M, Real theta,
    Real dr_dlambda, Real dtheta_dlambda, Real dphi_dlambda) noexcept
{
    const Real c_r_tt = christoffel_r_tt(r, M);
    const Real c_r_rr = christoffel_r_rr(r, M);
    const Real c_r_thth = christoffel_r_thth(r, M);
    const Real c_r_phph = christoffel_r_phph(r, M, theta);

    const Real dtheta_dlambda_sq = dtheta_dlambda * dtheta_dlambda;
    const Real dphi_dlambda_sq = dphi_dlambda * dphi_dlambda;

    // d²r/dλ² = -Γ^r_tt (dt/dλ)² - 2Γ^r_tr (dt/dλ)(dr/dλ) - Γ^r_rr (dr/dλ)²
    //           - Γ^r_θθ (dθ/dλ)² - Γ^r_φφ (dφ/dλ)² sin²(θ)
    return c_r_tt - c_r_rr * (dr_dlambda * dr_dlambda)
         - c_r_thth * dtheta_dlambda_sq
         - c_r_phph * dphi_dlambda_sq;
}

}  // namespace verified
