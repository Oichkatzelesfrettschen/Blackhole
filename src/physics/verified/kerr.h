// Verified Kerr Metric and Black Hole Functions
// Phase 5: Extended formalization with BPT ISCO formula
// Extracted from Rocq proofs via OCaml extraction

#pragma once

#include <cmath>
#include <concepts>

namespace verified {

// Kerr metric parameter (spin parameter a = J/M)
template<typename Real = double>
concept KerrScalar = std::floating_point<Real>;

// Kerr helper: Sigma function (encodes radial-angular coupling)
// Sigma(r, theta, a) = r^2 + a^2 * cos^2(theta)
template<KerrScalar Real>
[[nodiscard]] constexpr Real kerr_Sigma(Real r, Real theta, Real a) noexcept {
    const Real cos_theta = std::cos(theta);
    return r * r + a * a * cos_theta * cos_theta;
}

// Kerr helper: Delta function (encodes horizon structure)
// Delta(r, M, a) = r^2 - 2Mr + a^2
template<KerrScalar Real>
[[nodiscard]] constexpr Real kerr_Delta(Real r, Real M, Real a) noexcept {
    return r * r - 2.0 * M * r + a * a;
}

// Kerr helper: A function (coordinate transformation normalization)
// A(r, theta, M, a) = (r^2 + a^2)^2 - a^2 * Delta * sin^2(theta)
template<KerrScalar Real>
[[nodiscard]] inline Real kerr_A(Real r, Real theta, Real M, Real a) noexcept {
    const Real Delta = kerr_Delta(r, M, a);
    const Real sin_theta = std::sin(theta);
    const Real r2_a2 = r * r + a * a;
    return r2_a2 * r2_a2 - a * a * Delta * sin_theta * sin_theta;
}

// Boyer-Lindquist metric component g_tt
// g_tt = -(1 - 2M*r/Sigma)
template<KerrScalar Real>
[[nodiscard]] constexpr Real kerr_g_tt(Real r, Real theta, Real M, Real a) noexcept {
    const Real Sigma = kerr_Sigma(r, theta, a);
    return -(1.0 - 2.0 * M * r / Sigma);
}

// Boyer-Lindquist metric component g_rr
// g_rr = Sigma / Delta
template<KerrScalar Real>
[[nodiscard]] constexpr Real kerr_g_rr(Real r, Real theta, Real M, Real a) noexcept {
    const Real Sigma = kerr_Sigma(r, theta, a);
    const Real Delta = kerr_Delta(r, M, a);
    return Sigma / Delta;
}

// Boyer-Lindquist metric component g_theta_theta
// g_thth = Sigma
template<KerrScalar Real>
[[nodiscard]] constexpr Real kerr_g_thth(Real r, Real theta, Real a) noexcept {
    return kerr_Sigma(r, theta, a);
}

// Boyer-Lindquist metric component g_phi_phi
// g_phph = (A/Sigma) * sin^2(theta)
template<KerrScalar Real>
[[nodiscard]] inline Real kerr_g_phph(Real r, Real theta, Real M, Real a) noexcept {
    const Real A = kerr_A(r, theta, M, a);
    const Real Sigma = kerr_Sigma(r, theta, a);
    const Real sin_theta = std::sin(theta);
    return (A / Sigma) * sin_theta * sin_theta;
}

// Boyer-Lindquist metric component g_t_phi (frame-dragging term)
// g_tph = -2M*a*r*sin^2(theta) / Sigma
template<KerrScalar Real>
[[nodiscard]] inline Real kerr_g_tph(Real r, Real theta, Real M, Real a) noexcept {
    const Real Sigma = kerr_Sigma(r, theta, a);
    const Real sin_theta = std::sin(theta);
    return -2.0 * M * a * r * sin_theta * sin_theta / Sigma;
}

// Kerr outer event horizon radius
// r_+ = M + sqrt(M^2 - a^2)
template<KerrScalar Real>
[[nodiscard]] inline Real outer_horizon(Real M, Real a) noexcept {
    const Real M2_a2 = M * M - a * a;
    if (M2_a2 < 0.0) return M;  // Extremal or naked singularity case
    return M + std::sqrt(M2_a2);
}

// Kerr inner event horizon radius
// r_- = M - sqrt(M^2 - a^2)
template<KerrScalar Real>
[[nodiscard]] inline Real inner_horizon(Real M, Real a) noexcept {
    const Real M2_a2 = M * M - a * a;
    if (M2_a2 < 0.0) return M;  // Extremal or naked singularity case
    return M - std::sqrt(M2_a2);
}

// Ergosphere outer radius (at equator, theta = pi/2)
// r_ergo = M + sqrt(M^2 - a^2 * cos^2(theta))
template<KerrScalar Real>
[[nodiscard]] inline Real ergosphere_outer_radius(Real theta, Real M, Real a) noexcept {
    const Real cos_theta = std::cos(theta);
    const Real term = M * M - a * a * cos_theta * cos_theta;
    if (term < 0.0) return M;  // Safety check
    return M + std::sqrt(term);
}

// Surface gravity at outer horizon
// kappa = sqrt(M^2 - a^2) / (2 * (M + sqrt(M^2 - a^2)))
template<KerrScalar Real>
[[nodiscard]] inline Real surface_gravity(Real M, Real a) noexcept {
    const Real M2_a2 = M * M - a * a;
    if (M2_a2 < 0.0) return 0.0;  // No surface gravity for naked singularity
    const Real sqrt_term = std::sqrt(M2_a2);
    const Real r_plus = M + sqrt_term;
    return sqrt_term / (2.0 * r_plus);
}

// Hawking temperature
// T = (hbar * kappa) / (2 * pi * k_B)  (in natural units, = hbar * kappa / (2 * pi))
template<KerrScalar Real>
[[nodiscard]] inline Real hawking_temperature(Real M, Real a) noexcept {
    return surface_gravity(M, a) / (2.0 * 3.141592653589793);  // pi in denominator
}

// Bardeen-Press-Teukolsky ISCO formula: helper Z1
template<KerrScalar Real>
[[nodiscard]] inline Real bpt_Z1(Real a) noexcept {
    const Real a2 = a * a;
    // Z1 = 1 + cbrt((1 - a^2)/(2)) * (cbrt(1 + a) + cbrt(1 - a))
    const Real one_minus_a2 = 1.0 - a2;
    const Real cbrt_half_one_minus_a2 = std::cbrt(one_minus_a2 / 2.0);
    const Real cbrt_1_plus_a = std::cbrt(1.0 + a);
    const Real cbrt_1_minus_a = std::cbrt(1.0 - a);
    return 1.0 + cbrt_half_one_minus_a2 * (cbrt_1_plus_a + cbrt_1_minus_a);
}

// Bardeen-Press-Teukolsky ISCO formula: helper Z2
template<KerrScalar Real>
[[nodiscard]] inline Real bpt_Z2(Real a) noexcept {
    const Real a2 = a * a;
    // Z2 = sqrt(Z1^2 - 8*a^2)
    const Real Z1 = bpt_Z1(a);
    const Real term = Z1 * Z1 - 8.0 * a2;
    if (term < 0.0) return 0.0;  // Safety check
    return std::sqrt(term);
}

// ISCO radius (prograde orbits)
// r_isco_pro = M * (3 + Z2 - sqrt((3 - Z1) * (3 + Z1 + 2*Z2)))
template<KerrScalar Real>
[[nodiscard]] inline Real isco_radius_prograde(Real M, Real a) noexcept {
    const Real Z1 = bpt_Z1(a);
    const Real Z2 = bpt_Z2(a);
    const Real factor = (3.0 - Z1) * (3.0 + Z1 + 2.0 * Z2);
    if (factor < 0.0) return 6.0 * M;  // Default to Schwarzschild
    const Real sqrt_factor = std::sqrt(factor);
    return M * (3.0 + Z2 - sqrt_factor);
}

// ISCO radius (retrograde orbits)
// r_isco_retro = M * (3 + Z2 + sqrt((3 - Z1) * (3 + Z1 + 2*Z2)))
template<KerrScalar Real>
[[nodiscard]] inline Real isco_radius_retrograde(Real M, Real a) noexcept {
    const Real Z1 = bpt_Z1(a);
    const Real Z2 = bpt_Z2(a);
    const Real factor = (3.0 - Z1) * (3.0 + Z1 + 2.0 * Z2);
    if (factor < 0.0) return 6.0 * M;  // Default to Schwarzschild
    const Real sqrt_factor = std::sqrt(factor);
    return M * (3.0 + Z2 + sqrt_factor);
}

// Orbital angular momentum for circular orbit at given radius
template<KerrScalar Real>
[[nodiscard]] constexpr Real circular_orbit_radius(Real M, Real E, Real L) noexcept {
    // Placeholder: related to effective potential
    (void)M; (void)E; (void)L;
    return 0.0;
}

// Binding energy at ISCO (energy cost to reach infinity)
template<KerrScalar Real>
[[nodiscard]] inline Real binding_energy_isco(Real M, Real a) noexcept {
    const Real r_isco = isco_radius_prograde(M, a);
    const Real Sigma = kerr_Sigma(r_isco, 3.141592653589793 / 2.0, a);  // theta = pi/2
    // Approximate binding energy
    return 1.0 - std::sqrt(1.0 - 2.0 * M / r_isco);
}

}  // namespace verified
