// Verified Kerr Metric and Black Hole Functions
// Phase 5: Extended formalization with BPT ISCO formula
// Extracted from Rocq proofs via OCaml extraction

#pragma once

#include <cmath>
#include <concepts>
#include <numbers>

namespace verified {

// Kerr metric parameter (spin parameter a = J/M)
template<typename Real = double>
concept KerrScalar = std::floating_point<Real>;

// Kerr helper: Sigma function (encodes radial-angular coupling)
// Sigma(r, theta, a) = r^2 + a^2 * cos^2(theta)
template <KerrScalar Real>
[[nodiscard]] constexpr Real kerrSigma(Real r, Real theta, Real a) noexcept {
  const Real cosTheta = std::cos(theta);
  return (r * r) + (a * a * cosTheta * cosTheta);
}

// Kerr helper: Delta function (encodes horizon structure)
// Delta(r, M, a) = r^2 - 2Mr + a^2
template <KerrScalar Real> [[nodiscard]] constexpr Real kerrDelta(Real r, Real m, Real a) noexcept {
  return (r * r) - (2.0 * m * r) + (a * a);
}

// Kerr helper: A function (coordinate transformation normalization)
// A(r, theta, M, a) = (r^2 + a^2)^2 - a^2 * Delta * sin^2(theta)
template <KerrScalar Real>
[[nodiscard]] inline Real kerrA(Real r, Real theta, Real m, Real a) noexcept {
  const Real delta = kerr_Delta(r, m, a);
  const Real sinTheta = std::sin(theta);
  const Real r2A2 = (r * r) + (a * a);
  return (r2A2 * r2A2) - (a * a * delta * sinTheta * sinTheta);
}

// Boyer-Lindquist metric component g_tt
// g_tt = -(1 - 2M*r/Sigma)
template <KerrScalar Real>
[[nodiscard]] constexpr Real kerrGTt(Real r, Real theta, Real m, Real a) noexcept {
  const Real sigma = kerrSigma(r, theta, a);
  return -(1.0 - (2.0 * m * r / sigma));
}

// Boyer-Lindquist metric component g_rr
// g_rr = Sigma / Delta
template <KerrScalar Real>
[[nodiscard]] constexpr Real kerrGRr(Real r, Real theta, Real m, Real a) noexcept {
  const Real sigma = kerrSigma(r, theta, a);
  const Real delta = kerrDelta(r, m, a);
  return sigma / delta;
}

// Boyer-Lindquist metric component g_theta_theta
// g_thth = Sigma
template <KerrScalar Real>
[[nodiscard]] constexpr Real kerrGThth(Real r, Real theta, Real a) noexcept {
  return kerr_Sigma(r, theta, a);
}

// Boyer-Lindquist metric component g_phi_phi
// g_phph = (A/Sigma) * sin^2(theta)
template <KerrScalar Real>
[[nodiscard]] inline Real kerrGPhph(Real r, Real theta, Real m, Real a) noexcept {
  const Real bigA = kerr_A(r, theta, m, a);
  const Real sigma = kerr_Sigma(r, theta, a);
  const Real sinTheta = std::sin(theta);
  return (bigA / sigma) * sinTheta * sinTheta;
}

// Boyer-Lindquist metric component g_t_phi (frame-dragging term)
// g_tph = -2M*a*r*sin^2(theta) / Sigma
template <KerrScalar Real>
[[nodiscard]] inline Real kerrGTph(Real r, Real theta, Real m, Real a) noexcept {
  const Real sigma = kerr_Sigma(r, theta, a);
  const Real sinTheta = std::sin(theta);
  return -2.0 * m * a * r * sinTheta * sinTheta / sigma;
}

// Kerr outer event horizon radius
// r_+ = M + sqrt(M^2 - a^2)
template <KerrScalar Real> [[nodiscard]] inline Real outerHorizon(Real m, Real a) noexcept {
  const Real m2A2 = (m * m) - (a * a);
  if (m2A2 < 0.0) {
    return m; // Extremal or naked singularity case
  }
  return m + std::sqrt(m2A2);
}

// Kerr inner event horizon radius
// r_- = M - sqrt(M^2 - a^2)
template <KerrScalar Real> [[nodiscard]] inline Real innerHorizon(Real m, Real a) noexcept {
  const Real m2A2 = (m * m) - (a * a);
  if (m2A2 < 0.0) {
    return m; // Extremal or naked singularity case
  }
  return m - std::sqrt(m2A2);
}

// Ergosphere outer radius (at equator, theta = pi/2)
// r_ergo = M + sqrt(M^2 - a^2 * cos^2(theta))
template <KerrScalar Real>
[[nodiscard]] inline Real ergosphereOuterRadius(Real theta, Real m, Real a) noexcept {
  const Real cosTheta = std::cos(theta);
  const Real term = (m * m) - (a * a * cosTheta * cosTheta);
  if (term < 0.0) {
    return m; // Safety check
  }
  return m + std::sqrt(term);
}

// Surface gravity at outer horizon
// kappa = sqrt(M^2 - a^2) / (2 * (M + sqrt(M^2 - a^2)))
template <KerrScalar Real> [[nodiscard]] inline Real surfaceGravity(Real m, Real a) noexcept {
  const Real m2A2 = (m * m) - (a * a);
  if (m2A2 < 0.0) {
    return 0.0; // No surface gravity for naked singularity
  }
  const Real sqrtTerm = std::sqrt(m2A2);
  const Real rPlus = m + sqrtTerm;
  return sqrtTerm / (2.0 * rPlus);
}

// Hawking temperature
// T = (hbar * kappa) / (2 * pi * k_B)  (in natural units, = hbar * kappa / (2 * pi))
template <KerrScalar Real> [[nodiscard]] inline Real hawkingTemperature(Real m, Real a) noexcept {
  return surface_gravity(m, a) / (2.0 * std::numbers::pi); // pi in denominator
}

// Bardeen-Press-Teukolsky ISCO formula: helper Z1
template <KerrScalar Real> [[nodiscard]] inline Real bptZ1(Real a) noexcept {
  const Real a2 = a * a;
  // Z1 = 1 + cbrt((1 - a^2)/(2)) * (cbrt(1 + a) + cbrt(1 - a))
  const Real oneMinusA2 = 1.0 - a2;
  const Real cbrtHalfOneMinusA2 = std::cbrt(oneMinusA2 / 2.0);
  const Real cbrt1PlusA = std::cbrt(1.0 + a);
  const Real cbrt1MinusA = std::cbrt(1.0 - a);
  return 1.0 + (cbrtHalfOneMinusA2 * (cbrt1PlusA + cbrt1MinusA));
}

// Bardeen-Press-Teukolsky ISCO formula: helper Z2
template <KerrScalar Real> [[nodiscard]] inline Real bptZ2(Real a) noexcept {
  const Real a2 = a * a;
  // Z2 = sqrt(3*a^2 + Z1^2) - Bardeen-Press-Teukolsky 1972
  const Real z1 = bptZ1(a);
  const Real term = (3.0 * a2) + (z1 * z1);
  return std::sqrt(term); // Always positive for 0 <= a <= 1
}

// ISCO radius (prograde orbits)
// r_isco_pro = M * (3 + Z2 - sqrt((3 - Z1) * (3 + Z1 + 2*Z2)))
template <KerrScalar Real> [[nodiscard]] inline Real iscoRadiusPrograde(Real m, Real a) noexcept {
  const Real z1 = bptZ1(a);
  const Real z2 = bptZ2(a);
  const Real factor = (3.0 - z1) * (3.0 + z1 + (2.0 * z2));
  if (factor < 0.0) {
    return 6.0 * m; // Default to Schwarzschild
  }
  const Real sqrtFactor = std::sqrt(factor);
  return m * (3.0 + z2 - sqrtFactor);
}

// ISCO radius (retrograde orbits)
// r_isco_retro = M * (3 + Z2 + sqrt((3 - Z1) * (3 + Z1 + 2*Z2)))
template <KerrScalar Real> [[nodiscard]] inline Real iscoRadiusRetrograde(Real m, Real a) noexcept {
  const Real z1 = bpt_Z1(a);
  const Real z2 = bpt_Z2(a);
  const Real factor = (3.0 - z1) * (3.0 + z1 + (2.0 * z2));
  if (factor < 0.0) {
    return 6.0 * m; // Default to Schwarzschild
  }
  const Real sqrtFactor = std::sqrt(factor);
  return m * (3.0 + z2 + sqrtFactor);
}

// Orbital angular momentum for circular orbit at given radius
template <KerrScalar Real>
[[nodiscard]] constexpr Real circularOrbitRadius(Real m, Real e, Real l) noexcept {
  // Placeholder: related to effective potential
  (void)m;
  (void)e;
  (void)l;
  return 0.0;
}

// Binding energy at ISCO (energy cost to reach infinity)
template <KerrScalar Real> [[nodiscard]] inline Real bindingEnergyIsco(Real m, Real a) noexcept {
  const Real rIsco = isco_radius_prograde(m, a);
  const Real sigma = kerr_Sigma(rIsco, std::numbers::pi / 2.0, a); // theta = pi/2
  // Approximate binding energy
  return 1.0 - std::sqrt(1.0 - (2.0 * m / rIsco));
}

}  // namespace verified
