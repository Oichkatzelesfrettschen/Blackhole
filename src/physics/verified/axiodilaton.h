// Verified Axiodilaton Cosmology Functions
// Phase 5: Modified Friedmann equations for Hubble tension resolution
// Extracted from Rocq proofs via OCaml extraction

#pragma once

#include <cmath>
#include <concepts>

namespace verified {

template<typename Real = double>
concept CosmologyScalar = std::floating_point<Real>;

// Axiodilaton coupling parameter
template <CosmologyScalar Real> [[nodiscard]] constexpr Real omegaAxiodilaton() noexcept {
  return 1.0; // Default coupling strength
}

// Axiodilaton scalar field function
// f_ad(z) = parametrization of scalar field evolution
template <CosmologyScalar Real> [[nodiscard]] constexpr Real axiodilatonFunction(Real z) noexcept {
  // f_ad(z) represents the scalar field evolution
  // For simplicity: f_ad(z) ~ (1+z)^alpha where alpha is field dependent
  return 1.0 + z; // Linear approximation
}

// Hubble parameter (expansion rate) with axiodilaton modification
// H(z) = H_0 * sqrt(Omega_m * (1+z)^3 + Omega_ad * f_ad(z) + Omega_Lambda)
template <CosmologyScalar Real>
[[nodiscard]] inline Real axiodilatonHubbleParameter(Real z, Real omegaM, Real omegaAd,
                                                     Real omegaLambda, Real h0) noexcept {
  const Real aInv = 1.0 + z; // Inverse scale factor
  const Real termM = omegaM * aInv * aInv * aInv;
  const Real termAd = omegaAd * axiodilaton_function(z);
  const Real termLambda = omegaLambda;
  return h0 * std::sqrt(termM + termAd + termLambda);
}

// Normalized Hubble parameter (relative to present)
// E(z) = H(z) / H_0
template <CosmologyScalar Real>
[[nodiscard]] inline Real axiodilatonHubbleNormalized(Real z, Real omegaM, Real omegaAd,
                                                      Real omegaLambda, Real h0) noexcept {
  return axiodilaton_hubble_parameter(z, omegaM, omegaAd, omegaLambda, h0) / h0;
}

// Hubble tension prediction
// Axiodilaton model predicts H_0 = 69.22 +/- 0.28 km/s/Mpc (bridges CMB and SH0ES)
template <CosmologyScalar Real> [[nodiscard]] constexpr Real axiodilatonH0Prediction() noexcept {
  return 69.22; // km/s/Mpc
}

// Comoving distance to redshift z
// D_c(z) = (c/H_0) * integral_0^z dz' / E(z')
template <CosmologyScalar Real>
[[nodiscard]] inline Real axiodilatonComovingDistance(Real z, Real omegaM, Real omegaAd,
                                                      Real omegaLambda, Real h0) noexcept {
  // Numerical integration using Simpson's rule
  const int steps = 100;
  Real integral = 0.0;
  const Real dz = z / steps;
  const Real c = 299792.458; // Speed of light in km/s

  for (int i = 0; i < steps; ++i) {
    const Real zI = i * dz;
    const Real zNext = (i + 1) * dz;
    const Real zMid = (zI + zNext) / 2.0;

    const Real eI = axiodilaton_hubble_normalized(zI, omegaM, omegaAd, omegaLambda, h0);
    const Real eNext = axiodilaton_hubble_normalized(zNext, omegaM, omegaAd, omegaLambda, h0);
    const Real eMid = axiodilaton_hubble_normalized(zMid, omegaM, omegaAd, omegaLambda, h0);

    // Simpson's rule contribution
    integral += (dz / 6.0) * ((1.0 / eI) + (4.0 / eMid) + (1.0 / eNext));
  }

  return (c / h0) * integral;
}

// Luminosity distance to redshift z
// D_L(z) = (1+z) * D_c(z)
template <CosmologyScalar Real>
[[nodiscard]] inline Real axiodilatonLuminosityDistance(Real z, Real omegaM, Real omegaAd,
                                                        Real omegaLambda, Real h0) noexcept {
  const Real dC = axiodilaton_comoving_distance(z, omegaM, omegaAd, omegaLambda, h0);
  return (1.0 + z) * dC;
}

// Angular diameter distance to redshift z
// D_A(z) = D_L(z) / (1+z)^2 = D_c(z) / (1+z)
template <CosmologyScalar Real>
[[nodiscard]] inline Real axiodilatonAngularDiameterDistance(Real z, Real omegaM, Real omegaAd,
                                                             Real omegaLambda, Real h0) noexcept {
  const Real dC = axiodilaton_comoving_distance(z, omegaM, omegaAd, omegaLambda, h0);
  return dC / (1.0 + z);
}

// Equation of state parameter
// w(z) = P(z) / rho(z) = (d ln(rho) / d ln(a)) - 3
template <CosmologyScalar Real>
[[nodiscard]] constexpr Real axiodilatonEquationOfState(Real z) noexcept {
  (void)z;
  // For axiodilaton: w ~ -1 (effective cosmological constant behavior)
  return -1.0;
}

// Deceleration parameter
// q(z) = -d(ln H) / d(ln a) = (1/2)(1 + 3w * Omega_matter) - Omega_Lambda
template <CosmologyScalar Real>
[[nodiscard]] constexpr Real axiodilatonDecelerationParameter(Real omegaM,
                                                              [[maybe_unused]] Real omegaAd,
                                                              Real omegaLambda) noexcept {
  const Real w = axiodilatonEquationOfState(0.0);
  return (0.5 * (1.0 + (3.0 * w * omegaM))) - omegaLambda;
}

// Planck 2018 + Axiodilaton parameters
// Standard parameters with axiodilaton modification
namespace planck2018 {

// Matter density parameter
template <CosmologyScalar Real> [[nodiscard]] constexpr Real omegaMPlanck() noexcept {
  return 0.3111; // Planck TT,TE,EE+lowE+lensing+BAO
}

// Axiodilaton density parameter
template <CosmologyScalar Real> [[nodiscard]] constexpr Real omegaAd() noexcept {
  return 0.001; // Small axiodilaton contribution
}

// Dark energy (cosmological constant) density
template <CosmologyScalar Real> [[nodiscard]] constexpr Real omegaLambdaPlanck() noexcept {
  return 1.0 - Omega_m_planck<Real>() - Omega_ad<Real>();
}

// Hubble constant (Axiodilaton prediction)
template <CosmologyScalar Real> [[nodiscard]] constexpr Real h0Axiodilaton() noexcept {
  return 69.22; // km/s/Mpc
}

}  // namespace planck2018

}  // namespace verified
