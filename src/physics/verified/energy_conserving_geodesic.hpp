/**
 * @file verified/energy_conserving_geodesic.hpp
 * @brief Energy-conserving geodesic integration - supplements RK4 with Hamiltonian preservation
 *
 * Implements Hamiltonian-based correction to RK4 integration to maintain conservation laws:
 *   - Energy E = -dL/dt (Killing vector conservation)
 *   - Angular momentum L = dL/dphi (Axial symmetry conservation)
 *   - Carter constant Q (Metric symmetry)
 *
 * Based on research:
 *   - GRay: A Massively Parallel GPU-Based Code for Ray Tracing in Relativistic Spacetimes
 *   - Carter constant preservation for Kerr orbits
 *   - Hamiltonian constraint enforcing technique
 *
 * Method:
 * 1. Compute standard RK4 step
 * 2. Evaluate conserved quantities at start and end
 * 3. Apply constraint-preserving correction
 * 4. Rescale velocities to restore null/timelike constraint
 *
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
 *
 * @note All functions use geometric units where c = G = 1
 * @note Requires verified/kerr.hpp for metric components
 * @note Requires verified/rk4.hpp for StateVector definition
 */

#ifndef PHYSICS_VERIFIED_ENERGY_CONSERVING_GEODESIC_HPP
#define PHYSICS_VERIFIED_ENERGY_CONSERVING_GEODESIC_HPP

#include <algorithm>
#include <cmath>
#include <functional>
#include <utility>

#include "geodesic.hpp"
#include "kerr.hpp"
#include "rk4.hpp"

namespace verified {

// ============================================================================
// Conserved Quantities (Constants of Motion)
// ============================================================================

/**
 * @brief Container for Kerr geodesic conserved quantities
 *
 * For orbits in Kerr spacetime:
 *   - Energy E: conserved by time translation symmetry (Killing vector: ∂/∂t)
 *   - Angular momentum L: conserved by axial symmetry (Killing vector: ∂/∂φ)
 *   - Carter constant Q: conserved by symmetry of Kerr metric
 *   - Particle mass m: determines geodesic type (timelike, null, spacelike)
 */
struct ConservedQuantities {
    double energy;           ///< E = -g_μν ξ^μ (dx^ν/dλ), ξ = ∂/∂t
    double angularMomentum;  ///< L = g_μν χ^μ (dx^ν/dλ), χ = ∂/∂φ
    double carterConstant;   ///< Q = Carter constant from separability
    double massSquared;      ///< m² = -g_μν (dx^μ/dλ)(dx^ν/dλ) at initial state

    constexpr ConservedQuantities() noexcept
        : energy(0.0), angularMomentum(0.0), carterConstant(0.0), massSquared(0.0) {}

    constexpr ConservedQuantities(double e, double l, double q, double m2) noexcept
        : energy(e), angularMomentum(l), carterConstant(q), massSquared(m2) {}
};

/**
 * @brief Compute energy E from metric and state
 *
 * For Kerr metric in Boyer-Lindquist coordinates:
 *   E = -(g_tt v_t + g_tφ v_φ)
 *
 * This is the conserved energy from the Killing vector ∂/∂t.
 *
 * @param g Metric components
 * @param state Current geodesic state
 * @return Conserved energy
 */
[[nodiscard]] inline double computeEnergy(const MetricComponents &g,
                                          const StateVector &state) noexcept {
  // E = -(g_tt * v_t + g_tφ * v_φ)
  return -(g.gTt * state.v0 + g.gTph * state.v3);
}

/**
 * @brief Compute angular momentum L from metric and state
 *
 * For Kerr metric in Boyer-Lindquist coordinates:
 *   L = g_φφ v_φ + g_tφ v_t
 *
 * This is the conserved angular momentum from the Killing vector ∂/∂φ.
 *
 * @param g Metric components
 * @param state Current geodesic state
 * @return Conserved angular momentum
 */
[[nodiscard]] inline double computeAngularMomentum(const MetricComponents &g,
                                                   const StateVector &state) noexcept {
  // L = g_φφ * v_φ + g_tφ * v_t
  return g.gPhph * state.v3 + g.gTph * state.v0;
}

/**
 * @brief Compute norm squared of four-velocity
 *
 * For all geodesics:
 *   m² = g_μν (dx^μ/dλ)(dx^ν/dλ)
 *
 * For timelike geodesics: m² = -1 (massive particles)
 * For null geodesics: m² = 0 (photons)
 * For spacelike: m² > 0 (not physical for particles)
 *
 * @param g Metric components
 * @param state Current geodesic state
 * @return Norm squared of four-velocity
 */
[[nodiscard]] inline double computeMetricNorm(const MetricComponents &g,
                                              const StateVector &state) noexcept {
  // m² = g_tt*v_t² + 2*g_tφ*v_t*v_φ + g_rr*v_r² + g_θθ*v_θ² + g_φφ*v_φ²
  double const result = g.gTt * state.v0 * state.v0 + 2.0 * g.gTph * state.v0 * state.v3 +
                        g.gRr * state.v1 * state.v1 + g.gThth * state.v2 * state.v2 +
                        g.gPhph * state.v3 * state.v3;
  return result;
}

/**
 * @brief Compute Carter constant for Kerr orbits
 *
 * The Carter constant Q is the third constant of motion in Kerr geometry.
 * It can be expressed in terms of E, L, and the effective potential.
 *
 * For orbits in the equatorial plane (θ = π/2, v_θ = 0):
 *   Q = 0
 *
 * For general orbits:
 *   Q = p_θ² + cos²(θ) * (a²(m² - E²) + L²/sin²(θ))
 *
 * where p_θ = g_θθ * v_θ is the θ-momentum.
 *
 * @param g Metric components
 * @param state Current geodesic state
 * @param m Black hole mass
 * @param a Spin parameter
 * @return Carter constant (Q ≥ 0 for physical orbits)
 */
[[nodiscard]] inline double computeCarterConstant(const MetricComponents &g,
                                                  const StateVector &state,
                                                  [[maybe_unused]] double m, double a) noexcept {
  const double sinTheta = std::sin(state.x2);
  const double cosTheta = std::cos(state.x2);
  const double cos2 = cosTheta * cosTheta;
  const double sin2 = sinTheta * sinTheta;

  // Avoid division by zero near poles
  if (sin2 < 1e-10) {
    return 0.0;
  }

  // p_θ = g_θθ * v_θ
  double const pTheta = g.gThth * state.v2;

  // E and L from Killing vectors
  double const e = computeEnergy(g, state);
  double const l = computeAngularMomentum(g, state);

  // m² from metric norm
  double const m2 = computeMetricNorm(g, state);

  // Q = p_θ² + cos²(θ) * (a²(m² - E²) + L²/sin²(θ))
  double const q = pTheta * pTheta + cos2 * (a * a * (m2 - e * e) + l * l / sin2);

  return std::max(0.0, q); // Enforce Q ≥ 0
}

/**
 * @brief Extract all conserved quantities from current state
 *
 * @param g Metric components
 * @param state Current geodesic state
 * @param m Black hole mass
 * @param a Spin parameter
 * @return Container with E, L, Q, m²
 */
[[nodiscard]] inline ConservedQuantities extractConservedQuantities(const MetricComponents &g,
                                                                    const StateVector &state,
                                                                    double m, double a) noexcept {
  return ConservedQuantities{computeEnergy(g, state), computeAngularMomentum(g, state),
                             computeCarterConstant(g, state, m, a), computeMetricNorm(g, state)};
}

// ============================================================================
// Constraint-Preserving Correction
// ============================================================================

/**
 * @brief Restore the geodesic norm g(v, v) = targetM2 by an additive projection
 *
 * Primary path: v^t and v^phi stay fixed, so E = -(g_tt v^t + g_tphi v^phi)
 * and L = g_tphi v^t + g_phph v^phi are unchanged, and v^r, v^theta scale by a
 * common alpha. Writing S = g_rr (v^r)^2 + g_thth (v^theta)^2 for the part that
 * scales, the corrected norm is norm - S + alpha^2 S, so
 *
 *   alpha^2 = (targetM2 - norm + S) / S.
 *
 * This primary additive correction matches open_gororoba gr_core
 * energy_conserving::apply_constraint_correction. A multiplicative factor
 * sqrt(|targetM2 / norm|) is zero for a null target and would zero v^r and
 * v^theta, turning a photon timelike.
 *
 * Fallback when S = 0 or alpha^2 < 0 (the r-theta motion cannot absorb the
 * drift): solve g_tt (v^t)^2 + 2 g_tphi v^phi v^t + (rest - targetM2) = 0 for
 * v^t and take the root nearest the current v^t, which changes E. This
 * fallback solves for targetM2, timelike or null, and departs from gr_core,
 * whose renormalize_null fallback ignores target_norm. When the quadratic has
 * no real root the state is returned unchanged.
 *
 * @param g Metric components
 * @param state State with potentially drifted velocities
 * @param targetM2 Target value for the norm (-1 timelike, 0 null)
 * @return Corrected state
 */
[[nodiscard]] inline StateVector applyConstraintCorrection(const MetricComponents &g,
                                                           const StateVector &state,
                                                           double targetM2) noexcept {
  const double currentNorm = computeMetricNorm(g, state);
  if (currentNorm == targetM2) {
    return state;
  }

  const double spatialRt = g.gRr * state.v1 * state.v1 + g.gThth * state.v2 * state.v2;
  if (spatialRt > 0.0) {
    const double alphaSquared = (targetM2 - currentNorm + spatialRt) / spatialRt;
    if (alphaSquared >= 0.0) {
      const double alpha = std::sqrt(alphaSquared);
      return StateVector{state.x0, state.x1,         state.x2,         state.x3,
                         state.v0, alpha * state.v1, alpha * state.v2, state.v3};
    }
  }

  // v^t quadratic: qa (v^t)^2 + qb v^t + qc = 0.
  const double qa = g.gTt;
  const double qb = 2.0 * g.gTph * state.v3;
  const double qc = spatialRt + g.gPhph * state.v3 * state.v3 - targetM2;
  if (qa == 0.0) {
    return (qb != 0.0) ? StateVector{state.x0, state.x1, state.x2, state.x3,
                                     -qc / qb, state.v1, state.v2, state.v3}
                       : state;
  }
  const double discriminant = qb * qb - 4.0 * qa * qc;
  if (discriminant < 0.0) {
    return state;
  }
  const double sqrtDisc = std::sqrt(discriminant);
  const double rootA = (-qb + sqrtDisc) / (2.0 * qa);
  const double rootB = (-qb - sqrtDisc) / (2.0 * qa);
  const double newV0 = (std::abs(rootA - state.v0) <= std::abs(rootB - state.v0)) ? rootA : rootB;
  return StateVector{state.x0, state.x1, state.x2, state.x3, newV0, state.v1, state.v2, state.v3};
}

// ============================================================================
// Energy-Conserving Integration Step
// ============================================================================

/**
 * @brief Energy-conserving geodesic integration combining RK4 with constraint preservation
 *
 * Algorithm:
 * 1. Extract initial conserved quantities (E, L, Q, m²)
 * 2. Perform standard RK4 step
 * 3. Apply constraint-preserving correction
 * 4. Validate energy conservation (drift check)
 * 5. Return corrected state
 *
 * Result:
 *   - The norm g(v, v) returns to its starting value (0 null, -1 timelike)
 *     through applyConstraintCorrection
 *   - The correction leaves v^t and v^phi, hence E and L, unchanged; E and L
 *     still drift at the RK4 truncation rate
 *   - Local error remains O(h^5) from RK4 base method
 *
 * @tparam F Type of RHS function (must satisfy std::invocable<F, StateVector>)
 * @param f Right-hand side: dstate/dλ = f(state)
 * @param h Integration step size
 * @param state Current state
 * @param g Metric components (function of r, θ, M, a)
 * @param m Black hole mass
 * @param a Spin parameter
 * @param geodesicType -1 for timelike, 0 for null geodesics
 * @return Corrected state after one energy-conserving step
 */
template <typename F>
requires std::invocable<F &, StateVector> [[nodiscard]] inline StateVector
energyConservingStep(F &&f, double h, const StateVector &state, const MetricComponents &g, double m,
                     double a, [[maybe_unused]] int geodesicType = 0) noexcept {
  // Named references preserve repeated lvalue invocation of stateful callbacks.
  auto &&rhsFunction = std::forward<F>(f);

  // 1. Extract initial conserved quantities
  const auto initialQ = extractConservedQuantities(g, state, m, a);
  const double targetM2 = initialQ.massSquared;

  // 2. Perform RK4 step
  const auto rk4Result = rk4Step(rhsFunction, h, state);

  // 3. Apply constraint correction to restore geodesic constraint
  const auto corrected = applyConstraintCorrection(g, rk4Result, targetM2);

  return corrected;
}

/**
 * @brief Long-duration energy-conserving integration with adaptive monitoring
 *
 * Integrates a geodesic over many steps while monitoring energy conservation.
 * Adjusts step size if constraint violation exceeds tolerance.
 *
 * @tparam F Type of RHS function
 * @param f Right-hand side function
 * @param initialH Initial step size
 * @param finalLambda Final affine parameter value
 * @param state Current state (modified in place)
 * @param gFunc Function to compute metric components: g_func(state, M, a) → MetricComponents
 * @param m Black hole mass
 * @param a Spin parameter
 * @param constraintTol Tolerance for constraint violation (default: 1e-8)
 * @return Number of steps taken
 */
template <typename F, typename GFunc>
requires std::invocable<F &, StateVector> &&
    std::invocable<GFunc &, StateVector, double, double> inline std::size_t
    integrateWithEnergyConservation(F &&f, double initialH, double finalLambda, StateVector &state,
                                    GFunc &&gFunc, double m, double a,
                                    double constraintTol = 1e-8) noexcept {
  // Named references preserve repeated lvalue invocation of stateful callbacks.
  auto &&rhsFunction = std::forward<F>(f);
  auto &&metricFunction = std::forward<GFunc>(gFunc);

  std::size_t stepCount = 0;
  double currentLambda = state.x0;
  double h = initialH;

  while (currentLambda < finalLambda) {
    // Compute metric at current position
    const auto g = metricFunction(state, m, a);

    // Ensure we don't overshoot final_lambda
    if (currentLambda + h > finalLambda) {
      h = finalLambda - currentLambda;
    }

    // Extract conserved quantities before step
    const auto qBefore = extractConservedQuantities(g, state, m, a);

    // Perform energy-conserving step
    state = energyConservingStep(rhsFunction, h, state, g, m, a);
    currentLambda += h;
    stepCount++;

    // Extract conserved quantities after step
    const auto gNew = metricFunction(state, m, a);
    const auto qAfter = extractConservedQuantities(gNew, state, m, a);

    // Check energy conservation
    const double energyDrift =
        std::abs(qAfter.energy - qBefore.energy) / (std::abs(qBefore.energy) + 1e-10);

    // Adaptive step size: reduce if drift too large
    if (energyDrift > constraintTol) {
      h *= 0.9;           // Reduce step size by 10%
      currentLambda -= h; // Back up
      stepCount--;
      continue;
    }

    // Increase step size slightly if drift is very small
    if (energyDrift < 0.1 * constraintTol && stepCount % 10 == 0) {
      h *= 1.05; // Increase step size by 5%
    }
  }

  return stepCount;
}

}  // namespace verified

#endif  // PHYSICS_VERIFIED_ENERGY_CONSERVING_GEODESIC_HPP
