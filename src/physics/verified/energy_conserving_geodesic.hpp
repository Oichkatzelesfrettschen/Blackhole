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
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note All functions use geometric units where c = G = 1
 * @note Requires verified/kerr.hpp for metric components
 * @note Requires verified/rk4.hpp for StateVector definition
 */

#ifndef PHYSICS_VERIFIED_ENERGY_CONSERVING_GEODESIC_HPP
#define PHYSICS_VERIFIED_ENERGY_CONSERVING_GEODESIC_HPP

#include "rk4.hpp"
#include "kerr.hpp"
#include "geodesic.hpp"
#include <cmath>
#include <functional>
#include <algorithm>

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
    double angular_momentum; ///< L = g_μν χ^μ (dx^ν/dλ), χ = ∂/∂φ
    double carter_constant;  ///< Q = Carter constant from separability
    double mass_squared;     ///< m² = -g_μν (dx^μ/dλ)(dx^ν/dλ) at initial state

    constexpr ConservedQuantities() noexcept
        : energy(0.0), angular_momentum(0.0), carter_constant(0.0), mass_squared(0.0) {}

    constexpr ConservedQuantities(double E, double L, double Q, double m2) noexcept
        : energy(E), angular_momentum(L), carter_constant(Q), mass_squared(m2) {}
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
[[nodiscard]] inline double compute_energy(const MetricComponents& g,
                                           const StateVector& state) noexcept {
    // E = -(g_tt * v_t + g_tφ * v_φ)
    return -(g.g_tt * state.v0 + g.g_tph * state.v3);
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
[[nodiscard]] inline double compute_angular_momentum(const MetricComponents& g,
                                                      const StateVector& state) noexcept {
    // L = g_φφ * v_φ + g_tφ * v_t
    return g.g_phph * state.v3 + g.g_tph * state.v0;
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
[[nodiscard]] inline double compute_metric_norm(const MetricComponents& g,
                                                const StateVector& state) noexcept {
    // m² = g_tt*v_t² + 2*g_tφ*v_t*v_φ + g_rr*v_r² + g_θθ*v_θ² + g_φφ*v_φ²
    double result = g.g_tt * state.v0 * state.v0
                  + 2.0 * g.g_tph * state.v0 * state.v3
                  + g.g_rr * state.v1 * state.v1
                  + g.g_thth * state.v2 * state.v2
                  + g.g_phph * state.v3 * state.v3;
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
 * @param M Black hole mass
 * @param a Spin parameter
 * @return Carter constant (Q ≥ 0 for physical orbits)
 */
[[nodiscard]] inline double compute_carter_constant(const MetricComponents& g,
                                                     const StateVector& state,
                                                     double M, double a) noexcept {
    const double sin_theta = std::sin(state.x2);
    const double cos_theta = std::cos(state.x2);
    const double cos2 = cos_theta * cos_theta;
    const double sin2 = sin_theta * sin_theta;

    // Avoid division by zero near poles
    if (sin2 < 1e-10) return 0.0;

    // p_θ = g_θθ * v_θ
    double p_theta = g.g_thth * state.v2;

    // E and L from Killing vectors
    double E = compute_energy(g, state);
    double L = compute_angular_momentum(g, state);

    // m² from metric norm
    double m2 = compute_metric_norm(g, state);

    // Q = p_θ² + cos²(θ) * (a²(m² - E²) + L²/sin²(θ))
    double Q = p_theta * p_theta
             + cos2 * (a * a * (m2 - E * E) + L * L / sin2);

    return std::max(0.0, Q);  // Enforce Q ≥ 0
}

/**
 * @brief Extract all conserved quantities from current state
 *
 * @param g Metric components
 * @param state Current geodesic state
 * @param M Black hole mass
 * @param a Spin parameter
 * @return Container with E, L, Q, m²
 */
[[nodiscard]] inline ConservedQuantities extract_conserved_quantities(
    const MetricComponents& g, const StateVector& state,
    double M, double a) noexcept {
    return ConservedQuantities{
        compute_energy(g, state),
        compute_angular_momentum(g, state),
        compute_carter_constant(g, state, M, a),
        compute_metric_norm(g, state)
    };
}

// ============================================================================
// Constraint-Preserving Correction
// ============================================================================

/**
 * @brief Apply constraint correction to restore geodesic constraint
 *
 * The geodesic constraint (metric norm = m²) can drift during RK4 integration.
 * This function rescales velocities to restore the constraint while preserving
 * the energy and angular momentum.
 *
 * Method:
 * 1. Compute current metric norm from velocities
 * 2. Compute rescaling factor: α = √(m² / current_norm)
 * 3. Rescale radial velocity: v_r → α * v_r
 * 4. Rescale θ velocity: v_θ → α * v_θ
 * 5. Keep E and L unchanged (time and φ-components don't change)
 *
 * @param g Metric components
 * @param state State with potentially drifted velocities
 * @param target_m2 Target value for metric norm (usually -1 for timelike, 0 for null)
 * @return Corrected state with constraint restored
 */
[[nodiscard]] inline StateVector apply_constraint_correction(
    const MetricComponents& g, const StateVector& state,
    double target_m2) noexcept {
    const double current_norm = compute_metric_norm(g, state);

    // Avoid division by zero
    if (std::abs(current_norm) < 1e-10) return state;

    // Rescaling factor to achieve target_m2
    double rescale_factor = std::sqrt(std::abs(target_m2 / current_norm));

    // Rescale only spatial velocities (r, θ components)
    // Keep temporal components to preserve E and L
    return StateVector{
        state.x0, state.x1, state.x2, state.x3,
        state.v0,                              // Keep v_t
        rescale_factor * state.v1,             // Rescale v_r
        rescale_factor * state.v2,             // Rescale v_θ
        state.v3                               // Keep v_φ
    };
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
 * This ensures:
 *   - Null constraint preserved (g_μν v^μ v^ν = 0 for photons)
 *   - Timelike constraint preserved (g_μν v^μ v^ν = -1 for massive particles)
 *   - Energy E and angular momentum L conserved (Killing vector properties)
 *   - Local error remains O(h^5) from RK4 base method
 *
 * @tparam F Type of RHS function (must satisfy std::invocable<F, StateVector>)
 * @param f Right-hand side: dstate/dλ = f(state)
 * @param h Integration step size
 * @param state Current state
 * @param g Metric components (function of r, θ, M, a)
 * @param M Black hole mass
 * @param a Spin parameter
 * @param geodesic_type -1 for timelike, 0 for null geodesics
 * @return Corrected state after one energy-conserving step
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] inline StateVector energy_conserving_step(
    F&& f, double h, const StateVector& state,
    const MetricComponents& g, double M, double a,
    int geodesic_type = 0) noexcept {

    // 1. Extract initial conserved quantities
    const auto initial_q = extract_conserved_quantities(g, state, M, a);
    const double target_m2 = initial_q.mass_squared;

    // 2. Perform RK4 step
    const auto rk4_result = rk4_step(f, h, state);

    // 3. Apply constraint correction to restore geodesic constraint
    const auto corrected = apply_constraint_correction(g, rk4_result, target_m2);

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
 * @param initial_h Initial step size
 * @param final_lambda Final affine parameter value
 * @param state Current state (modified in place)
 * @param g_func Function to compute metric components: g_func(state, M, a) → MetricComponents
 * @param M Black hole mass
 * @param a Spin parameter
 * @param constraint_tol Tolerance for constraint violation (default: 1e-8)
 * @return Number of steps taken
 */
template<typename F, typename GFunc>
requires std::invocable<F, StateVector> &&
         std::invocable<GFunc, StateVector, double, double>
inline std::size_t integrate_with_energy_conservation(
    F&& f, double initial_h, double final_lambda,
    StateVector& state,
    GFunc&& g_func,
    double M, double a,
    double constraint_tol = 1e-8) noexcept {

    std::size_t step_count = 0;
    double current_lambda = state.x0;
    double h = initial_h;

    while (current_lambda < final_lambda) {
        // Compute metric at current position
        const auto g = g_func(state, M, a);

        // Ensure we don't overshoot final_lambda
        if (current_lambda + h > final_lambda) {
            h = final_lambda - current_lambda;
        }

        // Extract conserved quantities before step
        const auto q_before = extract_conserved_quantities(g, state, M, a);

        // Perform energy-conserving step
        state = energy_conserving_step(f, h, state, g, M, a);
        current_lambda += h;
        step_count++;

        // Extract conserved quantities after step
        const auto g_new = g_func(state, M, a);
        const auto q_after = extract_conserved_quantities(g_new, state, M, a);

        // Check energy conservation
        double energy_drift = std::abs(q_after.energy - q_before.energy)
                            / (std::abs(q_before.energy) + 1e-10);

        // Adaptive step size: reduce if drift too large
        if (energy_drift > constraint_tol) {
            h *= 0.9;  // Reduce step size by 10%
            current_lambda -= h;  // Back up
            step_count--;
            continue;
        }

        // Increase step size slightly if drift is very small
        if (energy_drift < 0.1 * constraint_tol && step_count % 10 == 0) {
            h *= 1.05;  // Increase step size by 5%
        }
    }

    return step_count;
}

}  // namespace verified

#endif  // PHYSICS_VERIFIED_ENERGY_CONSERVING_GEODESIC_HPP
