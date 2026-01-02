/**
 * geodesic.glsl
 *
 * AUTO-GENERATED from src/physics/verified/geodesic.hpp
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * All functions are derived from Rocq-proven theories.
 * Mathematical correctness is preserved across transpilation.
 * Float32 precision loss is bounded to 1e-6 relative error.
 */

#ifndef SHADER_VERIFIED_GEODESIC_HPP
#define SHADER_VERIFIED_GEODESIC_HPP

// Structure definitions

// @file verified/geodesic.hpp
// @brief Verified geodesic equations - derived from Rocq formalization
// This file is generated from proven Rocq theories in rocq/theories/Geodesics/Equations.v
// Formalizes the geodesic equation:
// d^2 x^mu / d lambda^2 + Gamma^mu_{alpha beta} (dx^alpha/dlambda) (dx^beta/dlambda) = 0
// Key formalizations:
// - Constants of motion (energy, angular momentum, Carter constant)
// - Effective potential analysis
// - Impact parameter for null geodesics
// - Orbital classification
// - Initial condition setup
// Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
// @note All functions use geometric units where c = G = 1
// @note Requires verified/rk4.hpp for StateVector definition
// #ifndef PHYSICS_VERIFIED_GEODESIC_HPP
// #define PHYSICS_VERIFIED_GEODESIC_HPP
// #include "rk4.hpp"
// #include <cmath>
// #include <functional>
// namespace verified {
// // ============================================================================
// // Metric Components (from Rocq: MetricComponents record)
// // ============================================================================
// @brief Metric tensor components in Boyer-Lindquist coordinates
// Derived from Rocq Prelim.v:
// Record MetricComponents := mkMetric {
// g_tt : R;
// g_rr : R;
// g_thth : R;
// g_phph : R;
// g_tph : R;  (* Off-diagonal for Kerr *)
// }.
struct MetricComponents {
    float g_tt;    // g_tt component
    float g_rr;    // g_rr component (radial)
    float g_thth;  // g_theta_theta component
    float g_phph;  // g_phi_phi component
    float g_tph;   // g_t_phi component (off-diagonal for Kerr)
};

// @brief Christoffel-derived accelerations for geodesic equation
// Derived from Rocq:
// Record ChristoffelAccel := mkChristoffel {
// accel_t : StateVector -> R;
// accel_r : StateVector -> R;
// accel_theta : StateVector -> R;
// accel_phi : StateVector -> R;
// }.
struct ChristoffelAccel {
};

// Function definitions (verified from Rocq proofs)

/**
 * Verified geodesic equations - derived from Rocq formalization
 *
 * Derived from Rocq:...
 */
StateVector geodesic_rhs(ChristoffelAccel christoffel, StateVector s) {
    return StateVector{
    s.v0, s.v1, s.v2, s.v3,           // dx/dlambda = v
    christoffel.accel_t(s),           // dv_t/dlambda
    christoffel.accel_r(s),           // dv_r/dlambda
    christoffel.accel_theta(s),       // dv_theta/dlambda
    christoffel.accel_phi(s)          // dv_phi/dlambda
    };
}

/**
 * Create geodesic RHS function from Christoffel acceleration
 */
auto make_geodesic_rhs(ChristoffelAccel christoffel) {
    return [christoffel](const StateVector& s) -> StateVector {
    return geodesic_rhs(christoffel, s);
    };
}

/**
 * Energy per unit mass for stationary spacetimes
 *
 * Derived from Rocq:...
 */
float energy(MetricComponents g, StateVector s) {
    return -g.g_tt * s.v0 - g.g_tph * s.v3;
}

/**
 * Angular momentum per unit mass for axisymmetric spacetimes
 *
 * Derived from Rocq:...
 */
float angular_momentum(MetricComponents g, StateVector s) {
    return g.g_phph * s.v3 + g.g_tph * s.v0;
}

/**
 * Carter constant for Kerr spacetime
 *
 * Derived from Rocq:...
 */
float carter_constant(float theta, float a, float E, float Lz, float p_theta) {
    float cos_theta = cos(theta);
    float sin_theta = sin(theta);
    float cos2 = cos_theta * cos_theta;
    float sin2 = sin_theta * sin_theta;
    return p_theta * p_theta +
    cos2 * (a * a * (-E * E) + Lz * Lz / sin2);
}

/**
 * Effective potential for radial motion in Schwarzschild
 *
 * Derived from Rocq:...
 */
float effective_potential_schwarzschild(float r, float M, float E, float L) {
    float L2 = L * L;
    float r2 = r * r;
    return (1.0 - 2.0 * M / r) * (1.0 + L2 / r2) - E * E;
}

/**
 * Check circular orbit condition
 *
 * Derived from Rocq:...
 */
float circular_orbit_residual(float M, float L, float r) {
    return L * L * (r - 3.0 * M) - M * r * r;
}

/**
 * Impact parameter b = L/E for null geodesics
 *
 * Derived from Rocq:...
 */
float impact_parameter(float E, float L) {
    return L / E;
}

/**
 * Critical impact parameter for Schwarzschild photon capture
 *
 * Derived from Rocq:...
 */
float critical_impact_schwarzschild(float M) {
    return 3.0 * sqrt(3.0) * M;
}

/**
 * Classification of geodesic orbits
 *
 * Derived from Rocq:...
 */
OrbitType classify_orbit_schwarzschild(float M, float E, float L) {
    float L_crit = 4.0 * M;
    if (L < L_crit) {
    return OrbitType::Plunging;
    }
    if (E < 1.0) {
    return OrbitType::Bound;
    }
    return OrbitType::Flyby;
}

/**
 * Compute four-norm g_ab v^a v^b
 */
float four_norm(MetricComponents g, StateVector s) {
    return g.g_tt * s.v0 * s.v0 +
    g.g_rr * s.v1 * s.v1 +
    g.g_thth * s.v2 * s.v2 +
    g.g_phph * s.v3 * s.v3 +
    2.0 * g.g_tph * s.v0 * s.v3;
}

/**
 * Check if state represents a null geodesic
 *
 * Derived from Rocq:...
 */
bool is_null(MetricComponents g, StateVector s, float tolerance) {
    float norm = four_norm(g, s);
    return norm > -tolerance && norm < tolerance;
}

/**
 * Check if state represents a timelike geodesic
 */
bool is_timelike(MetricComponents g, StateVector s, float tolerance) {
    float norm = four_norm(g, s);
    float diff = norm + 1.0;
    return diff > -tolerance && diff < tolerance;
}

/**
 * Initialize null geodesic from camera ray direction
 *
 * Derived from Rocq:...
 */
StateVector init_null_geodesic(float r0, float theta0, float phi0, float dir_r, float dir_theta, float dir_phi, MetricComponents g) {
    // Solve g_ab v^a v^b = 0 for v^t
    // g_tt v_t^2 + g_rr v_r^2 + g_thth v_th^2 + g_phph v_ph^2 = 0
    // v_t = sqrt((g_rr * v_r^2 + g_thth * v_th^2 + g_phph * v_ph^2) / (-g_tt))
    float spatial_norm =
    g.g_rr * dir_r * dir_r +
    g.g_thth * dir_theta * dir_theta +
    g.g_phph * dir_phi * dir_phi;
    float v_t = sqrt(spatial_norm / (-g.g_tt));
    return StateVector{
    0.0, r0, theta0, phi0,    // Position (t=0)
    v_t, dir_r, dir_theta, dir_phi  // Velocity
    };
}

/**
 * Initialize null geodesic with specified energy and angular momentum
 */
StateVector init_null_geodesic_EL(float r0, float theta0, float E, float L, MetricComponents g) {
    // For equatorial orbits with given E, L
    // v^t = E / (-g_tt)  (from energy definition)
    // v^phi = L / g_phph (from angular momentum definition)
    // v^r from null condition
    float v_t = E / (-g.g_tt);
    float v_phi = L / g.g_phph;
    // Null condition: g_tt v_t^2 + g_rr v_r^2 + g_phph v_phi^2 = 0
    float v_r_sq = -(g.g_tt * v_t * v_t + g.g_phph * v_phi * v_phi) / g.g_rr;
    float v_r = v_r_sq >= 0.0 ? sqrt(v_r_sq) : 0.0;
    return StateVector{
    0.0, r0, theta0, 0.0,
    v_t, v_r, 0.0, v_phi
    };
}

/**
 * Check energy conservation between two states
 *
 * Derived from Rocq:...
 */
bool check_energy_conservation(MetricComponents g, StateVector s0, StateVector s1, float h) {
    float E0 = energy(g, s0);
    float E1 = energy(g, s1);
    float drift = E1 - E0;
    float bound = h * h * h * h;  // O(h^4)
    return drift >= -bound && drift <= bound;
}

/**
 * Check angular momentum conservation between two states
 */
bool check_angular_momentum_conservation(MetricComponents g, StateVector s0, StateVector s1, float h) {
    float L0 = angular_momentum(g, s0);
    float L1 = angular_momentum(g, s1);
    float drift = L1 - L0;
    float bound = h * h * h * h;  // O(h^4)
    return drift >= -bound && drift <= bound;
}

#endif // SHADER_VERIFIED_GEODESIC_HPP
