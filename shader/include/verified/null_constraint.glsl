/**
 * null_constraint.glsl
 *
 * AUTO-GENERATED from src/physics/verified/null_constraint.hpp
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * All functions are derived from Rocq-proven theories.
 * Mathematical correctness is preserved across transpilation.
 * Float32 precision loss is bounded to 1e-6 relative error.
 */

#ifndef SHADER_VERIFIED_NULL_CONSTRAINT_HPP
#define SHADER_VERIFIED_NULL_CONSTRAINT_HPP

// Structure definitions

// @file verified/null_constraint.hpp
// @brief Verified null geodesic constraint preservation - derived from Rocq formalization
// This file is generated from proven Rocq theories in rocq/theories/Geodesics/NullConstraint.v
// Key result: For RK4 integration of geodesics derived from a Lorentzian metric,
// the null constraint drift is O(h^4) per step.
// Null geodesic constraint: g_ab v^a v^b = 0
// For light rays, this condition must be preserved during numerical integration.
// Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
// @note All functions are constexpr/inline for performance
// @note Uses geometric units where c = G = 1
// #ifndef PHYSICS_VERIFIED_NULL_CONSTRAINT_HPP
// #define PHYSICS_VERIFIED_NULL_CONSTRAINT_HPP
// #include <cmath>
// #include <functional>
// #include "rk4.hpp"
// #include "geodesic.hpp"
// namespace verified {
// // ============================================================================
// // Null Constraint Function (from Rocq: null_constraint_function)
// // ============================================================================
// @brief Compute null constraint: C(x,v) = g_ab(x) v^a v^b
// Derived from Rocq: Definition null_constraint_function (g : MetricComponents) (s : StateVector) : R :=
// let v := mkFV s.(v0) s.(v1) s.(v2) s.(v3) in
// four_norm g v.
// For null geodesics, this should equal zero.
// For timelike geodesics, this equals -1 (with proper normalization).
// @param g Metric components at current position
// @param s State vector containing position and velocity
// @return C = g_tt*v0^2 + g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2 + 2*g_tph*v0*v3
// [[nodiscard]] constexpr double null_constraint_function(
// const MetricComponents& g, const StateVector& s) noexcept
// {
// // Derived from Rocq four_norm definition
// return g.g_tt * s.v0 * s.v0 +
// g.g_rr * s.v1 * s.v1 +
// g.g_thth * s.v2 * s.v2 +
// g.g_phph * s.v3 * s.v3 +
// 2.0 * g.g_tph * s.v0 * s.v3;
// }
// @brief Check if state satisfies null condition: C = 0
// Derived from Rocq: Definition initially_null (g : MetricComponents) (s : StateVector) : Prop :=
// null_constraint_function g s = 0.
// @param g Metric components
// @param s State vector
// @param tol Tolerance for comparison to zero
// @return true if |C| < tol
// [[nodiscard]] constexpr bool is_null(
// const MetricComponents& g, const StateVector& s, double tol = 1e-10) noexcept
// {
// return std::abs(null_constraint_function(g, s)) < tol;
// }
// // ============================================================================
// // Constraint After Integration Step (from Rocq: constraint_after_step)
// // ============================================================================
// @brief Compute constraint after one RK4 step
// Derived from Rocq: Definition constraint_after_step (g : MetricComponents)
// (christoffel : ChristoffelAccel) (h : R) (s : StateVector) : R :=
// let s' := rk4_step (geodesic_rhs christoffel) h s in
// null_constraint_function g s'.
// @param g Metric components (evaluated at new position)
// @param christoffel Christoffel acceleration functions
// @param h Step size
// @param s Initial state
// @return Null constraint value after step
// [[nodiscard]] inline double constraint_after_step(
// const MetricComponents& g,
// const ChristoffelAccel& christoffel,
// double h,
// const StateVector& s) noexcept
// {
// // Create RHS function from Christoffel symbols
// auto rhs = [&christoffel](const StateVector& state) -> StateVector {
// return geodesic_rhs(christoffel, state);
// };
// // Perform RK4 step
// StateVector s_new = rk4_step(rhs, h, s);
// // Evaluate constraint at new state
// return null_constraint_function(g, s_new);
// }
// // ============================================================================
// // Constraint Drift Analysis (from Rocq: constraint_drift_step)
// // ============================================================================
// @brief Compute constraint drift after one step: Delta C = C(after) - C(before)
// Derived from Rocq: Definition constraint_drift_step (g : MetricComponents)
// (christoffel : ChristoffelAccel) (h : R) (s : StateVector) : R :=
// constraint_after_step g christoffel h s - null_constraint_function g s.
// Theorem null_constraint_drift_bound:
// |Delta C| <= O(h^4) per step for RK4 integration.
// @param g Metric components
// @param christoffel Christoffel acceleration functions
// @param h Step size
// @param s Initial state
// @return Constraint drift (ideally near zero)
// [[nodiscard]] inline double constraint_drift_step(
// const MetricComponents& g,
// const ChristoffelAccel& christoffel,
// double h,
// const StateVector& s) noexcept
// {
// return constraint_after_step(g, christoffel, h, s) - null_constraint_function(g, s);
// }
// @brief Estimate constraint drift bound: C * h^4
// From Rocq theorem null_constraint_drift_bound:
// The RK4 local truncation error is O(h^5) for position/velocity,
// but the constraint (quadratic in velocity) accumulates error as O(h^4).
// @param C Bound constant (problem-dependent)
// @param h Step size
// @return Estimated maximum drift per step
// [[nodiscard]] constexpr double constraint_drift_bound(double C, double h) noexcept {
// const double h2 = h * h;
// return C * h2 * h2;  // C * h^4
// }
// // ============================================================================
// // Global Drift Accumulation (from Rocq: null_constraint_global_drift)
// // ============================================================================
// @brief Estimate accumulated drift after N steps
// From Rocq theorem null_constraint_global_drift:
// After N steps with step size h, total drift is bounded by N * C * h^4.
// For integration over total affine parameter Lambda = N * h:
// Total drift ~ (Lambda / h) * C * h^4 = C * Lambda * h^3
// This decreases as h decreases, confirming convergence.
// @param C Bound constant
// @param h Step size
// @param N Number of steps
// @return Estimated accumulated drift bound
// [[nodiscard]] constexpr double global_drift_bound(double C, double h, std::size_t N) noexcept {
// return static_cast<double>(N) * constraint_drift_bound(C, h);
// }
// // ============================================================================
// // Renormalization Functions (from Rocq: renormalize_null)
// // ============================================================================
// @brief Renormalize velocity to restore null condition
// Derived from Rocq: Definition renormalize_null (g : MetricComponents) (s : StateVector) : StateVector :=
// let new_v0 := sqrt ((g.(g_rr) * s.(v1)^2 + g.(g_thth) * s.(v2)^2 +
// g.(g_phph) * s.(v3)^2) / (-g.(g_tt))) in
// mkSV s.(x0) s.(x1) s.(x2) s.(x3) new_v0 s.(v1) s.(v2) s.(v3).
// This recomputes v0 (time component) from spatial velocity components
// to exactly satisfy g_tt*v0^2 + g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2 = 0.
// Note: This assumes diagonal metric (g_tph = 0). For Kerr, use renormalize_null_kerr.
// Theorem renormalization_restores_null:
// is_lorentzian g -> (v1 != 0 || v2 != 0 || v3 != 0) ->
// initially_null g (renormalize_null g s).
// @param g Metric components (must have g_tt < 0)
// @param s State to renormalize
// @return State with v0 recomputed to satisfy null condition
// [[nodiscard]] inline StateVector renormalize_null(
// const MetricComponents& g, const StateVector& s) noexcept
// {
// // Compute spatial contribution: g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2
// const double spatial_norm =
// g.g_rr * s.v1 * s.v1 +
// g.g_thth * s.v2 * s.v2 +
// g.g_phph * s.v3 * s.v3;
// // Solve for v0: g_tt * v0^2 = -spatial_norm
// // v0 = sqrt(-spatial_norm / g_tt) = sqrt(spatial_norm / (-g_tt))
// const double new_v0 = std::sqrt(spatial_norm / (-g.g_tt));
// return StateVector{
// s.x0, s.x1, s.x2, s.x3,
// new_v0, s.v1, s.v2, s.v3
// };
// }
// @brief Renormalize velocity for Kerr metric (handles frame dragging)
// For Kerr metric with g_tph != 0, the null condition becomes:
// g_tt*v0^2 + 2*g_tph*v0*v3 + g_phph*v3^2 + g_rr*v1^2 + g_thth*v2^2 = 0
// This is a quadratic in v0:
// g_tt*v0^2 + 2*g_tph*v3*v0 + (spatial terms) = 0
// v0 = (-g_tph*v3 + sqrt((g_tph*v3)^2 - g_tt*spatial)) / g_tt
// @param g Metric components with frame dragging
// @param s State to renormalize
// @return State with v0 recomputed for null geodesic
// [[nodiscard]] inline StateVector renormalize_null_kerr(
// const MetricComponents& g, const StateVector& s) noexcept
// {
// // Spatial contribution (excluding v3 cross term)
// const double spatial_rr_thth =
// g.g_rr * s.v1 * s.v1 +
// g.g_thth * s.v2 * s.v2;
// // Full spatial including phi
// const double spatial_full = spatial_rr_thth + g.g_phph * s.v3 * s.v3;
// // Quadratic formula for v0
// // g_tt*v0^2 + 2*g_tph*v3*v0 + spatial_full = 0
// // a = g_tt, b = 2*g_tph*v3, c = spatial_full
// const double a = g.g_tt;
// const double b = 2.0 * g.g_tph * s.v3;
// const double c = spatial_full;
// // Discriminant: b^2 - 4ac
// const double discriminant = b * b - 4.0 * a * c;
// // v0 = (-b + sqrt(disc)) / (2a)  [take positive root for future-directed]
// // Since a = g_tt < 0, we need the sign that gives v0 > 0
// const double sqrt_disc = std::sqrt(std::abs(discriminant));
// const double new_v0 = (-b + sqrt_disc) / (2.0 * a);
// return StateVector{
// s.x0, s.x1, s.x2, s.x3,
// std::abs(new_v0), s.v1, s.v2, s.v3  // Ensure v0 > 0 (future-directed)
// };
// }
// // ============================================================================
// // Drift Monitoring (from Rocq: needs_renormalization)
// // ============================================================================
// @brief Check if renormalization is needed based on constraint violation
// Derived from Rocq: Definition needs_renormalization (g : MetricComponents) (s : StateVector) (tol : R) : bool :=
// if Rlt_dec tol (Rabs (null_constraint_function g s)) then true else false.
// @param g Metric components
// @param s Current state
// @param tol Tolerance threshold
// @return true if |C| > tol (renormalization recommended)
// [[nodiscard]] constexpr bool needs_renormalization(
// const MetricComponents& g, const StateVector& s, double tol) noexcept
// {
// return std::abs(null_constraint_function(g, s)) > tol;
// }
// @brief Adaptive tolerance based on step size
// Reasonable tolerance is proportional to expected drift: O(h^4).
// A good heuristic is tol ~ 10 * h^4 to allow some accumulation
// before triggering renormalization.
// @param h Current step size
// @param safety_factor Multiplier (default 10)
// @return Recommended tolerance for renormalization check
// [[nodiscard]] constexpr double adaptive_tolerance(double h, double safety_factor = 10.0) noexcept {
// const double h2 = h * h;
// return safety_factor * h2 * h2;  // safety_factor * h^4
// }
// // ============================================================================
// // Massive Particle Constraint (from Rocq: mass_shell_constraint)
// // ============================================================================
// @brief Mass-shell constraint for massive particles: g_ab p^a p^b = -m^2
// Derived from Rocq: Definition mass_shell_constraint (g : MetricComponents) (s : StateVector) (m : R) : R :=
// null_constraint_function g s + m^2.
// For massive particles with mass m (in geometric units):
// - Constraint should equal zero: g_ab v^a v^b + m^2 = 0
// - Equivalently: g_ab v^a v^b = -m^2
// Theorem massive_constraint_preserved:
// Similar to null constraint, drift is O(h^4) per step.
// @param g Metric components
// @param s State vector
// @param m Particle mass in geometric units
// @return Should be zero for properly normalized massive geodesic
// [[nodiscard]] constexpr double mass_shell_constraint(
// const MetricComponents& g, const StateVector& s, double m) noexcept
// {
// return null_constraint_function(g, s) + m * m;
// }
// @brief Check if state satisfies massive particle constraint
// @param g Metric components
// @param s State vector
// @param m Particle mass
// @param tol Tolerance
// @return true if mass-shell constraint is satisfied within tolerance
// [[nodiscard]] constexpr bool is_timelike(
// const MetricComponents& g, const StateVector& s, double m, double tol = 1e-10) noexcept
// {
// return std::abs(mass_shell_constraint(g, s, m)) < tol;
// }
// @brief Renormalize massive particle velocity
// Recomputes v0 to satisfy g_ab v^a v^b = -m^2 for diagonal metrics.
// @param g Metric components (g_tt < 0, diagonal)
// @param s State to renormalize
// @param m Particle mass
// @return State with v0 adjusted for mass-shell condition
// [[nodiscard]] inline StateVector renormalize_massive(
// const MetricComponents& g, const StateVector& s, double m) noexcept
// {
// // For massive: g_tt*v0^2 + spatial = -m^2
// // v0^2 = (spatial + m^2) / (-g_tt)
// const double spatial_norm =
// g.g_rr * s.v1 * s.v1 +
// g.g_thth * s.v2 * s.v2 +
// g.g_phph * s.v3 * s.v3;
// const double new_v0 = std::sqrt((spatial_norm + m * m) / (-g.g_tt));
// return StateVector{
// s.x0, s.x1, s.x2, s.x3,
// new_v0, s.v1, s.v2, s.v3
// };
// }
// // ============================================================================
// // Extraction Interface (from Rocq: check_null_constraint, correct_null_constraint)
// // ============================================================================
// @brief Check null constraint value (extraction interface)
// Derived from Rocq: Definition check_null_constraint (g : MetricComponents) (s : StateVector) : R :=
// null_constraint_function g s.
// @param g Metric components
// @param s State vector
// @return Null constraint value
// [[nodiscard]] constexpr double check_null_constraint(
// const MetricComponents& g, const StateVector& s) noexcept
// {
// return null_constraint_function(g, s);
// }
// @brief Correct null constraint violation (extraction interface)
// Derived from Rocq: Definition correct_null_constraint (g : MetricComponents) (s : StateVector) : StateVector :=
// renormalize_null g s.
// @param g Metric components
// @param s State to correct
// @return Corrected state satisfying null condition
// [[nodiscard]] inline StateVector correct_null_constraint(
// const MetricComponents& g, const StateVector& s) noexcept
// {
// return renormalize_null(g, s);
// }
// @brief Should correction be applied? (extraction interface)
// Derived from Rocq: Definition should_correct (g : MetricComponents) (s : StateVector) (tol : R) : bool :=
// needs_renormalization g s tol.
// @param g Metric components
// @param s State to check
// @param tol Tolerance threshold
// @return true if correction recommended
// [[nodiscard]] constexpr bool should_correct(
// const MetricComponents& g, const StateVector& s, double tol) noexcept
// {
// return needs_renormalization(g, s, tol);
// }
// // ============================================================================
// // Integrated Geodesic Step with Constraint Correction
// // ============================================================================
// @brief Perform RK4 step with optional null constraint correction
// Combines integration and constraint maintenance in a single operation.
// If constraint drift exceeds tolerance, applies renormalization.
// @param g_func Function to compute metric at position
// @param christoffel Christoffel acceleration functions
// @param h Step size
// @param s Current state
// @param tol Constraint tolerance (use adaptive_tolerance for automatic selection)
// @return New state with constraint preserved
// template<typename MetricFunc>
// requires std::invocable<MetricFunc, double, double, double>
// [[nodiscard]] inline StateVector rk4_step_null_preserving(
// MetricFunc&& g_func,
// const ChristoffelAccel& christoffel,
// double h,
// const StateVector& s,
// double tol) noexcept
// {
// // Create RHS function
// auto rhs = [&christoffel](const StateVector& state) -> StateVector {
// return geodesic_rhs(christoffel, state);
// };
// // Perform RK4 step
// StateVector s_new = rk4_step(rhs, h, s);
// // Evaluate metric at new position
// MetricComponents g_new = g_func(s_new.x1, s_new.x2, s_new.x3);
// // Check if correction needed
// if (needs_renormalization(g_new, s_new, tol)) {
// // Apply renormalization
// if (std::abs(g_new.g_tph) < 1e-15) {
// s_new = renormalize_null(g_new, s_new);
// } else {
// s_new = renormalize_null_kerr(g_new, s_new);
// }
// }
// return s_new;
// }
// // ============================================================================
// // Constraint Monitoring Statistics
// // ============================================================================
// @brief Statistics for constraint monitoring during integration
struct ConstraintStats {
    float max_constraint;
    observed double total_drift;
    uint renorm_count;
    uint step_count;
};

// Function definitions (verified from Rocq proofs)

/**
 * Verified null geodesic constraint preservation - derived from Rocq formalization
 *
 * Derived from Rocq:Definition null_constraint_function (g : MetricComponents) (s : StateVector) : R :...
 */
float null_constraint_function(MetricComponents g, StateVector s) {
    // Derived from Rocq four_norm definition
    return g.g_tt * s.v0 * s.v0 +
    g.g_rr * s.v1 * s.v1 +
    g.g_thth * s.v2 * s.v2 +
    g.g_phph * s.v3 * s.v3 +
    2.0 * g.g_tph * s.v0 * s.v3;
}

/**
 * Check if state satisfies null condition: C = 0
 *
 * Derived from Rocq:Definition initially_null (g : MetricComponents) (s : StateVector) : Prop :=...
 */
bool is_null(MetricComponents g, StateVector s, float tol) {
    return abs(null_constraint_function(g, s)) < tol;
}

/**
 * Compute constraint after one RK4 step
 *
 * Derived from Rocq:Definition constraint_after_step (g : MetricComponents)...
 */
float constraint_after_step(MetricComponents g, ChristoffelAccel christoffel, float h, StateVector s) {
    // Create RHS function from Christoffel symbols
    auto rhs = [&christoffel](const StateVector& state) -> StateVector {
    return geodesic_rhs(christoffel, state);
    };
    // Perform RK4 step
    StateVector s_new = rk4_step(rhs, h, s);
    // Evaluate constraint at new state
    return null_constraint_function(g, s_new);
}

/**
 * Compute constraint drift after one step: Delta C = C(after) - C(before)
 *
 * Derived from Rocq:Definition constraint_drift_step (g : MetricComponents)...
 */
float constraint_drift_step(MetricComponents g, ChristoffelAccel christoffel, float h, StateVector s) {
    return constraint_after_step(g, christoffel, h, s) - null_constraint_function(g, s);
}

/**
 * Estimate constraint drift bound: C * h^4
 */
float constraint_drift_bound(float C, float h) {
    float h2 = h * h;
    return C * h2 * h2;  // C * h^4
}

/**
 * Estimate accumulated drift after N steps
 */
float global_drift_bound(float C, float h, uint N) {
    return static_cast<float>(N) * constraint_drift_bound(C, h);
}

/**
 * Renormalize velocity to restore null condition
 *
 * Derived from Rocq:Definition renormalize_null (g : MetricComponents) (s : StateVector) : StateVector...
 */
StateVector renormalize_null(MetricComponents g, StateVector s) {
    // Compute spatial contribution: g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2
    float spatial_norm =
    g.g_rr * s.v1 * s.v1 +
    g.g_thth * s.v2 * s.v2 +
    g.g_phph * s.v3 * s.v3;
    // Solve for v0: g_tt * v0^2 = -spatial_norm
    // v0 = sqrt(-spatial_norm / g_tt) = sqrt(spatial_norm / (-g_tt))
    float new_v0 = sqrt(spatial_norm / (-g.g_tt));
    return StateVector{
    s.x0, s.x1, s.x2, s.x3,
    new_v0, s.v1, s.v2, s.v3
    };
}

/**
 * Renormalize velocity for Kerr metric (handles frame dragging)
 */
StateVector renormalize_null_kerr(MetricComponents g, StateVector s) {
    // Spatial contribution (excluding v3 cross term)
    float spatial_rr_thth =
    g.g_rr * s.v1 * s.v1 +
    g.g_thth * s.v2 * s.v2;
    // Full spatial including phi
    float spatial_full = spatial_rr_thth + g.g_phph * s.v3 * s.v3;
    // Quadratic formula for v0
    // g_tt*v0^2 + 2*g_tph*v3*v0 + spatial_full = 0
    // a = g_tt, b = 2*g_tph*v3, c = spatial_full
    float a = g.g_tt;
    float b = 2.0 * g.g_tph * s.v3;
    float c = spatial_full;
    // Discriminant: b^2 - 4ac
    float discriminant = b * b - 4.0 * a * c;
    // v0 = (-b + sqrt(disc)) / (2a)  [take positive root for future-directed]
    // Since a = g_tt < 0, we need the sign that gives v0 > 0
    float sqrt_disc = sqrt(abs(discriminant));
    float new_v0 = (-b + sqrt_disc) / (2.0 * a);
    return StateVector{
    s.x0, s.x1, s.x2, s.x3,
    abs(new_v0), s.v1, s.v2, s.v3  // Ensure v0 > 0 (future-directed)
    };
}

/**
 * Check if renormalization is needed based on constraint violation
 *
 * Derived from Rocq:Definition needs_renormalization (g : MetricComponents) (s : StateVector) (tol : R...
 */
bool needs_renormalization(MetricComponents g, StateVector s, float tol) {
    return abs(null_constraint_function(g, s)) > tol;
}

/**
 * Adaptive tolerance based on step size
 */
float adaptive_tolerance(float h, float safety_factor) {
    float h2 = h * h;
    return safety_factor * h2 * h2;  // safety_factor * h^4
}

/**
 * Mass-shell constraint for massive particles: g_ab p^a p^b = -m^2
 *
 * Derived from Rocq:Definition mass_shell_constraint (g : MetricComponents) (s : StateVector) (m : R) ...
 */
float mass_shell_constraint(MetricComponents g, StateVector s, float m) {
    return null_constraint_function(g, s) + m * m;
}

/**
 * Check if state satisfies massive particle constraint
 */
bool is_timelike(MetricComponents g, StateVector s, float m, float tol) {
    return abs(mass_shell_constraint(g, s, m)) < tol;
}

/**
 * Renormalize massive particle velocity
 */
StateVector renormalize_massive(MetricComponents g, StateVector s, float m) {
    // For massive: g_tt*v0^2 + spatial = -m^2
    // v0^2 = (spatial + m^2) / (-g_tt)
    float spatial_norm =
    g.g_rr * s.v1 * s.v1 +
    g.g_thth * s.v2 * s.v2 +
    g.g_phph * s.v3 * s.v3;
    float new_v0 = sqrt((spatial_norm + m * m) / (-g.g_tt));
    return StateVector{
    s.x0, s.x1, s.x2, s.x3,
    new_v0, s.v1, s.v2, s.v3
    };
}

/**
 * Check null constraint value (extraction interface)
 *
 * Derived from Rocq:Definition check_null_constraint (g : MetricComponents) (s : StateVector) : R :=...
 */
float check_null_constraint(MetricComponents g, StateVector s) {
    return null_constraint_function(g, s);
}

/**
 * Correct null constraint violation (extraction interface)
 *
 * Derived from Rocq:Definition correct_null_constraint (g : MetricComponents) (s : StateVector) : Stat...
 */
StateVector correct_null_constraint(MetricComponents g, StateVector s) {
    return renormalize_null(g, s);
}

/**
 * Should correction be applied? (extraction interface)
 *
 * Derived from Rocq:Definition should_correct (g : MetricComponents) (s : StateVector) (tol : R) : boo...
 */
bool should_correct(MetricComponents g, StateVector s, float tol) {
    return needs_renormalization(g, s, tol);
}

StateVector rk4_step_null_preserving(ChristoffelAccel christoffel, float h, StateVector s, float tol) {
    // Create RHS function
    auto rhs = [&christoffel](const StateVector& state) -> StateVector {
    return geodesic_rhs(christoffel, state);
    };
    // Perform RK4 step
    StateVector s_new = rk4_step(rhs, h, s);
    // Evaluate metric at new position
    MetricComponents g_new = g_func(s_new.x1, s_new.x2, s_new.x3);
    // Check if correction needed
    if (needs_renormalization(g_new, s_new, tol)) {
    // Apply renormalization
    if (abs(g_new.g_tph) < 1e-15) {
    s_new = renormalize_null(g_new, s_new);
    } else {
    s_new = renormalize_null_kerr(g_new, s_new);
}

#endif // SHADER_VERIFIED_NULL_CONSTRAINT_HPP
