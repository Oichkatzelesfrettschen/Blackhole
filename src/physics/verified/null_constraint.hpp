/**
 * @file verified/null_constraint.hpp
 * @brief Verified null geodesic constraint preservation - derived from Rocq formalization
 *
 * Maintained C++ reference for rocq/theories/Geodesics/NullConstraint.v
 *
 * Key result: For RK4 integration of geodesics derived from a Lorentzian metric,
 * the null constraint drift is O(h^4) per step.
 *
 * Null geodesic constraint: g_ab v^a v^b = 0
 * For light rays, this condition must be preserved during numerical integration.
 *
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
 *
 * @note All functions are constexpr/inline for performance
 * @note Uses geometric units where c = G = 1
 */

#ifndef PHYSICS_VERIFIED_NULL_CONSTRAINT_HPP
#define PHYSICS_VERIFIED_NULL_CONSTRAINT_HPP

#include <cmath>
#include <functional>
#include <utility>

#include "geodesic.hpp"
#include "rk4.hpp"

namespace verified {

// ============================================================================
// Null Constraint Function (from Rocq: null_constraint_function)
// ============================================================================

/**
 * @brief Compute null constraint: C(x,v) = g_ab(x) v^a v^b
 *
 * Derived from Rocq: Definition null_constraint_function (g : MetricComponents) (s : StateVector) : R :=
 *   let v := mkFV s.(v0) s.(v1) s.(v2) s.(v3) in
 *   four_norm g v.
 *
 * For null geodesics, this should equal zero.
 * For timelike geodesics, this equals -1 (with proper normalization).
 *
 * @param g Metric components at current position
 * @param s State vector containing position and velocity
 * @return C = g_tt*v0^2 + g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2 + 2*g_tph*v0*v3
 */
[[nodiscard]] constexpr double nullConstraintFunction(const MetricComponents &g,
                                                      const StateVector &s) noexcept {
  // Derived from Rocq four_norm definition
  return g.gTt * s.v0 * s.v0 + g.gRr * s.v1 * s.v1 + g.gThth * s.v2 * s.v2 + g.gPhph * s.v3 * s.v3 +
         2.0 * g.gTph * s.v0 * s.v3;
}

/**
 * @brief Check if state satisfies null condition: C = 0
 *
 * Derived from Rocq: Definition initially_null (g : MetricComponents) (s : StateVector) : Prop :=
 *   null_constraint_function g s = 0.
 *
 * @param g Metric components
 * @param s State vector
 * @param tol Tolerance for comparison to zero
 * @return true if |C| < tol
 */
#ifndef VERIFIED_IS_NULL_ALREADY_DEFINED
[[nodiscard]] constexpr bool isNull(const MetricComponents &g, const StateVector &s,
                                    double tol = 1e-10) noexcept {
  return std::abs(nullConstraintFunction(g, s)) < tol;
}
#endif // VERIFIED_IS_NULL_ALREADY_DEFINED

// ============================================================================
// Constraint After Integration Step (from Rocq: constraint_after_step)
// ============================================================================

/**
 * @brief Compute constraint after one RK4 step
 *
 * Derived from Rocq: Definition constraint_after_step (g : MetricComponents)
 *   (christoffel : ChristoffelAccel) (h : R) (s : StateVector) : R :=
 *   let s' := rk4_step (geodesic_rhs christoffel) h s in
 *   null_constraint_function g s'.
 *
 * @param g Metric components (evaluated at new position)
 * @param christoffel Christoffel acceleration functions
 * @param h Step size
 * @param s Initial state
 * @return Null constraint value after step
 */
[[nodiscard]] inline double constraintAfterStep(const MetricComponents &g,
                                                const ChristoffelAccel &christoffel, double h,
                                                const StateVector &s) noexcept {
  // Create RHS function from Christoffel symbols
  auto rhs = [&christoffel](const StateVector &state) -> StateVector {
    return geodesicRhs(christoffel, state);
  };

  // Perform RK4 step
  StateVector const sNew = rk4Step(rhs, h, s);

  // Evaluate constraint at new state
  return nullConstraintFunction(g, sNew);
}

// ============================================================================
// Constraint Drift Analysis (from Rocq: constraint_drift_step)
// ============================================================================

/**
 * @brief Compute constraint drift after one step: Delta C = C(after) - C(before)
 *
 * Derived from Rocq: Definition constraint_drift_step (g : MetricComponents)
 *   (christoffel : ChristoffelAccel) (h : R) (s : StateVector) : R :=
 *   constraint_after_step g christoffel h s - null_constraint_function g s.
 *
 * Theorem null_constraint_drift_bound:
 *   |Delta C| <= O(h^4) per step for RK4 integration.
 *
 * @param g Metric components
 * @param christoffel Christoffel acceleration functions
 * @param h Step size
 * @param s Initial state
 * @return Constraint drift (ideally near zero)
 */
[[nodiscard]] inline double constraintDriftStep(const MetricComponents &g,
                                                const ChristoffelAccel &christoffel, double h,
                                                const StateVector &s) noexcept {
  return constraintAfterStep(g, christoffel, h, s) - nullConstraintFunction(g, s);
}

/**
 * @brief Estimate constraint drift bound: C * h^4
 *
 * From Rocq theorem null_constraint_drift_bound:
 * The RK4 local truncation error is O(h^5) for position/velocity,
 * but the constraint (quadratic in velocity) accumulates error as O(h^4).
 *
 * @param c Bound constant (problem-dependent)
 * @param h Step size
 * @return Estimated maximum drift per step
 */
[[nodiscard]] constexpr double constraintDriftBound(double c, double h) noexcept {
  const double h2 = h * h;
  return c * h2 * h2; // C * h^4
}

// ============================================================================
// Global Drift Accumulation (from Rocq: null_constraint_global_drift)
// ============================================================================

/**
 * @brief Estimate accumulated drift after N steps
 *
 * From Rocq theorem null_constraint_global_drift:
 * After N steps with step size h, total drift is bounded by N * C * h^4.
 *
 * For integration over total affine parameter Lambda = N * h:
 * Total drift ~ (Lambda / h) * C * h^4 = C * Lambda * h^3
 *
 * This decreases as h decreases, confirming convergence.
 *
 * @param c Bound constant
 * @param h Step size
 * @param n Number of steps
 * @return Estimated accumulated drift bound
 */
[[nodiscard]] constexpr double globalDriftBound(double c, double h, std::size_t n) noexcept {
  return static_cast<double>(n) * constraintDriftBound(c, h);
}

// ============================================================================
// Renormalization Functions (from Rocq: renormalize_null)
// ============================================================================

/**
 * @brief Renormalize velocity to restore null condition
 *
 * Derived from Rocq: Definition renormalize_null (g : MetricComponents) (s : StateVector) : StateVector :=
 *   let new_v0 := sqrt ((g.(g_rr) * s.(v1)^2 + g.(g_thth) * s.(v2)^2 +
 *                        g.(g_phph) * s.(v3)^2) / (-g.(g_tt))) in
 *   mkSV s.(x0) s.(x1) s.(x2) s.(x3) new_v0 s.(v1) s.(v2) s.(v3).
 *
 * This recomputes v0 (time component) from spatial velocity components
 * to exactly satisfy g_tt*v0^2 + g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2 = 0.
 *
 * Note: This assumes diagonal metric (g_tph = 0). For Kerr, use renormalize_null_kerr.
 *
 * Theorem renormalization_restores_null:
 *   is_lorentzian g -> (v1 != 0 || v2 != 0 || v3 != 0) ->
 *   initially_null g (renormalize_null g s).
 *
 * @param g Metric components (must have g_tt < 0)
 * @param s State to renormalize
 * @return State with v0 recomputed to satisfy null condition
 */
[[nodiscard]] inline StateVector renormalizeNull(const MetricComponents &g,
                                                 const StateVector &s) noexcept {
  // Compute spatial contribution: g_rr*v1^2 + g_thth*v2^2 + g_phph*v3^2
  const double spatialNorm = g.gRr * s.v1 * s.v1 + g.gThth * s.v2 * s.v2 + g.gPhph * s.v3 * s.v3;

  // Solve for v0: g_tt * v0^2 = -spatial_norm
  // v0 = sqrt(-spatial_norm / g_tt) = sqrt(spatial_norm / (-g_tt))
  const double newV0 = std::sqrt(spatialNorm / (-g.gTt));

  return StateVector{s.x0, s.x1, s.x2, s.x3, newV0, s.v1, s.v2, s.v3};
}

/**
 * @brief Renormalize velocity for Kerr metric (handles frame dragging)
 *
 * For Kerr metric with g_tph != 0, the null condition becomes:
 * g_tt*v0^2 + 2*g_tph*v0*v3 + g_phph*v3^2 + g_rr*v1^2 + g_thth*v2^2 = 0
 *
 * This is a quadratic in v0:
 * g_tt*v0^2 + 2*g_tph*v3*v0 + (spatial terms) = 0
 * v0 = (-g_tph*v3 + sqrt((g_tph*v3)^2 - g_tt*spatial)) / g_tt
 *
 * @param g Metric components with frame dragging
 * @param s State to renormalize
 * @return State with v0 recomputed for null geodesic
 */
[[nodiscard]] inline StateVector renormalizeNullKerr(const MetricComponents &g,
                                                     const StateVector &s) noexcept {
  // Spatial contribution (excluding v3 cross term)
  const double spatialRrThth = g.gRr * s.v1 * s.v1 + g.gThth * s.v2 * s.v2;

  // Full spatial including phi
  const double spatialFull = spatialRrThth + g.gPhph * s.v3 * s.v3;

  // Quadratic formula for v0
  // g_tt*v0^2 + 2*g_tph*v3*v0 + spatial_full = 0
  // a = g_tt, b = 2*g_tph*v3, c = spatial_full
  const double a = g.gTt;
  const double b = 2.0 * g.gTph * s.v3;
  const double c = spatialFull;

  // Discriminant: b^2 - 4ac
  const double discriminant = b * b - 4.0 * a * c;

  // v0 = (-b + sqrt(disc)) / (2a)  [take positive root for future-directed]
  // Since a = g_tt < 0, we need the sign that gives v0 > 0
  const double sqrtDisc = std::sqrt(std::abs(discriminant));
  const double newV0 = (-b + sqrtDisc) / (2.0 * a);

  return StateVector{
      s.x0, s.x1, s.x2, s.x3, std::abs(newV0), s.v1, s.v2, s.v3 // Ensure v0 > 0 (future-directed)
  };
}

// ============================================================================
// Drift Monitoring (from Rocq: needs_renormalization)
// ============================================================================

/**
 * @brief Check if renormalization is needed based on constraint violation
 *
 * Derived from Rocq: Definition needs_renormalization (g : MetricComponents) (s : StateVector) (tol : R) : bool :=
 *   if Rlt_dec tol (Rabs (null_constraint_function g s)) then true else false.
 *
 * @param g Metric components
 * @param s Current state
 * @param tol Tolerance threshold
 * @return true if |C| > tol (renormalization recommended)
 */
[[nodiscard]] constexpr bool needsRenormalization(const MetricComponents &g, const StateVector &s,
                                                  double tol) noexcept {
  return std::abs(nullConstraintFunction(g, s)) > tol;
}

/**
 * @brief Adaptive tolerance based on step size
 *
 * Reasonable tolerance is proportional to expected drift: O(h^4).
 * A good heuristic is tol ~ 10 * h^4 to allow some accumulation
 * before triggering renormalization.
 *
 * @param h Current step size
 * @param safetyFactor Multiplier (default 10)
 * @return Recommended tolerance for renormalization check
 */
[[nodiscard]] constexpr double adaptiveTolerance(double h, double safetyFactor = 10.0) noexcept {
  const double h2 = h * h;
  return safetyFactor * h2 * h2; // safety_factor * h^4
}

// ============================================================================
// Massive Particle Constraint (from Rocq: mass_shell_constraint)
// ============================================================================

/**
 * @brief Mass-shell constraint for massive particles: g_ab p^a p^b = -m^2
 *
 * Derived from Rocq: Definition mass_shell_constraint (g : MetricComponents) (s : StateVector) (m : R) : R :=
 *   null_constraint_function g s + m^2.
 *
 * For massive particles with mass m (in geometric units):
 * - Constraint should equal zero: g_ab v^a v^b + m^2 = 0
 * - Equivalently: g_ab v^a v^b = -m^2
 *
 * Theorem massive_constraint_preserved:
 *   Similar to null constraint, drift is O(h^4) per step.
 *
 * @param g Metric components
 * @param s State vector
 * @param m Particle mass in geometric units
 * @return Should be zero for properly normalized massive geodesic
 */
[[nodiscard]] constexpr double massShellConstraint(const MetricComponents &g, const StateVector &s,
                                                   double m) noexcept {
  return nullConstraintFunction(g, s) + m * m;
}

/**
 * @brief Check if state satisfies massive particle constraint
 *
 * @param g Metric components
 * @param s State vector
 * @param m Particle mass
 * @param tol Tolerance
 * @return true if mass-shell constraint is satisfied within tolerance
 */
[[nodiscard]] constexpr bool isTimelike(const MetricComponents &g, const StateVector &s, double m,
                                        double tol = 1e-10) noexcept {
  return std::abs(massShellConstraint(g, s, m)) < tol;
}

/**
 * @brief Renormalize massive particle velocity
 *
 * Recomputes v0 to satisfy g_ab v^a v^b = -m^2 for diagonal metrics.
 *
 * @param g Metric components (g_tt < 0, diagonal)
 * @param s State to renormalize
 * @param m Particle mass
 * @return State with v0 adjusted for mass-shell condition
 */
[[nodiscard]] inline StateVector renormalizeMassive(const MetricComponents &g, const StateVector &s,
                                                    double m) noexcept {
  // For massive: g_tt*v0^2 + spatial = -m^2
  // v0^2 = (spatial + m^2) / (-g_tt)
  const double spatialNorm = g.gRr * s.v1 * s.v1 + g.gThth * s.v2 * s.v2 + g.gPhph * s.v3 * s.v3;

  const double newV0 = std::sqrt((spatialNorm + m * m) / (-g.gTt));

  return StateVector{s.x0, s.x1, s.x2, s.x3, newV0, s.v1, s.v2, s.v3};
}

// ============================================================================
// Extraction Interface (from Rocq: check_null_constraint, correct_null_constraint)
// ============================================================================

/**
 * @brief Check null constraint value (extraction interface)
 *
 * Derived from Rocq: Definition check_null_constraint (g : MetricComponents) (s : StateVector) : R :=
 *   null_constraint_function g s.
 *
 * @param g Metric components
 * @param s State vector
 * @return Null constraint value
 */
[[nodiscard]] constexpr double checkNullConstraint(const MetricComponents &g,
                                                   const StateVector &s) noexcept {
  return nullConstraintFunction(g, s);
}

/**
 * @brief Correct null constraint violation (extraction interface)
 *
 * Derived from Rocq: Definition correct_null_constraint (g : MetricComponents) (s : StateVector) : StateVector :=
 *   renormalize_null g s.
 *
 * @param g Metric components
 * @param s State to correct
 * @return Corrected state satisfying null condition
 */
[[nodiscard]] inline StateVector correctNullConstraint(const MetricComponents &g,
                                                       const StateVector &s) noexcept {
  return renormalizeNull(g, s);
}

/**
 * @brief Should correction be applied? (extraction interface)
 *
 * Derived from Rocq: Definition should_correct (g : MetricComponents) (s : StateVector) (tol : R) : bool :=
 *   needs_renormalization g s tol.
 *
 * @param g Metric components
 * @param s State to check
 * @param tol Tolerance threshold
 * @return true if correction recommended
 */
[[nodiscard]] constexpr bool shouldCorrect(const MetricComponents &g, const StateVector &s,
                                           double tol) noexcept {
  return needsRenormalization(g, s, tol);
}

// ============================================================================
// Integrated Geodesic Step with Constraint Correction
// ============================================================================

/**
 * @brief Perform RK4 step with optional null constraint correction
 *
 * Combines integration and constraint maintenance in a single operation.
 * If constraint drift exceeds tolerance, applies renormalization.
 *
 * @param gFunc Function to compute metric at position
 * @param christoffel Christoffel acceleration functions
 * @param h Step size
 * @param s Current state
 * @param tol Constraint tolerance (use adaptive_tolerance for automatic selection)
 * @return New state with constraint preserved
 */
template <typename MetricFunc>
requires std::invocable<MetricFunc &, double, double, double> [[nodiscard]] inline StateVector
rk4StepNullPreserving(MetricFunc &&gFunc, const ChristoffelAccel &christoffel, double h,
                      const StateVector &s, double tol) noexcept {
  // Named references preserve repeated lvalue invocation of stateful callbacks.
  auto &&metricFunction = std::forward<MetricFunc>(gFunc);
  // Create RHS function
  auto rhs = [&christoffel](const StateVector &state) -> StateVector {
    return geodesicRhs(christoffel, state);
  };

  // Perform RK4 step
  StateVector sNew = rk4Step(rhs, h, s);

  // Evaluate metric at new position
  const MetricComponents gNew = metricFunction(sNew.x1, sNew.x2, sNew.x3);

  // Check if correction needed
  if (needsRenormalization(gNew, sNew, tol)) {
    // Apply renormalization
    if (std::abs(gNew.gTph) < 1e-15) {
      sNew = renormalizeNull(gNew, sNew);
    } else {
      sNew = renormalizeNullKerr(gNew, sNew);
    }
  }

  return sNew;
}

// ============================================================================
// Constraint Monitoring Statistics
// ============================================================================

/**
 * @brief Statistics for constraint monitoring during integration
 */
struct ConstraintStats {
  double maxConstraint{0.0};  ///< Maximum |C| observed
  double totalDrift{0.0};     ///< Accumulated drift
  std::size_t renormCount{0}; ///< Number of renormalizations applied
  std::size_t stepCount{0};   ///< Total integration steps

  constexpr ConstraintStats() noexcept = default;

  /**
   * @brief Update statistics after a step
   * @param constraint Current constraint value
   * @param renormalized Whether renormalization was applied
   */
  constexpr void update(double constraint, bool renormalized) noexcept {
    const double absC = std::abs(constraint);
    if (absC > maxConstraint) {
      maxConstraint = absC;
    }
    totalDrift += absC;
    if (renormalized) {
      ++renormCount;
    }
    ++stepCount;
  }

    /**
     * @brief Average constraint violation per step
     */
    [[nodiscard]] constexpr double averageConstraint() const noexcept {
      return stepCount > 0 ? totalDrift / static_cast<double>(stepCount) : 0.0;
    }

    /**
     * @brief Renormalization frequency
     */
    [[nodiscard]] constexpr double renormFrequency() const noexcept {
      return stepCount > 0 ? static_cast<double>(renormCount) / static_cast<double>(stepCount)
                           : 0.0;
    }
};

} // namespace verified

#endif // PHYSICS_VERIFIED_NULL_CONSTRAINT_HPP
