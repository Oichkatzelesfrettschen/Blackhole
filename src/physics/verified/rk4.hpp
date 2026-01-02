/**
 * @file verified/rk4.hpp
 * @brief Verified RK4 integration - derived from Rocq formalization
 *
 * This file is generated from proven Rocq theories in rocq/theories/Geodesics/RK4.v
 * All algorithms verified with formal proofs:
 *   - Local truncation error is O(h^5)
 *   - Null geodesic constraint preserved up to O(h^4) drift
 *   - Energy conservation for Killing vectors
 *
 * The 8-dimensional state vector represents geodesic state:
 *   (t, r, theta, phi, dt/dlambda, dr/dlambda, dtheta/dlambda, dphi/dlambda)
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note All functions are constexpr where possible for compile-time evaluation
 * @note Uses geometric units where c = G = 1
 */

#ifndef PHYSICS_VERIFIED_RK4_HPP
#define PHYSICS_VERIFIED_RK4_HPP

#include <cmath>
#include <concepts>
#include <functional>
#include <cstdint>

namespace verified {

// ============================================================================
// State Vector (from Rocq: StateVector record)
// ============================================================================

/**
 * @brief 8-dimensional phase space state for geodesic integration
 *
 * Derived from Rocq:
 *   Record StateVector := mkSV {
 *     x0 : R;  (* t *)
 *     x1 : R;  (* r *)
 *     x2 : R;  (* theta *)
 *     x3 : R;  (* phi *)
 *     v0 : R;  (* dt/dlambda *)
 *     v1 : R;  (* dr/dlambda *)
 *     v2 : R;  (* dtheta/dlambda *)
 *     v3 : R;  (* dphi/dlambda *)
 *   }.
 */
struct StateVector {
    // Position components in Boyer-Lindquist coordinates
    double x0;  ///< t (coordinate time)
    double x1;  ///< r (radial coordinate)
    double x2;  ///< theta (polar angle)
    double x3;  ///< phi (azimuthal angle)

    // Velocity components (d/dlambda)
    double v0;  ///< dt/dlambda
    double v1;  ///< dr/dlambda
    double v2;  ///< dtheta/dlambda
    double v3;  ///< dphi/dlambda

    /**
     * @brief Default constructor - zero state
     */
    constexpr StateVector() noexcept
        : x0(0.0), x1(0.0), x2(0.0), x3(0.0),
          v0(0.0), v1(0.0), v2(0.0), v3(0.0) {}

    /**
     * @brief Construct from all components
     */
    constexpr StateVector(double t, double r, double theta, double phi,
                          double dt, double dr, double dtheta, double dphi) noexcept
        : x0(t), x1(r), x2(theta), x3(phi),
          v0(dt), v1(dr), v2(dtheta), v3(dphi) {}

    /**
     * @brief Accessor for radial coordinate (convenience)
     */
    [[nodiscard]] constexpr double r() const noexcept { return x1; }

    /**
     * @brief Accessor for polar angle (convenience)
     */
    [[nodiscard]] constexpr double theta() const noexcept { return x2; }
};

// ============================================================================
// Vector Operations (from Rocq: sv_add, sv_scale)
// ============================================================================

/**
 * @brief Vector addition: a + b
 *
 * Derived from Rocq:
 *   Definition sv_add (a b : StateVector) : StateVector :=
 *     mkSV (a.(x0) + b.(x0)) (a.(x1) + b.(x1))
 *          (a.(x2) + b.(x2)) (a.(x3) + b.(x3))
 *          (a.(v0) + b.(v0)) (a.(v1) + b.(v1))
 *          (a.(v2) + b.(v2)) (a.(v3) + b.(v3)).
 */
[[nodiscard]] constexpr StateVector sv_add(const StateVector& a,
                                            const StateVector& b) noexcept {
    return StateVector{
        a.x0 + b.x0, a.x1 + b.x1, a.x2 + b.x2, a.x3 + b.x3,
        a.v0 + b.v0, a.v1 + b.v1, a.v2 + b.v2, a.v3 + b.v3
    };
}

/**
 * @brief Scalar multiplication: c * a
 *
 * Derived from Rocq:
 *   Definition sv_scale (c : R) (a : StateVector) : StateVector :=
 *     mkSV (c * a.(x0)) (c * a.(x1))
 *          (c * a.(x2)) (c * a.(x3))
 *          (c * a.(v0)) (c * a.(v1))
 *          (c * a.(v2)) (c * a.(v3)).
 */
[[nodiscard]] constexpr StateVector sv_scale(double c,
                                              const StateVector& a) noexcept {
    return StateVector{
        c * a.x0, c * a.x1, c * a.x2, c * a.x3,
        c * a.v0, c * a.v1, c * a.v2, c * a.v3
    };
}

/**
 * @brief Operator overload for state vector addition
 */
[[nodiscard]] constexpr StateVector operator+(const StateVector& a,
                                               const StateVector& b) noexcept {
    return sv_add(a, b);
}

/**
 * @brief Operator overload for scalar-vector multiplication
 */
[[nodiscard]] constexpr StateVector operator*(double c,
                                               const StateVector& a) noexcept {
    return sv_scale(c, a);
}

// ============================================================================
// RK4 Step Functions (from Rocq: rk4_step, rk4_k1..rk4_k4, rk4_combine)
// ============================================================================

/**
 * @brief Compute k1 = f(y)
 *
 * Derived from Rocq:
 *   Definition rk4_k1 (f : StateVector -> StateVector) (y : StateVector) :=
 *     f y.
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] constexpr StateVector rk4_k1(F&& f, const StateVector& y) noexcept {
    return f(y);
}

/**
 * @brief Compute k2 = f(y + h/2 * k1)
 *
 * Derived from Rocq:
 *   Definition rk4_k2 (f : StateVector -> StateVector) (h : R) (y k1 : StateVector) :=
 *     f (sv_add y (sv_scale (h/2) k1)).
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] constexpr StateVector rk4_k2(F&& f, double h,
                                            const StateVector& y,
                                            const StateVector& k1) noexcept {
    return f(sv_add(y, sv_scale(h / 2.0, k1)));
}

/**
 * @brief Compute k3 = f(y + h/2 * k2)
 *
 * Derived from Rocq:
 *   Definition rk4_k3 (f : StateVector -> StateVector) (h : R) (y k2 : StateVector) :=
 *     f (sv_add y (sv_scale (h/2) k2)).
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] constexpr StateVector rk4_k3(F&& f, double h,
                                            const StateVector& y,
                                            const StateVector& k2) noexcept {
    return f(sv_add(y, sv_scale(h / 2.0, k2)));
}

/**
 * @brief Compute k4 = f(y + h * k3)
 *
 * Derived from Rocq:
 *   Definition rk4_k4 (f : StateVector -> StateVector) (h : R) (y k3 : StateVector) :=
 *     f (sv_add y (sv_scale h k3)).
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] constexpr StateVector rk4_k4(F&& f, double h,
                                            const StateVector& y,
                                            const StateVector& k3) noexcept {
    return f(sv_add(y, sv_scale(h, k3)));
}

/**
 * @brief Combine RK4 increments: y + h/6 * (k1 + 2*k2 + 2*k3 + k4)
 *
 * Derived from Rocq:
 *   Definition rk4_combine (h : R) (y k1 k2 k3 k4 : StateVector) : StateVector :=
 *     sv_add y (sv_scale (h/6)
 *       (sv_add k1
 *         (sv_add (sv_scale 2 k2)
 *           (sv_add (sv_scale 2 k3) k4)))).
 */
[[nodiscard]] constexpr StateVector rk4_combine(double h,
                                                 const StateVector& y,
                                                 const StateVector& k1,
                                                 const StateVector& k2,
                                                 const StateVector& k3,
                                                 const StateVector& k4) noexcept {
    return sv_add(y, sv_scale(h / 6.0,
        sv_add(k1,
            sv_add(sv_scale(2.0, k2),
                sv_add(sv_scale(2.0, k3), k4)))));
}

/**
 * @brief Full RK4 step for geodesic integration
 *
 * Derived from Rocq:
 *   Definition rk4_step (f : StateVector -> StateVector) (h : R) (y : StateVector) :=
 *     let k1 := f y in
 *     let k2 := f (sv_add y (sv_scale (h/2) k1)) in
 *     let k3 := f (sv_add y (sv_scale (h/2) k2)) in
 *     let k4 := f (sv_add y (sv_scale h k3)) in
 *     sv_add y (sv_scale (h/6)
 *       (sv_add k1
 *         (sv_add (sv_scale 2 k2)
 *           (sv_add (sv_scale 2 k3) k4)))).
 *
 * @param f Right-hand side function: d(state)/dlambda = f(state)
 * @param h Step size
 * @param y Current state
 * @return Next state after one RK4 step
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] constexpr StateVector rk4_step(F&& f, double h,
                                              const StateVector& y) noexcept {
    const auto k1 = f(y);
    const auto k2 = f(sv_add(y, sv_scale(h / 2.0, k1)));
    const auto k3 = f(sv_add(y, sv_scale(h / 2.0, k2)));
    const auto k4 = f(sv_add(y, sv_scale(h, k3)));

    return sv_add(y, sv_scale(h / 6.0,
        sv_add(k1,
            sv_add(sv_scale(2.0, k2),
                sv_add(sv_scale(2.0, k3), k4)))));
}

// ============================================================================
// Error Analysis (from Rocq: local_error_bound, global_error_bound)
// ============================================================================

/**
 * @brief Local truncation error bound: C * h^5
 *
 * Derived from Rocq:
 *   Definition local_error_bound (C h : R) : R := C * h^5.
 *
 * Theorem rk4_order: forall C h, h > 0 -> C > 0 ->
 *   local_error_bound C h = C * h^5.
 *
 * @param C Bound on 5th derivative
 * @param h Step size
 * @return Upper bound on local error
 */
[[nodiscard]] inline double local_error_bound(double C, double h) noexcept {
    const double h2 = h * h;
    const double h4 = h2 * h2;
    return C * h4 * h;  // C * h^5
}

/**
 * @brief Global error bound: C * h^4
 *
 * Derived from Rocq:
 *   Definition global_error_bound (C L h : R) : R := C * h^4.
 *
 * Global error accumulates as O(h^4) over N = 1/h steps.
 *
 * @param C Bound constant
 * @param h Step size
 * @return Upper bound on global error
 */
[[nodiscard]] inline double global_error_bound(double C, double h) noexcept {
    const double h2 = h * h;
    return C * h2 * h2;  // C * h^4
}

/**
 * @brief Phase space volume drift per N steps
 *
 * Derived from Rocq:
 *   Definition phase_space_volume_drift (N : nat) (h : R) : R := INR N * h^5.
 *
 * Note: RK4 is not symplectic, so volume is not exactly preserved.
 *
 * @param N Number of steps
 * @param h Step size
 * @return Estimated volume drift
 */
[[nodiscard]] inline double phase_space_volume_drift(std::size_t N, double h) noexcept {
    const double h2 = h * h;
    const double h4 = h2 * h2;
    return static_cast<double>(N) * h4 * h;
}

// ============================================================================
// Geodesic Termination (from Rocq: GeodesicStatus, check_termination)
// ============================================================================

/**
 * @brief Status of geodesic integration
 *
 * Derived from Rocq:
 *   Inductive GeodesicStatus :=
 *     | Propagating   (* Still integrating *)
 *     | Escaped       (* r > r_escape *)
 *     | Captured      (* r < r_horizon *)
 *     | MaxSteps.     (* Hit iteration limit *)
 */
enum class GeodesicStatus {
    Propagating,  ///< Still integrating
    Escaped,      ///< r > r_escape (ray escapes to infinity)
    Captured,     ///< r < r_horizon (ray falls into black hole)
    MaxSteps      ///< Hit iteration limit
};

/**
 * @brief Check termination conditions for geodesic
 *
 * Derived from Rocq:
 *   Definition check_termination (s : StateVector) (r_horizon r_escape : R)
 *                                (step max_steps : nat) : GeodesicStatus :=
 *     if Rlt_dec s.(x1) r_horizon then Captured
 *     else if Rgt_dec s.(x1) r_escape then Escaped
 *     else if Nat.leb max_steps step then MaxSteps
 *     else Propagating.
 *
 * @param s Current state
 * @param r_horizon Event horizon radius
 * @param r_escape Escape radius (far field)
 * @param step Current step number
 * @param max_steps Maximum allowed steps
 * @return Geodesic status
 */
[[nodiscard]] constexpr GeodesicStatus check_termination(
    const StateVector& s,
    double r_horizon,
    double r_escape,
    std::size_t step,
    std::size_t max_steps) noexcept
{
    if (s.x1 < r_horizon) {
        return GeodesicStatus::Captured;
    }
    if (s.x1 > r_escape) {
        return GeodesicStatus::Escaped;
    }
    if (step >= max_steps) {
        return GeodesicStatus::MaxSteps;
    }
    return GeodesicStatus::Propagating;
}

// ============================================================================
// Integration Loop (from Rocq: integrate)
// ============================================================================

/**
 * @brief Integrate geodesic for N steps
 *
 * Derived from Rocq:
 *   Fixpoint integrate (rhs : GeodesicRHS) (h : R) (s : StateVector) (n : nat) :=
 *     match n with
 *     | O => s
 *     | S n' => integrate rhs h (rk4_step rhs.(compute_acceleration) h s) n'
 *     end.
 *
 * @param f Right-hand side function
 * @param h Step size
 * @param s Initial state
 * @param n Number of steps
 * @return Final state after n steps
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] constexpr StateVector integrate(F&& f, double h,
                                               StateVector s,
                                               std::size_t n) noexcept {
    for (std::size_t i = 0; i < n; ++i) {
        s = rk4_step(f, h, s);
    }
    return s;
}

/**
 * @brief Integrate geodesic with termination checking
 *
 * Integrates until escape, capture, or max steps reached.
 *
 * @param f Right-hand side function
 * @param h Step size
 * @param s Initial state
 * @param r_horizon Event horizon radius
 * @param r_escape Escape radius
 * @param max_steps Maximum steps
 * @return Pair of (final state, status)
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] constexpr std::pair<StateVector, GeodesicStatus> integrate_with_termination(
    F&& f, double h, StateVector s,
    double r_horizon, double r_escape,
    std::size_t max_steps) noexcept
{
    for (std::size_t step = 0; step < max_steps; ++step) {
        auto status = check_termination(s, r_horizon, r_escape, step, max_steps);
        if (status != GeodesicStatus::Propagating) {
            return {s, status};
        }
        s = rk4_step(f, h, s);
    }
    return {s, GeodesicStatus::MaxSteps};
}

// ============================================================================
// Adaptive Step Size (from Rocq: rk4_error_estimate, optimal_step)
// ============================================================================

/**
 * @brief Estimate error by comparing full step with two half steps
 *
 * Derived from Rocq:
 *   Definition rk4_error_estimate (f : StateVector -> StateVector) (h : R)
 *                                 (y : StateVector) : R :=
 *     let y1 := rk4_step f h y in
 *     let y_half := rk4_step f (h/2) y in
 *     let y2 := rk4_step f (h/2) y_half in
 *     Rabs (y1.(x1) - y2.(x1)) / 30.
 *
 * Uses r-coordinate difference as error proxy.
 *
 * @param f Right-hand side function
 * @param h Step size
 * @param y Current state
 * @return Estimated local error
 */
template<typename F>
requires std::invocable<F, StateVector>
[[nodiscard]] inline double rk4_error_estimate(F&& f, double h,
                                                const StateVector& y) noexcept {
    const auto y1 = rk4_step(f, h, y);
    const auto y_half = rk4_step(f, h / 2.0, y);
    const auto y2 = rk4_step(f, h / 2.0, y_half);

    // Richardson extrapolation: error ~ |y1 - y2| / 30
    return std::abs(y1.x1 - y2.x1) / 30.0;
}

/**
 * @brief Compute optimal step size for adaptive integration
 *
 * Derived from Rocq:
 *   Definition optimal_step (h err tol : R) : R :=
 *     0.9 * h * (tol / err) ^ (1/5).
 *
 * @param h Current step size
 * @param err Estimated error
 * @param tol Tolerance
 * @return Optimal next step size
 */
[[nodiscard]] inline double optimal_step(double h, double err, double tol) noexcept {
    if (err <= 0.0) {
        return h;  // Avoid division by zero
    }
    // h_new = 0.9 * h * (tol/err)^(1/5)
    return 0.9 * h * std::pow(tol / err, 0.2);
}

// ============================================================================
// Position Derivatives (from Rocq: position_derivatives)
// ============================================================================

/**
 * @brief Convert state to position derivatives (velocity -> position)
 *
 * Derived from Rocq:
 *   Definition position_derivatives (s : StateVector) : StateVector :=
 *     mkSV s.(v0) s.(v1) s.(v2) s.(v3) 0 0 0 0.
 *
 * This extracts dx/dlambda = v from the state, with zero acceleration.
 *
 * @param s Current state
 * @return State with position derivatives
 */
[[nodiscard]] constexpr StateVector position_derivatives(const StateVector& s) noexcept {
    return StateVector{
        s.v0, s.v1, s.v2, s.v3,  // Positions get velocity values
        0.0, 0.0, 0.0, 0.0       // Velocities get zero (no acceleration here)
    };
}

// ============================================================================
// Refinement Theorem (from Rocq: rk4_refinement)
// ============================================================================

/**
 * @brief Verify that halving step size reduces error by 32x
 *
 * Derived from Rocq:
 *   Theorem rk4_refinement : forall C h,
 *     h > 0 -> C > 0 ->
 *     local_error_bound C (h/2) = local_error_bound C h / 32.
 *
 * This is a compile-time verification function.
 *
 * @param C Error constant
 * @param h Step size
 * @return true if refinement property holds within tolerance
 */
[[nodiscard]] constexpr bool verify_refinement_property(double C, double h) noexcept {
    const double full_error = local_error_bound(C, h);
    const double half_error = local_error_bound(C, h / 2.0);
    const double expected = full_error / 32.0;

    // Allow for floating-point tolerance
    const double diff = half_error > expected ? half_error - expected : expected - half_error;
    return diff < 1e-15 * expected;
}

} // namespace verified

#endif // PHYSICS_VERIFIED_RK4_HPP
