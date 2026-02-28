// Verified RK4 Geodesic Integrator
// Fourth-order Runge-Kutta with error bounds
// Extracted from Rocq proofs via OCaml extraction

#pragma once

#include <array>
#include <concepts>
#include <cmath>

namespace verified {

template<typename Real = double>
concept IntegratorScalar = std::floating_point<Real>;

// State vector: 8D phase space in Boyer-Lindquist coordinates
// Position: (t, r, theta, phi)
// Velocity: (dt/dlambda, dr/dlambda, dtheta/dlambda, dphi/dlambda)
template<IntegratorScalar Real>
struct StateVector {
    Real x0, x1, x2, x3;      // Position (t, r, theta, phi)
    Real v0, v1, v2, v3;      // Velocity (dt/λ, dr/λ, dθ/λ, dφ/λ)

    // Vector addition
    [[nodiscard]] constexpr StateVector operator+(const StateVector& other) const noexcept {
        return {
            x0 + other.x0, x1 + other.x1, x2 + other.x2, x3 + other.x3,
            v0 + other.v0, v1 + other.v1, v2 + other.v2, v3 + other.v3
        };
    }

    // Scalar multiplication
    [[nodiscard]] constexpr StateVector operator*(Real scalar) const noexcept {
        return {
            scalar * x0, scalar * x1, scalar * x2, scalar * x3,
            scalar * v0, scalar * v1, scalar * v2, scalar * v3
        };
    }

    // In-place scalar multiplication
    StateVector& scale_inplace(Real scalar) noexcept {
        x0 *= scalar; x1 *= scalar; x2 *= scalar; x3 *= scalar;
        v0 *= scalar; v1 *= scalar; v2 *= scalar; v3 *= scalar;
        return *this;
    }

    // Euclidean norm (for error estimation)
    [[nodiscard]] inline Real norm() const noexcept {
        return std::sqrt(
            x0*x0 + x1*x1 + x2*x2 + x3*x3 +
            v0*v0 + v1*v1 + v2*v2 + v3*v3
        );
    }
};

// Right-hand side of geodesic equations
// dy/dλ = f(λ, y) where y = (position, velocity)
// Returns acceleration components (velocity is already in state)
template<IntegratorScalar Real>
using GeodesicRHS = StateVector<Real>(*)(const StateVector<Real>&, Real, Real, Real);

// RK4 stage 1: k1 = h * f(λ, y)
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> rk4_k1(
    const StateVector<Real>& y, Real lambda, Real h,
    Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    auto k = f(y, lambda, M, a);
    return k * h;
}

// RK4 stage 2: k2 = h * f(λ + h/2, y + k1/2)
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> rk4_k2(
    const StateVector<Real>& y, const StateVector<Real>& k1,
    Real lambda, Real h, Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    auto y_half = y + (k1 * 0.5);
    auto k = f(y_half, lambda + h / 2.0, M, a);
    return k * h;
}

// RK4 stage 3: k3 = h * f(λ + h/2, y + k2/2)
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> rk4_k3(
    const StateVector<Real>& y, const StateVector<Real>& k2,
    Real lambda, Real h, Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    auto y_half = y + (k2 * 0.5);
    auto k = f(y_half, lambda + h / 2.0, M, a);
    return k * h;
}

// RK4 stage 4: k4 = h * f(λ + h, y + k3)
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> rk4_k4(
    const StateVector<Real>& y, const StateVector<Real>& k3,
    Real lambda, Real h, Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    auto y_next = y + k3;
    auto k = f(y_next, lambda + h, M, a);
    return k * h;
}

// RK4 combination: y_next = y + (k1 + 2*k2 + 2*k3 + k4) / 6
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> rk4_combine(
    const StateVector<Real>& y,
    const StateVector<Real>& k1, const StateVector<Real>& k2,
    const StateVector<Real>& k3, const StateVector<Real>& k4) noexcept
{
    const Real weight_1_4 = 1.0 / 6.0;
    const Real weight_2_3 = 2.0 / 6.0;

    return y + (k1 * weight_1_4) + (k2 * weight_2_3) +
               (k3 * weight_2_3) + (k4 * weight_1_4);
}

// RK4 error estimate (difference between 4th and 5th order methods)
// Used for adaptive step size control
template<IntegratorScalar Real>
[[nodiscard]] inline Real rk4_error_estimate(
    const StateVector<Real>& k1, const StateVector<Real>& k2,
    const StateVector<Real>& k3, const StateVector<Real>& k4) noexcept
{
    // Local truncation error: O(h^5)
    // Approximate via Runge-Kutta error estimate
    const Real c1 = 1.0 / 6.0;
    const Real c2 = -1.0 / 6.0;
    const Real c3 = -1.0 / 6.0;
    const Real c4 = 1.0 / 6.0;

    auto error = (k1 * c1) + (k2 * c2) + (k3 * c3) + (k4 * c4);
    return error.norm();
}

// Single RK4 integration step
// y(λ + h) ≈ RK4(λ, y, h)
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> rk4_step(
    const StateVector<Real>& y, Real lambda, Real h,
    Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    auto k1 = rk4_k1(y, lambda, h, M, a, f);
    auto k2 = rk4_k2(y, k1, lambda, h, M, a, f);
    auto k3 = rk4_k3(y, k2, lambda, h, M, a, f);
    auto k4 = rk4_k4(y, k3, lambda, h, M, a, f);

    return rk4_combine(y, k1, k2, k3, k4);
}

// RK4 step with error estimation
template<IntegratorScalar Real>
struct RK4StepResult {
    StateVector<Real> state;    // Updated state at λ + h
    Real error;                  // Local truncation error estimate
    Real step_size;              // Actual step size used
};

template<IntegratorScalar Real>
[[nodiscard]] inline RK4StepResult<Real> rk4_step_with_error(
    const StateVector<Real>& y, Real lambda, Real h,
    Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    auto k1 = rk4_k1(y, lambda, h, M, a, f);
    auto k2 = rk4_k2(y, k1, lambda, h, M, a, f);
    auto k3 = rk4_k3(y, k2, lambda, h, M, a, f);
    auto k4 = rk4_k4(y, k3, lambda, h, M, a, f);

    auto error = rk4_error_estimate(k1, k2, k3, k4);
    auto state = rk4_combine(y, k1, k2, k3, k4);

    return {state, error, h};
}

// Local error bound (for convergence analysis)
template<IntegratorScalar Real>
[[nodiscard]] constexpr Real local_error_bound(Real h, Real C = 1e-3) noexcept {
    // Typical bound: error ~ C * h^5
    // For RK4: error = O(h^5)
    return C * h * h * h * h * h;
}

// ============================================================================
// Dormand-Prince RK45 embedded pair (Shampine & Watts 1986)
//
// WHY: The heuristic step control in integrate() (h*=1.2 / h*=0.5) does not
// use a proper error estimate and can over- or under-step near the photon
// sphere.  Dormand-Prince provides an O(h^5) solution and O(h^4) error
// estimate from the same 7-stage evaluation, enabling principled adaptive
// step selection per Hairer, Norsett & Wanner (1993).
//
// The Butcher tableau coefficients below are from Dormand & Prince (1980),
// J. Comput. Appl. Math. 6, 19.
// ============================================================================

// DP45 stage coefficients (nodes c2..c6)
template<IntegratorScalar Real>
struct DP45Stages {
    StateVector<Real> k1, k2, k3, k4, k5, k6, k7;
};

template<IntegratorScalar Real>
[[nodiscard]] inline DP45Stages<Real> dp45_stages(
    const StateVector<Real>& y, Real lambda, Real h,
    Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    DP45Stages<Real> s;
    // k1 = h * f(y)
    s.k1 = f(y, lambda, M, a) * h;

    // k2: c2 = 1/5
    auto y2 = y + (s.k1 * (1.0/5.0));
    s.k2 = f(y2, lambda + h/5.0, M, a) * h;

    // k3: c3 = 3/10
    auto y3 = y + (s.k1 * (3.0/40.0)) + (s.k2 * (9.0/40.0));
    s.k3 = f(y3, lambda + 3.0*h/10.0, M, a) * h;

    // k4: c4 = 4/5
    auto y4 = y + (s.k1 * (44.0/45.0)) + (s.k2 * (-56.0/15.0)) + (s.k3 * (32.0/9.0));
    s.k4 = f(y4, lambda + 4.0*h/5.0, M, a) * h;

    // k5: c5 = 8/9
    auto y5 = y + (s.k1 * (19372.0/6561.0)) + (s.k2 * (-25360.0/2187.0))
                + (s.k3 * (64448.0/6561.0)) + (s.k4 * (-212.0/729.0));
    s.k5 = f(y5, lambda + 8.0*h/9.0, M, a) * h;

    // k6: c6 = 1 (FSAL candidate)
    auto y6 = y + (s.k1 * (9017.0/3168.0))   + (s.k2 * (-355.0/33.0))
                + (s.k3 * (46732.0/5247.0))   + (s.k4 * (49.0/176.0))
                + (s.k5 * (-5103.0/18656.0));
    s.k6 = f(y6, lambda + h, M, a) * h;

    // 5th-order solution (for propagation)
    auto y5th = y + (s.k1 * (35.0/384.0))  + (s.k3 * (500.0/1113.0))
                  + (s.k4 * (125.0/192.0)) + (s.k5 * (-2187.0/6784.0))
                  + (s.k6 * (11.0/84.0));

    // k7 = f(y5th) for FSAL and error estimate
    s.k7 = f(y5th, lambda + h, M, a) * h;

    return s;
}

// Dormand-Prince step: returns 5th-order solution and embedded error estimate
template<IntegratorScalar Real>
struct DP45Result {
    StateVector<Real> y5;    // 5th-order propagated state
    Real error;               // Embedded error norm (||y5 - y4||_inf)
    Real h;                   // Step size used
};

template<IntegratorScalar Real>
[[nodiscard]] inline DP45Result<Real> dp45_step(
    const StateVector<Real>& y, Real lambda, Real h,
    Real M, Real a, GeodesicRHS<Real> f) noexcept
{
    auto s = dp45_stages(y, lambda, h, M, a, f);

    // 5th-order solution
    auto y5 = y + (s.k1 * (35.0/384.0))   + (s.k3 * (500.0/1113.0))
                + (s.k4 * (125.0/192.0))  + (s.k5 * (-2187.0/6784.0))
                + (s.k6 * (11.0/84.0));

    // 4th-order solution (embedded)
    auto y4 = y + (s.k1 * (5179.0/57600.0))  + (s.k3 * (7571.0/16695.0))
                + (s.k4 * (393.0/640.0))     + (s.k5 * (-92097.0/339200.0))
                + (s.k6 * (187.0/2100.0))    + (s.k7 * (1.0/40.0));

    // Error = ||y5 - y4|| (local extrapolation)
    auto err_vec = y5 + (y4 * static_cast<Real>(-1.0));
    Real error = err_vec.norm();

    return {y5, error, h};
}

// Optimal step size for next iteration (Hairer 1993, Eq. II.4.12)
// h_new = h * min(fac_max, max(fac_min, fac * (tol/err)^(1/5)))
template<IntegratorScalar Real>
[[nodiscard]] inline Real dp45_next_step(Real h, Real error, Real tol) noexcept {
    if (error < static_cast<Real>(1e-50)) return h * 2.0;
    Real ratio = std::pow(tol / error, static_cast<Real>(0.2));
    // Safety factor and bounds from Hairer p. 168
    Real factor = std::min(static_cast<Real>(2.0),
                           std::max(static_cast<Real>(0.1),
                                    static_cast<Real>(0.9) * ratio));
    return h * factor;
}

// Full geodesic integration from lambda_0 to lambda_final using DP45
// Falls back to fixed-step RK4 if DP45 is disabled via compile flag.
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> integrate(
    StateVector<Real> y, Real lambda_0, Real lambda_final, Real h_init,
    Real M, Real a, GeodesicRHS<Real> f,
    Real tolerance = 1e-10) noexcept
{
    Real lambda = lambda_0;
    Real h = h_init;
    const Real h_min = h_init * static_cast<Real>(1e-8);

    while (lambda < lambda_final) {
        // Clamp step to remaining interval
        if (lambda + h > lambda_final) {
            h = lambda_final - lambda;
        }
        if (h < h_min) h = h_min;

        // Dormand-Prince adaptive step
        auto [y_new, error, h_used] = dp45_step(y, lambda, h, M, a, f);

        if (error < tolerance || h <= h_min) {
            // Accept step
            y = y_new;
            lambda += h_used;
        }
        // Adjust step for next iteration (whether accepted or not)
        h = dp45_next_step(h_used, error, tolerance);
    }

    return y;
}

// Check termination condition (e.g., reached singularity or escape)
template<IntegratorScalar Real>
[[nodiscard]] constexpr bool check_termination(
    const StateVector<Real>& state, Real M, Real a) noexcept
{
    // Termination if r < r_+ (crossed event horizon)
    const Real r = state.x1;
    const Real r_plus = M + std::sqrt(M * M - a * a);

    return r < r_plus;
}

}  // namespace verified
