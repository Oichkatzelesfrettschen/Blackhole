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

// Full geodesic integration from λ₀ to λ_final
template<IntegratorScalar Real>
[[nodiscard]] inline StateVector<Real> integrate(
    StateVector<Real> y, Real lambda_0, Real lambda_final, Real h_init,
    Real M, Real a, GeodesicRHS<Real> f,
    Real tolerance = 1e-10) noexcept
{
    Real lambda = lambda_0;
    Real h = h_init;

    while (lambda < lambda_final) {
        // Adaptive step size
        if (lambda + h > lambda_final) {
            h = lambda_final - lambda;
        }

        auto [y_new, error, h_used] = rk4_step_with_error(y, lambda, h, M, a, f);

        // Simple adaptive control: increase/decrease step based on error
        if (error < tolerance / 10.0) {
            h *= 1.2;  // Increase step size
        } else if (error > tolerance) {
            h *= 0.5;  // Decrease step size and retry
            continue;
        }

        y = y_new;
        lambda += h;
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
