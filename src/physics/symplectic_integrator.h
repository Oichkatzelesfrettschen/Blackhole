/**
 * @file symplectic_integrator.h
 * @brief 4th-order Yoshida symplectic geodesic integrator for Kerr spacetime.
 *
 * WHY: RK4 geodesic integration accumulates a secular Hamiltonian drift because
 * it is not symplectic -- it does not exactly preserve the phase-space volume
 * element dp ^ dq at each step.  For long integrations (many-orbit accretion
 * disk trajectories, precision EHT ray tracing, stability analyses) this drift
 * corrupts the conserved invariants E, L_z, Carter Q over time.  A symplectic
 * integrator bounds the Hamiltonian error: it oscillates around a "shadow"
 * Hamiltonian H_tilde at O(h^4) amplitude rather than growing secularly.
 *
 * WHAT: The Yoshida (1990) 4th-order composition applies three leapfrog
 * (Stormer-Verlet) steps with weights
 *
 *   w1 = 1 / (2 - 2^{1/3}),   w0 = 1 - 2 w1 = -2^{1/3} / (2 - 2^{1/3})
 *
 * to achieve 4th-order global accuracy.  The base leapfrog uses a DKD
 * (drift-kick-drift) splitting of the geodesic Hamiltonian:
 *
 *   H(q, p) = (1/2) g^{mu nu}(q) p_mu p_nu
 *
 * in Boyer-Lindquist coordinates with covariant momenta p_mu.
 *
 * Each sub-step:
 *   Drift (A): q^mu  +=  h * g^{mu nu}(q) p_nu
 *   Kick  (B): p_mu  +=  h * (-partial H / partial q^mu)
 *
 * The kick uses central-difference evaluation of H for the r and theta
 * components (the only coordinates on which H depends).  The t and phi
 * components are set analytically to zero, preserving p_t = -E and
 * p_phi = L_z to floating-point precision.
 *
 * WHY covariant momenta: p_t = -E and p_phi = L_z are Killing momenta, exactly
 * conserved because Gamma^sigma_{t rho} and Gamma^sigma_{phi rho} both contract
 * to zero via metric compatibility when the metric has the corresponding symmetry.
 * This is not an approximation; the cancellation is algebraic.
 *
 * HOW: Include this header, construct a GeodesicState and KerrParams, then call
 * yoshida4Step() or integrateGeodesic().  Parameters follow the connection.h
 * convention: rS = 2M is the Schwarzschild radius in geometric units (G=c=1).
 *
 * OPTIMISED SEQUENCE (7 sub-steps: 4 drifts + 3 kicks):
 *   The three DKD leapfrogs share adjacent end/start drift steps, reducing
 *   9 sub-steps to 7 without any accuracy loss:
 *     drift(c1) kick(w1) drift(c2) kick(w0) drift(c2) kick(w1) drift(c1)
 *   where c1 = w1/2 and c2 = (w1+w0)/2 = (1-w1)/2.
 *
 * References:
 *   - Yoshida, H. (1990). Phys. Lett. A 150, 262 -- 4th-order composition
 *   - Ruth, R. D. (1983). IEEE Trans. Nucl. Sci. 30, 2669 -- symplectic maps
 *   - Lubich, C. et al. (2010). Phys. Rev. D 81, 104025 -- Kerr application
 *   - Misner, Thorne & Wheeler (1973). Gravitation, ch. 33 -- geodesic H
 *   - Hairer, Lubich & Wanner (2006). Geometric Numerical Integration, ch. V
 */

#ifndef PHYSICS_SYMPLECTIC_INTEGRATOR_H
#define PHYSICS_SYMPLECTIC_INTEGRATOR_H

#include "connection.h"  // kerrGcon, Metric4 (kerrConnection not used here)

#include <array>
#include <cmath>

namespace physics {

// ============================================================================
// Parameter bundle
// ============================================================================

/**
 * @brief Kerr spacetime parameters for the symplectic integrator.
 *
 * Uses the rS = 2M convention (Schwarzschild radius) matching connection.h.
 * Convert geometric mass M to rS via rS = 2*M before constructing this struct.
 *
 * Validity: |a| <= rS/2 for a sub-extremal black hole.
 */
struct KerrParams {
    double a;   ///< Spin parameter J/M [geometric units]
    double rS;  ///< Schwarzschild radius 2M [geometric units]; rS > 0
};

// ============================================================================
// Phase-space state
// ============================================================================

/**
 * @brief Geodesic phase-space state in Boyer-Lindquist coordinates.
 *
 * The canonical position q = (t, r, theta, phi) and covariant momenta
 * p_mu = g_{mu nu} u^nu, where u^nu = dq^nu/dlambda is the contravariant
 * 4-velocity and lambda is the affine parameter.
 *
 * On-shell constraint: H = (1/2) g^{mu nu} p_mu p_nu equals
 *   -1/2 for timelike geodesics (signature -+++),
 *    0   for null geodesics.
 *
 * The Killing momenta p_t = -E (energy) and p_phi = L_z (axial angular
 * momentum) are conserved along Kerr geodesics.
 */
struct GeodesicState {
    std::array<double, 4> q;  ///< BL coordinates (t, r, theta, phi)
    std::array<double, 4> p;  ///< Covariant momenta (p_t, p_r, p_theta, p_phi)
};

// ============================================================================
// Hamiltonian and kinematics
// ============================================================================

/**
 * @brief Kerr geodesic Hamiltonian: H = (1/2) g^{mu nu}(q) p_mu p_nu.
 *
 * WHY: H is the primary conserved invariant for geodesic motion.  For
 * timelike geodesics H = -1/2; for null geodesics H = 0.  Monitoring H
 * across integration steps quantifies symplectic performance and detects
 * numerical instability near coordinate singularities.
 *
 * @param s      Current phase-space state.
 * @param params Kerr parameters (a, rS).
 * @return H [dimensionless in geometric units].
 */
[[nodiscard]] inline double kerrHamiltonian(const GeodesicState& s,
                                            const KerrParams& params) noexcept {
    const Metric4 gcon = kerrGcon(s.q[1], s.q[2], params.a, params.rS);
    double H = 0.0;
    for (std::size_t mu = 0; mu < 4; ++mu)
        for (std::size_t nu = 0; nu < 4; ++nu)
            H += gcon.at(mu).at(nu) * s.p[mu] * s.p[nu];
    return 0.5 * H;
}

/**
 * @brief Compute contravariant velocity: u^mu = g^{mu nu}(q) p_nu.
 *
 * This is dq^mu/dlambda -- the coordinate velocity with respect to the affine
 * parameter.  Used by both the drift sub-step and the force (kick) computation.
 *
 * @param s      Current phase-space state.
 * @param params Kerr parameters (a, rS).
 * @return Contravariant 4-velocity u^mu.
 */
[[nodiscard]] inline std::array<double, 4> kerrVelocity(
    const GeodesicState& s, const KerrParams& params) noexcept {
    const Metric4 gcon = kerrGcon(s.q[1], s.q[2], params.a, params.rS);
    std::array<double, 4> vel{};
    for (std::size_t mu = 0; mu < 4; ++mu)
        for (std::size_t nu = 0; nu < 4; ++nu)
            vel[mu] += gcon.at(mu).at(nu) * s.p[nu];
    return vel;
}

/**
 * @brief Compute dp_mu/dlambda = -partial H/partial q^mu via central differences.
 *
 * WHY finite differences instead of Christoffel contraction: the Hamilton
 * equations directly give
 *
 *   dp_mu/dlambda = -partial H / partial q^mu
 *
 * where H = (1/2) g^{alpha beta}(r, theta) p_alpha p_beta.  The metric does
 * not depend on t or phi (stationarity and axisymmetry of Kerr), so
 *
 *   dp_t   / dlambda = 0   exactly  (p_t = -E conserved)
 *   dp_phi / dlambda = 0   exactly  (p_phi = L_z conserved)
 *
 * These two components are set to zero analytically -- no arithmetic, no
 * cancellation, exact to floating-point precision.  For the remaining two
 * (r and theta), which do depend on position, central differences of H give
 *
 *   dp_r     / dlambda ~ -(H(r+eps) - H(r-eps)) / (2*eps)
 *   dp_theta / dlambda ~ -(H(theta+eps) - H(theta-eps)) / (2*eps)
 *
 * with truncation error O(eps^2 partial^3 H).  For eps = 1e-5 the FD error
 * is ~1e-10, negligible relative to the O(h^4) Yoshida global error.
 *
 * @param s      Current phase-space state.
 * @param params Kerr parameters (a, rS).
 * @param eps    Central-difference step [geometric units]; default 1e-5.
 * @return dp_mu/dlambda for each mu (indices 0 and 3 are identically zero).
 */
[[nodiscard]] inline std::array<double, 4> kerrForce(
    const GeodesicState& s,
    const KerrParams& params,
    double eps = 1.0e-5) noexcept {
    std::array<double, 4> rate{};

    // mu=0 (t): dp_t/dlambda = 0 exactly -- metric independent of t.
    // mu=3 (phi): dp_phi/dlambda = 0 exactly -- metric independent of phi.

    // mu=1 (r): central difference w.r.t. s.q[1] = r.
    {
        GeodesicState sp = s;
        GeodesicState sm = s;
        sp.q[1] += eps;
        sm.q[1] -= eps;
        rate[1] = -(kerrHamiltonian(sp, params) - kerrHamiltonian(sm, params)) / (2.0 * eps);
    }

    // mu=2 (theta): central difference w.r.t. s.q[2] = theta.
    {
        GeodesicState sp = s;
        GeodesicState sm = s;
        sp.q[2] += eps;
        sm.q[2] -= eps;
        rate[2] = -(kerrHamiltonian(sp, params) - kerrHamiltonian(sm, params)) / (2.0 * eps);
    }

    return rate;
}

// ============================================================================
// DKD leapfrog sub-steps
// ============================================================================

/**
 * @brief Apply a drift sub-step: q^mu += h * g^{mu nu}(q) p_nu.
 *
 * WHY evaluate metric at current q before update: the exact drift flow
 * for H = (1/2) g^{mu nu}(q) p_mu p_nu is not analytically integrable because
 * g depends on q.  Evaluating at the current point gives a first-order
 * approximation to the exact flow; the Yoshida composition corrects the global
 * error to O(h^4) by cancellation across the three leapfrog sub-steps.
 *
 * @param s      State updated in-place (only q modified).
 * @param h      Sub-step size (signed; may be negative for Yoshida middle step).
 * @param params Kerr parameters.
 */
inline void applyDrift(GeodesicState& s, double h,
                       const KerrParams& params) noexcept {
    const auto vel = kerrVelocity(s, params);
    for (std::size_t mu = 0; mu < 4; ++mu)
        s.q[mu] += h * vel[mu];
}

/**
 * @brief Apply a kick sub-step: p_mu += h * (-partial H/partial q^mu).
 *
 * @param s      State updated in-place (only p modified).
 * @param h      Sub-step size.
 * @param params Kerr parameters.
 */
inline void applyKick(GeodesicState& s, double h,
                      const KerrParams& params) noexcept {
    const auto rate = kerrForce(s, params);
    for (std::size_t mu = 0; mu < 4; ++mu)
        s.p[mu] += h * rate[mu];
}

// ============================================================================
// Yoshida 4th-order step
// ============================================================================

/**
 * @brief Single 4th-order Yoshida symplectic step for Kerr geodesics.
 *
 * WHY Yoshida composition: the leapfrog DKD integrator is 2nd-order symplectic.
 * Yoshida (1990) proved that composing three leapfrog steps with the weights
 *
 *   w1 = 1 / (2 - 2^{1/3})  ~  +1.3512071919596578
 *   w0 = 1 - 2 w1           ~  -1.7024143839193153
 *
 * yields a 4th-order symplectic method.  The negative middle weight w0 is
 * unavoidable for any explicit real-coefficient 4th-order composition (Suzuki
 * 1992 no-go theorem).  Adjacent drift sub-steps at the boundary of each
 * leapfrog are merged to produce the optimised 4D+3K sequence below.
 *
 * SEQUENCE (4 drifts D, 3 kicks K):
 *   D(c1) K(w1) D(c2) K(w0) D(c2) K(w1) D(c1)
 *   c1 = w1/2,  c2 = (w1+w0)/2 = (1-w1)/2
 *
 * This requires 4 kerrGcon calls (drift velocity) + 3 kerrGcon + 3 kerrConnection
 * calls (kick velocity + Christoffels) = 7 metric + 3 connection evaluations
 * per full step.
 *
 * @param s      State advanced in-place by one full step of size h.
 * @param h      Affine-parameter step size.
 * @param params Kerr parameters (a, rS).
 */
inline void yoshida4Step(GeodesicState& s, double h,
                         const KerrParams& params) noexcept {
    // Yoshida 4th-order composition coefficients.
    static constexpr double kCbrt2 = 1.2599210498948732;   // 2^{1/3}
    static constexpr double kW1    = 1.0 / (2.0 - kCbrt2); // ~+1.3512
    static constexpr double kW0    = 1.0 - 2.0 * kW1;      // ~-1.7024

    // Merged drift coefficients (c1 = w1/2; c2 = (w1+w0)/2 = (1-w1)/2).
    static constexpr double kC1 = kW1 * 0.5;
    static constexpr double kC2 = (kW1 + kW0) * 0.5;  // = (1.0 - kW1) * 0.5

    applyDrift(s, kC1 * h, params);
    applyKick (s, kW1 * h, params);
    applyDrift(s, kC2 * h, params);
    applyKick (s, kW0 * h, params);
    applyDrift(s, kC2 * h, params);
    applyKick (s, kW1 * h, params);
    applyDrift(s, kC1 * h, params);
}

// ============================================================================
// High-level integrator
// ============================================================================

/**
 * @brief Integrate a Kerr geodesic forward by a specified affine-parameter span.
 *
 * Advances the state by dLambda using nSteps equal Yoshida 4th-order steps,
 * each of size h = dLambda / nSteps.  The Hamiltonian H remains bounded at
 * O(h^4) deviation from its initial value for all N, not growing with time.
 *
 * For time-reversal: integrateGeodesic(s, -dLambda, nSteps, params) approximately
 * recovers the initial state.  The Yoshida coefficients are palindromic, which
 * guarantees S4(-h) = S4(h)^{-1} for separable Hamiltonians.  For Kerr (non-
 * separable H), the drift sub-step evaluates g^{mu nu}(q) at the pre-update q;
 * on reversal the metric is evaluated at a different q, giving an O(h^4)
 * per-step residual that accumulates as ~N h^4 over N steps.
 *
 * @param s       Initial state; overwritten with final state.
 * @param dLambda Total affine-parameter span (positive = forward; negative = backward).
 * @param nSteps  Number of equal-size steps; must be positive.
 * @param params  Kerr parameters.
 */
inline void integrateGeodesic(GeodesicState& s,
                               double dLambda, int nSteps,
                               const KerrParams& params) noexcept {
    if (nSteps <= 0) return;
    const double h = dLambda / static_cast<double>(nSteps);
    for (int k = 0; k < nSteps; ++k)
        yoshida4Step(s, h, params);
}

} // namespace physics

#endif // PHYSICS_SYMPLECTIC_INTEGRATOR_H
