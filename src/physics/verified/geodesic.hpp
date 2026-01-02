/**
 * @file verified/geodesic.hpp
 * @brief Verified geodesic equations - derived from Rocq formalization
 *
 * This file is generated from proven Rocq theories in rocq/theories/Geodesics/Equations.v
 * Formalizes the geodesic equation:
 *   d^2 x^mu / d lambda^2 + Gamma^mu_{alpha beta} (dx^alpha/dlambda) (dx^beta/dlambda) = 0
 *
 * Key formalizations:
 *   - Constants of motion (energy, angular momentum, Carter constant)
 *   - Effective potential analysis
 *   - Impact parameter for null geodesics
 *   - Orbital classification
 *   - Initial condition setup
 *
 * Pipeline: Rocq 9.1+ -> OCaml -> C++23 -> GLSL 4.60
 *
 * @note All functions use geometric units where c = G = 1
 * @note Requires verified/rk4.hpp for StateVector definition
 */

#ifndef PHYSICS_VERIFIED_GEODESIC_HPP
#define PHYSICS_VERIFIED_GEODESIC_HPP

#include "rk4.hpp"
#include <cmath>
#include <functional>

namespace verified {

// ============================================================================
// Metric Components (from Rocq: MetricComponents record)
// ============================================================================

/**
 * @brief Metric tensor components in Boyer-Lindquist coordinates
 *
 * Derived from Rocq Prelim.v:
 *   Record MetricComponents := mkMetric {
 *     g_tt : R;
 *     g_rr : R;
 *     g_thth : R;
 *     g_phph : R;
 *     g_tph : R;  (* Off-diagonal for Kerr *)
 *   }.
 */
struct MetricComponents {
    double g_tt;    ///< Time-time component (negative for timelike)
    double g_rr;    ///< Radial component
    double g_thth;  ///< Theta-theta component
    double g_phph;  ///< Phi-phi component
    double g_tph;   ///< Time-phi off-diagonal (frame dragging)

    constexpr MetricComponents() noexcept
        : g_tt(-1.0), g_rr(1.0), g_thth(1.0), g_phph(1.0), g_tph(0.0) {}

    constexpr MetricComponents(double tt, double rr, double thth,
                               double phph, double tph = 0.0) noexcept
        : g_tt(tt), g_rr(rr), g_thth(thth), g_phph(phph), g_tph(tph) {}
};

// ============================================================================
// Christoffel Acceleration (from Rocq: ChristoffelAccel record)
// ============================================================================

/**
 * @brief Christoffel-derived accelerations for geodesic equation
 *
 * Derived from Rocq:
 *   Record ChristoffelAccel := mkChristoffel {
 *     accel_t : StateVector -> R;
 *     accel_r : StateVector -> R;
 *     accel_theta : StateVector -> R;
 *     accel_phi : StateVector -> R;
 *   }.
 */
struct ChristoffelAccel {
    std::function<double(const StateVector&)> accel_t;
    std::function<double(const StateVector&)> accel_r;
    std::function<double(const StateVector&)> accel_theta;
    std::function<double(const StateVector&)> accel_phi;
};

/**
 * @brief Build geodesic RHS from Christoffel acceleration
 *
 * Derived from Rocq:
 *   Definition geodesic_rhs (christoffel : ChristoffelAccel) (s : StateVector) :=
 *     mkSV
 *       s.(v0) s.(v1) s.(v2) s.(v3)  (* dx/dlambda = v *)
 *       (christoffel.(accel_t) s)    (* dv_t/dlambda *)
 *       (christoffel.(accel_r) s)    (* dv_r/dlambda *)
 *       (christoffel.(accel_theta) s)(* dv_theta/dlambda *)
 *       (christoffel.(accel_phi) s). (* dv_phi/dlambda *)
 *
 * @param christoffel Acceleration functions from Christoffel symbols
 * @param s Current state
 * @return Derivative state for RK4 integration
 */
[[nodiscard]] inline StateVector geodesic_rhs(const ChristoffelAccel& christoffel,
                                               const StateVector& s) noexcept {
    return StateVector{
        s.v0, s.v1, s.v2, s.v3,           // dx/dlambda = v
        christoffel.accel_t(s),           // dv_t/dlambda
        christoffel.accel_r(s),           // dv_r/dlambda
        christoffel.accel_theta(s),       // dv_theta/dlambda
        christoffel.accel_phi(s)          // dv_phi/dlambda
    };
}

/**
 * @brief Create geodesic RHS function from Christoffel acceleration
 *
 * Returns a callable suitable for rk4_step.
 */
[[nodiscard]] inline auto make_geodesic_rhs(const ChristoffelAccel& christoffel) {
    return [christoffel](const StateVector& s) -> StateVector {
        return geodesic_rhs(christoffel, s);
    };
}

// ============================================================================
// Constants of Motion (from Rocq: energy, angular_momentum, carter_constant)
// ============================================================================

/**
 * @brief Energy per unit mass for stationary spacetimes
 *
 * Derived from Rocq:
 *   Definition energy (g : MetricComponents) (s : StateVector) : R :=
 *     - g.(g_tt) * s.(v0) - g.(g_tph) * s.(v3).
 *
 * For stationary metrics (independent of t), E is conserved.
 *
 * @param g Metric components at current position
 * @param s Current state
 * @return Energy E = -g_tt * v^t - g_tph * v^phi
 */
[[nodiscard]] constexpr double energy(const MetricComponents& g,
                                       const StateVector& s) noexcept {
    return -g.g_tt * s.v0 - g.g_tph * s.v3;
}

/**
 * @brief Angular momentum per unit mass for axisymmetric spacetimes
 *
 * Derived from Rocq:
 *   Definition angular_momentum (g : MetricComponents) (s : StateVector) : R :=
 *     g.(g_phph) * s.(v3) + g.(g_tph) * s.(v0).
 *
 * For axisymmetric metrics (independent of phi), L is conserved.
 *
 * @param g Metric components at current position
 * @param s Current state
 * @return Angular momentum L = g_phph * v^phi + g_tph * v^t
 */
[[nodiscard]] constexpr double angular_momentum(const MetricComponents& g,
                                                 const StateVector& s) noexcept {
    return g.g_phph * s.v3 + g.g_tph * s.v0;
}

/**
 * @brief Carter constant for Kerr spacetime
 *
 * Derived from Rocq:
 *   Definition carter_constant (theta a E Lz : R) (p_theta : R) : R :=
 *     p_theta^2 + cos^2(theta) * (a^2 * (-E^2) + Lz^2 / sin^2(theta)).
 *
 * The Carter constant Q is the third constant of motion for Kerr.
 *
 * @param theta Polar angle
 * @param a Spin parameter
 * @param E Energy
 * @param Lz Angular momentum
 * @param p_theta Theta component of momentum
 * @return Carter constant Q
 */
[[nodiscard]] inline double carter_constant(double theta, double a,
                                             double E, double Lz,
                                             double p_theta) noexcept {
    const double cos_theta = std::cos(theta);
    const double sin_theta = std::sin(theta);
    const double cos2 = cos_theta * cos_theta;
    const double sin2 = sin_theta * sin_theta;

    return p_theta * p_theta +
           cos2 * (a * a * (-E * E) + Lz * Lz / sin2);
}

// ============================================================================
// Effective Potential (from Rocq: effective_potential_schwarzschild)
// ============================================================================

/**
 * @brief Effective potential for radial motion in Schwarzschild
 *
 * Derived from Rocq:
 *   Definition effective_potential_schwarzschild (r M E L : R) : R :=
 *     (1 - 2*M/r) * (1 + L^2 / r^2) - E^2.
 *
 * Radial motion satisfies: (dr/dlambda)^2 + V_eff = 0
 *
 * @param r Radial coordinate
 * @param M Black hole mass
 * @param E Energy per unit mass
 * @param L Angular momentum per unit mass
 * @return Effective potential
 */
[[nodiscard]] constexpr double effective_potential_schwarzschild(
    double r, double M, double E, double L) noexcept
{
    const double L2 = L * L;
    const double r2 = r * r;
    return (1.0 - 2.0 * M / r) * (1.0 + L2 / r2) - E * E;
}

/**
 * @brief Check circular orbit condition
 *
 * Derived from Rocq:
 *   Definition circular_orbit_condition (M L r : R) : Prop :=
 *     L^2 * (r - 3*M) = M * r^2.
 *
 * @param M Black hole mass
 * @param L Angular momentum
 * @param r Radial coordinate
 * @return Residual (should be zero for circular orbit)
 */
[[nodiscard]] constexpr double circular_orbit_residual(
    double M, double L, double r) noexcept
{
    return L * L * (r - 3.0 * M) - M * r * r;
}

// ============================================================================
// Impact Parameter (from Rocq: impact_parameter, critical_impact_schwarzschild)
// ============================================================================

/**
 * @brief Impact parameter b = L/E for null geodesics
 *
 * Derived from Rocq:
 *   Definition impact_parameter (E L : R) : R := L / E.
 *
 * @param E Energy
 * @param L Angular momentum
 * @return Impact parameter b
 */
[[nodiscard]] constexpr double impact_parameter(double E, double L) noexcept {
    return L / E;
}

/**
 * @brief Critical impact parameter for Schwarzschild photon capture
 *
 * Derived from Rocq:
 *   Definition critical_impact_schwarzschild (M : R) : R := 3 * sqrt(3) * M.
 *
 * Rays with b < b_crit are captured by the black hole.
 *
 * @param M Black hole mass
 * @return Critical impact parameter b_crit = 3*sqrt(3)*M
 */
[[nodiscard]] inline double critical_impact_schwarzschild(double M) noexcept {
    return 3.0 * std::sqrt(3.0) * M;
}

// ============================================================================
// Orbital Classification (from Rocq: OrbitType, classify_orbit_schwarzschild)
// ============================================================================

/**
 * @brief Classification of geodesic orbits
 *
 * Derived from Rocq:
 *   Inductive OrbitType :=
 *     | Plunging     (* Falls into singularity *)
 *     | Bound        (* Periodic orbit *)
 *     | Flyby        (* Escapes to infinity *)
 *     | Marginally.  (* On separatrix *)
 */
enum class OrbitType {
    Plunging,    ///< Falls into singularity
    Bound,       ///< Periodic orbit
    Flyby,       ///< Escapes to infinity
    Marginally   ///< On separatrix (marginally bound)
};

/**
 * @brief Classify Schwarzschild orbit by energy and angular momentum
 *
 * Derived from Rocq:
 *   Definition classify_orbit_schwarzschild (M E L : R) : OrbitType :=
 *     let L_crit := 4 * M in
 *     if Rlt_dec L L_crit then Plunging
 *     else if Rlt_dec E 1 then Bound
 *     else Flyby.
 *
 * @param M Black hole mass
 * @param E Energy per unit mass
 * @param L Angular momentum per unit mass
 * @return Orbit classification
 */
[[nodiscard]] constexpr OrbitType classify_orbit_schwarzschild(
    double M, double E, double L) noexcept
{
    const double L_crit = 4.0 * M;

    if (L < L_crit) {
        return OrbitType::Plunging;
    }
    if (E < 1.0) {
        return OrbitType::Bound;
    }
    return OrbitType::Flyby;
}

// ============================================================================
// Four-Norm (from Rocq: four_norm, is_null)
// ============================================================================

/**
 * @brief Compute four-norm g_ab v^a v^b
 *
 * Derived from Rocq Prelim.v:
 *   Definition four_norm (g : MetricComponents) (v : FourVector) : R :=
 *     g.(g_tt) * v.(v_t)^2 + g.(g_rr) * v.(v_r)^2 +
 *     g.(g_thth) * v.(v_th)^2 + g.(g_phph) * v.(v_ph)^2 +
 *     2 * g.(g_tph) * v.(v_t) * v.(v_ph).
 *
 * @param g Metric components
 * @param s State (uses velocity components)
 * @return g_ab v^a v^b
 */
[[nodiscard]] constexpr double four_norm(const MetricComponents& g,
                                          const StateVector& s) noexcept {
    return g.g_tt * s.v0 * s.v0 +
           g.g_rr * s.v1 * s.v1 +
           g.g_thth * s.v2 * s.v2 +
           g.g_phph * s.v3 * s.v3 +
           2.0 * g.g_tph * s.v0 * s.v3;
}

/**
 * @brief Check if state represents a null geodesic
 *
 * Derived from Rocq:
 *   Definition is_null (g : MetricComponents) (v : FourVector) : Prop :=
 *     four_norm g v = 0.
 *
 * @param g Metric components
 * @param s State
 * @param tolerance Tolerance for null check
 * @return true if |g_ab v^a v^b| < tolerance
 */
[[nodiscard]] constexpr bool is_null(const MetricComponents& g,
                                      const StateVector& s,
                                      double tolerance = 1e-10) noexcept {
    const double norm = four_norm(g, s);
    return norm > -tolerance && norm < tolerance;
}

/**
 * @brief Check if state represents a timelike geodesic
 *
 * Timelike geodesics satisfy g_ab v^a v^b = -1 (proper time parameterization)
 *
 * @param g Metric components
 * @param s State
 * @param tolerance Tolerance for check
 * @return true if |g_ab v^a v^b + 1| < tolerance
 */
[[nodiscard]] constexpr bool is_timelike(const MetricComponents& g,
                                          const StateVector& s,
                                          double tolerance = 1e-10) noexcept {
    const double norm = four_norm(g, s);
    const double diff = norm + 1.0;
    return diff > -tolerance && diff < tolerance;
}

// ============================================================================
// Initial Conditions (from Rocq: init_null_geodesic)
// ============================================================================

/**
 * @brief Initialize null geodesic from camera ray direction
 *
 * Derived from Rocq:
 *   Definition init_null_geodesic (r0 theta0 phi0 : R)
 *                                 (dir_r dir_theta dir_phi : R)
 *                                 (g : MetricComponents) : StateVector :=
 *     let v_t := sqrt(
 *       (g.(g_rr) * dir_r^2 + g.(g_thth) * dir_theta^2 + g.(g_phph) * dir_phi^2)
 *       / (-g.(g_tt))
 *     ) in
 *     mkSV 0 r0 theta0 phi0 v_t dir_r dir_theta dir_phi.
 *
 * Computes v^t from null condition: g_ab v^a v^b = 0
 *
 * @param r0 Initial radial position
 * @param theta0 Initial polar angle
 * @param phi0 Initial azimuthal angle
 * @param dir_r Radial direction
 * @param dir_theta Theta direction
 * @param dir_phi Phi direction
 * @param g Metric components at initial position
 * @return Initial state normalized to null geodesic
 */
[[nodiscard]] inline StateVector init_null_geodesic(
    double r0, double theta0, double phi0,
    double dir_r, double dir_theta, double dir_phi,
    const MetricComponents& g) noexcept
{
    // Solve g_ab v^a v^b = 0 for v^t
    // g_tt v_t^2 + g_rr v_r^2 + g_thth v_th^2 + g_phph v_ph^2 = 0
    // v_t = sqrt((g_rr * v_r^2 + g_thth * v_th^2 + g_phph * v_ph^2) / (-g_tt))

    const double spatial_norm =
        g.g_rr * dir_r * dir_r +
        g.g_thth * dir_theta * dir_theta +
        g.g_phph * dir_phi * dir_phi;

    const double v_t = std::sqrt(spatial_norm / (-g.g_tt));

    return StateVector{
        0.0, r0, theta0, phi0,    // Position (t=0)
        v_t, dir_r, dir_theta, dir_phi  // Velocity
    };
}

/**
 * @brief Initialize null geodesic with specified energy and angular momentum
 *
 * @param r0 Initial radial position
 * @param theta0 Initial polar angle
 * @param E Energy per unit mass
 * @param L Angular momentum per unit mass
 * @param g Metric at initial position
 * @return Initial state
 */
[[nodiscard]] inline StateVector init_null_geodesic_EL(
    double r0, double theta0,
    double E, double L,
    const MetricComponents& g) noexcept
{
    // For equatorial orbits with given E, L
    // v^t = E / (-g_tt)  (from energy definition)
    // v^phi = L / g_phph (from angular momentum definition)
    // v^r from null condition

    const double v_t = E / (-g.g_tt);
    const double v_phi = L / g.g_phph;

    // Null condition: g_tt v_t^2 + g_rr v_r^2 + g_phph v_phi^2 = 0
    const double v_r_sq = -(g.g_tt * v_t * v_t + g.g_phph * v_phi * v_phi) / g.g_rr;
    const double v_r = v_r_sq >= 0.0 ? std::sqrt(v_r_sq) : 0.0;

    return StateVector{
        0.0, r0, theta0, 0.0,
        v_t, v_r, 0.0, v_phi
    };
}

// ============================================================================
// Conservation Check (from Rocq: energy_conservation, angular_momentum_conservation)
// ============================================================================

/**
 * @brief Check energy conservation between two states
 *
 * Derived from Rocq:
 *   Theorem energy_conservation : forall g s0 s1 h,
 *     Rabs (energy g s1 - energy g s0) < h^4.
 *
 * @param g Metric components
 * @param s0 Previous state
 * @param s1 Current state
 * @param h Step size
 * @return true if energy drift is within RK4 bounds
 */
[[nodiscard]] constexpr bool check_energy_conservation(
    const MetricComponents& g,
    const StateVector& s0, const StateVector& s1,
    double h) noexcept
{
    const double E0 = energy(g, s0);
    const double E1 = energy(g, s1);
    const double drift = E1 - E0;
    const double bound = h * h * h * h;  // O(h^4)

    return drift >= -bound && drift <= bound;
}

/**
 * @brief Check angular momentum conservation between two states
 *
 * @param g Metric components
 * @param s0 Previous state
 * @param s1 Current state
 * @param h Step size
 * @return true if angular momentum drift is within RK4 bounds
 */
[[nodiscard]] constexpr bool check_angular_momentum_conservation(
    const MetricComponents& g,
    const StateVector& s0, const StateVector& s1,
    double h) noexcept
{
    const double L0 = angular_momentum(g, s0);
    const double L1 = angular_momentum(g, s1);
    const double drift = L1 - L0;
    const double bound = h * h * h * h;  // O(h^4)

    return drift >= -bound && drift <= bound;
}

// ============================================================================
// Schwarzschild-Specific Geodesic Helpers
// ============================================================================

/**
 * @brief Create Schwarzschild Christoffel acceleration
 *
 * Uses Christoffel symbols from verified/schwarzschild.hpp
 *
 * @param M Black hole mass
 * @return ChristoffelAccel for Schwarzschild geodesics
 */
inline ChristoffelAccel make_schwarzschild_christoffel(double M) {
    return ChristoffelAccel{
        // accel_t: -Gamma^t_{tr} * v^t * v^r - Gamma^t_{rt} * v^r * v^t
        [M](const StateVector& s) -> double {
            const double r = s.x1;
            const double Gamma_t_tr = M / (r * (r - 2.0 * M));
            return -2.0 * Gamma_t_tr * s.v0 * s.v1;
        },

        // accel_r: sum of all Gamma^r terms
        [M](const StateVector& s) -> double {
            const double r = s.x1;
            const double theta = s.x2;
            const double sin_theta = std::sin(theta);

            const double Gamma_r_tt = M * (r - 2.0 * M) / (r * r * r);
            const double Gamma_r_rr = -M / (r * (r - 2.0 * M));
            const double Gamma_r_thth = -(r - 2.0 * M);
            const double Gamma_r_phph = -(r - 2.0 * M) * sin_theta * sin_theta;

            return -Gamma_r_tt * s.v0 * s.v0
                   - Gamma_r_rr * s.v1 * s.v1
                   - Gamma_r_thth * s.v2 * s.v2
                   - Gamma_r_phph * s.v3 * s.v3;
        },

        // accel_theta: -2 * Gamma^th_{r th} * v^r * v^th - Gamma^th_{phph} * v^ph^2
        [](const StateVector& s) -> double {
            const double r = s.x1;
            const double theta = s.x2;
            const double Gamma_th_rth = 1.0 / r;
            const double Gamma_th_phph = -std::sin(theta) * std::cos(theta);

            return -2.0 * Gamma_th_rth * s.v1 * s.v2
                   - Gamma_th_phph * s.v3 * s.v3;
        },

        // accel_phi: -2 * Gamma^ph_{r ph} * v^r * v^ph - 2 * Gamma^ph_{th ph} * v^th * v^ph
        [](const StateVector& s) -> double {
            const double r = s.x1;
            const double theta = s.x2;
            const double Gamma_ph_rph = 1.0 / r;
            const double Gamma_ph_thph = std::cos(theta) / std::sin(theta);

            return -2.0 * Gamma_ph_rph * s.v1 * s.v3
                   - 2.0 * Gamma_ph_thph * s.v2 * s.v3;
        }
    };
}

} // namespace verified

#endif // PHYSICS_VERIFIED_GEODESIC_HPP
