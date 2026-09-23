/**
 * @file verified/geodesic.hpp
 * @brief Verified geodesic equations - derived from Rocq formalization
 *
 * Maintained C++ reference for rocq/theories/Geodesics/Equations.v
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
 * The maintained C++ is an input to scripts/cpp_to_glsl.py.
 * Rocq definitions document the mathematical source; floating-point
 * implementations are checked by tests rather than a proved extraction chain.
 *
 * @note All functions use geometric units where c = G = 1
 * @note Requires verified/rk4.hpp for StateVector definition
 */

#ifndef PHYSICS_VERIFIED_GEODESIC_HPP
#define PHYSICS_VERIFIED_GEODESIC_HPP

#include <cmath>
#include <functional>
#include <numbers>

#include "rk4.hpp"

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
  double gTt;   ///< Time-time component (negative for timelike)
  double gRr;   ///< Radial component
  double gThth; ///< Theta-theta component
  double gPhph; ///< Phi-phi component
  double gTph;  ///< Time-phi off-diagonal (frame dragging)

  constexpr MetricComponents() noexcept : gTt(-1.0), gRr(1.0), gThth(1.0), gPhph(1.0), gTph(0.0) {}

  constexpr MetricComponents(double tt, double rr, double thth, double phph,
                             double tph = 0.0) noexcept
      : gTt(tt), gRr(rr), gThth(thth), gPhph(phph), gTph(tph) {}
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
  std::function<double(const StateVector &)> accelT;
  std::function<double(const StateVector &)> accelR;
  std::function<double(const StateVector &)> accelTheta;
  std::function<double(const StateVector &)> accelPhi;
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
[[nodiscard]] inline StateVector geodesicRhs(const ChristoffelAccel &christoffel,
                                             const StateVector &s) noexcept {
  return StateVector{
      s.v0,
      s.v1,
      s.v2,
      s.v3,                      // dx/dlambda = v
      christoffel.accelT(s),     // dv_t/dlambda
      christoffel.accelR(s),     // dv_r/dlambda
      christoffel.accelTheta(s), // dv_theta/dlambda
      christoffel.accelPhi(s)    // dv_phi/dlambda
  };
}

/**
 * @brief Create geodesic RHS function from Christoffel acceleration
 *
 * Returns a callable suitable for rk4_step.
 */
[[nodiscard]] inline auto makeGeodesicRhs(const ChristoffelAccel &christoffel) {
  return [christoffel](const StateVector &s) -> StateVector { return geodesicRhs(christoffel, s); };
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
  return -g.gTt * s.v0 - g.gTph * s.v3;
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
[[nodiscard]] constexpr double angularMomentum(const MetricComponents &g,
                                               const StateVector &s) noexcept {
  return g.gPhph * s.v3 + g.gTph * s.v0;
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
 * @param pTheta Theta component of momentum
 * @return Carter constant Q
 */
[[nodiscard]] inline double carterConstant(double theta, double a, double e, double lz,
                                           double pTheta) noexcept {
  const double cosTheta = std::cos(theta);
  const double sinTheta = std::sin(theta);
  const double cos2 = cosTheta * cosTheta;
  const double sin2 = sinTheta * sinTheta;

  return pTheta * pTheta + cos2 * (a * a * (-e * e) + lz * lz / sin2);
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
 * @param m Black hole mass
 * @param E Energy per unit mass
 * @param L Angular momentum per unit mass
 * @return Effective potential
 */
[[nodiscard]] constexpr double effectivePotentialSchwarzschild(double r, double m, double e,
                                                               double l) noexcept {
  const double l2 = l * l;
  const double r2 = r * r;
  return (1.0 - 2.0 * m / r) * (1.0 + l2 / r2) - e * e;
}

/**
 * @brief Check circular orbit condition
 *
 * Derived from Rocq:
 *   Definition circular_orbit_condition (M L r : R) : Prop :=
 *     L^2 * (r - 3*M) = M * r^2.
 *
 * @param m Black hole mass
 * @param L Angular momentum
 * @param r Radial coordinate
 * @return Residual (should be zero for circular orbit)
 */
[[nodiscard]] constexpr double circularOrbitResidual(double m, double l, double r) noexcept {
  return l * l * (r - 3.0 * m) - m * r * r;
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
[[nodiscard]] constexpr double impactParameter(double e, double l) noexcept {
  return l / e;
}

/**
 * @brief Critical impact parameter for Schwarzschild photon capture
 *
 * Derived from Rocq:
 *   Definition critical_impact_schwarzschild (M : R) : R := 3 * sqrt(3) * M.
 *
 * Rays with b < b_crit are captured by the black hole.
 *
 * @param m Black hole mass
 * @return Critical impact parameter b_crit = 3*sqrt(3)*M
 */
[[nodiscard]] inline double criticalImpactSchwarzschild(double m) noexcept {
  return 3.0 * std::numbers::sqrt3 * m;
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
 * @param m Black hole mass
 * @param E Energy per unit mass
 * @param L Angular momentum per unit mass
 * @return Orbit classification
 */
[[nodiscard]] constexpr OrbitType classifyOrbitSchwarzschild(double m, double e,
                                                             double l) noexcept {
  const double lCrit = 4.0 * m;

  if (l < lCrit) {
    return OrbitType::Plunging;
  }
  if (e < 1.0) {
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
[[nodiscard]] constexpr double fourNorm(const MetricComponents &g, const StateVector &s) noexcept {
  return g.gTt * s.v0 * s.v0 + g.gRr * s.v1 * s.v1 + g.gThth * s.v2 * s.v2 + g.gPhph * s.v3 * s.v3 +
         2.0 * g.gTph * s.v0 * s.v3;
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
[[nodiscard]] constexpr bool isNull(const MetricComponents &g, const StateVector &s,
                                    double tolerance = 1e-10) noexcept {
  const double norm = fourNorm(g, s);
  return norm > -tolerance && norm < tolerance;
}
#define VERIFIED_IS_NULL_ALREADY_DEFINED

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
[[nodiscard]] constexpr bool isTimelike(const MetricComponents &g, const StateVector &s,
                                        double tolerance = 1e-10) noexcept {
  const double norm = fourNorm(g, s);
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
 * @param dirR Radial direction
 * @param dirTheta Theta direction
 * @param dirPhi Phi direction
 * @param g Metric components at initial position
 * @return Initial state normalized to null geodesic
 */
[[nodiscard]] inline StateVector initNullGeodesic(double r0, double theta0, double phi0,
                                                  double dirR, double dirTheta, double dirPhi,
                                                  const MetricComponents &g) noexcept {
  // Solve g_ab v^a v^b = 0 for v^t
  // g_tt v_t^2 + g_rr v_r^2 + g_thth v_th^2 + g_phph v_ph^2 = 0
  // v_t = sqrt((g_rr * v_r^2 + g_thth * v_th^2 + g_phph * v_ph^2) / (-g_tt))

  const double spatialNorm =
      g.gRr * dirR * dirR + g.gThth * dirTheta * dirTheta + g.gPhph * dirPhi * dirPhi;

  const double vT = std::sqrt(spatialNorm / (-g.gTt));

  return StateVector{
      0.0, r0,   theta0,   phi0,  // Position (t=0)
      vT,  dirR, dirTheta, dirPhi // Velocity
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
[[nodiscard]] inline StateVector initNullGeodesicEl(double r0, double theta0, double e, double l,
                                                    const MetricComponents &g) noexcept {
  // For equatorial orbits with given E, L
  // v^t = E / (-g_tt)  (from energy definition)
  // v^phi = L / g_phph (from angular momentum definition)
  // v^r from null condition

  const double vT = e / (-g.gTt);
  const double vPhi = l / g.gPhph;

  // Null condition: g_tt v_t^2 + g_rr v_r^2 + g_phph v_phi^2 = 0
  const double vRSq = -(g.gTt * vT * vT + g.gPhph * vPhi * vPhi) / g.gRr;
  const double vR = vRSq >= 0.0 ? std::sqrt(vRSq) : 0.0;

  return StateVector{0.0, r0, theta0, 0.0, vT, vR, 0.0, vPhi};
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
[[nodiscard]] constexpr bool checkEnergyConservation(const MetricComponents &g,
                                                     const StateVector &s0, const StateVector &s1,
                                                     double h) noexcept {
  const double e0 = energy(g, s0);
  const double e1 = energy(g, s1);
  const double drift = e1 - e0;
  const double bound = h * h * h * h; // O(h^4)

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
[[nodiscard]] constexpr bool checkAngularMomentumConservation(const MetricComponents &g,
                                                              const StateVector &s0,
                                                              const StateVector &s1,
                                                              double h) noexcept {
  const double l0 = angularMomentum(g, s0);
  const double l1 = angularMomentum(g, s1);
  const double drift = l1 - l0;
  const double bound = h * h * h * h; // O(h^4)

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
 * @param m Black hole mass
 * @return ChristoffelAccel for Schwarzschild geodesics
 */
inline ChristoffelAccel makeSchwarzschildChristoffel(double m) {
  return ChristoffelAccel{
      // accel_t: -Gamma^t_{tr} * v^t * v^r - Gamma^t_{rt} * v^r * v^t
      [m](const StateVector &s) -> double {
        const double r = s.x1;
        const double gammaTTr = m / (r * (r - 2.0 * m));
        return -2.0 * gammaTTr * s.v0 * s.v1;
      },

      // accel_r: sum of all Gamma^r terms
      [m](const StateVector &s) -> double {
        const double r = s.x1;
        const double theta = s.x2;
        const double sinTheta = std::sin(theta);

        const double gammaRTt = m * (r - 2.0 * m) / (r * r * r);
        const double gammaRRr = -m / (r * (r - 2.0 * m));
        const double gammaRThth = -(r - 2.0 * m);
        const double gammaRPhph = -(r - 2.0 * m) * sinTheta * sinTheta;

        return -gammaRTt * s.v0 * s.v0 - gammaRRr * s.v1 * s.v1 - gammaRThth * s.v2 * s.v2 -
               gammaRPhph * s.v3 * s.v3;
      },

      // accel_theta: -2 * Gamma^th_{r th} * v^r * v^th - Gamma^th_{phph} * v^ph^2
      [](const StateVector &s) -> double {
        const double r = s.x1;
        const double theta = s.x2;
        const double gammaThRth = 1.0 / r;
        const double gammaThPhph = -std::sin(theta) * std::cos(theta);

        return -2.0 * gammaThRth * s.v1 * s.v2 - gammaThPhph * s.v3 * s.v3;
      },

      // accel_phi: -2 * Gamma^ph_{r ph} * v^r * v^ph - 2 * Gamma^ph_{th ph} * v^th * v^ph
      [](const StateVector &s) -> double {
        const double r = s.x1;
        const double theta = s.x2;
        const double gammaPhRph = 1.0 / r;
        const double gammaPhThph = std::cos(theta) / std::sin(theta);

        return -2.0 * gammaPhRph * s.v1 * s.v3 - 2.0 * gammaPhThph * s.v2 * s.v3;
      }};
}

} // namespace verified

#endif // PHYSICS_VERIFIED_GEODESIC_HPP
