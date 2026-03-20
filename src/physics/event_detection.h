/**
 * @file event_detection.h
 * @brief Bisection refinement for horizon and photon sphere crossings.
 *
 * WHY: During geodesic integration, a ray may cross the event horizon
 * or photon sphere between two integration steps. Without event detection,
 * the crossing point is only located to within one step size h, which
 * can be 0.1-1.0 M. For photon ring subring rendering (n=1, n=2),
 * the rings are exponentially thin (delta_r/r ~ exp(-pi)), requiring
 * sub-step precision.
 *
 * WHAT: Bisection refinement that narrows the crossing interval from
 * [lambda_n, lambda_{n+1}] to within a specified tolerance. Detects:
 *   - Horizon crossing: r crosses r_+ = M + sqrt(M^2 - a^2)
 *   - Photon sphere crossing: dr/dlambda changes sign
 *   - Custom radial thresholds (ISCO, emission ring, etc.)
 *
 * HOW: Given two states bracketing a crossing, perform bisection on
 * the affine parameter lambda to locate the crossing point.
 *
 * References:
 *   - Gralla, Lupsasca, Strominger (2020) PRD -- photon ring structure
 *   - Johnson+ (2020) -- universal photon ring signatures
 */

#ifndef PHYSICS_EVENT_DETECTION_H
#define PHYSICS_EVENT_DETECTION_H

#include "constants.h"
#include <array>
#include <cmath>
#include <functional>

namespace physics {

// ============================================================================
// Event Types
// ============================================================================

enum class EventType {
  None,
  HorizonCrossing,
  PhotonSphereCrossing,
  TurningPoint,      // dr/dlambda sign change (radial turning point)
  RadialThreshold,   // r crosses a specified value
  EquatorialCrossing // theta crosses pi/2
};

/**
 * @brief Result of an event detection.
 */
struct EventResult {
  EventType type = EventType::None;
  double lambda = 0.0;       // Affine parameter at crossing
  double r = 0.0;            // Radial coordinate at crossing
  double theta = 0.0;        // Polar angle at crossing
  int n_bisections = 0;      // Number of bisection iterations used
  bool detected = false;
};

// ============================================================================
// Crossing Detectors
// ============================================================================

/**
 * @brief Detect if a radial crossing occurred between two states.
 *
 * Returns true if r crossed r_target between r0 and r1.
 *
 * @param r0 Radius at step start
 * @param r1 Radius at step end
 * @param r_target Target radius to detect crossing
 * @return true if (r0 - r_target) and (r1 - r_target) have opposite signs
 */
inline bool crossed_radius(double r0, double r1, double r_target) {
  return (r0 - r_target) * (r1 - r_target) < 0.0;
}

/**
 * @brief Detect radial turning point (dr/dlambda sign change).
 *
 * @param vr0 Radial velocity at step start
 * @param vr1 Radial velocity at step end
 * @return true if vr changed sign
 */
inline bool has_turning_point(double vr0, double vr1) {
  return vr0 * vr1 < 0.0;
}

/**
 * @brief Detect equatorial plane crossing.
 *
 * @param theta0 Polar angle at step start
 * @param theta1 Polar angle at step end
 * @return true if theta crossed pi/2
 */
inline bool crossed_equator(double theta0, double theta1) {
  return (theta0 - PI / 2.0) * (theta1 - PI / 2.0) < 0.0;
}

// ============================================================================
// Bisection Refinement
// ============================================================================

/**
 * @brief Refine a radial crossing via bisection.
 *
 * Given two states at affine parameters lambda0 and lambda1 that
 * bracket a crossing of r_target, bisect to find the crossing point
 * within tolerance.
 *
 * The integrator callback takes (lambda, state) -> new_state for
 * stepping from one affine parameter to another.
 *
 * @tparam State State vector type (must have .x1 for r component)
 * @tparam Stepper Callable: State(lambda_start, lambda_end, State)
 *
 * @param lambda0 Affine parameter at step start
 * @param lambda1 Affine parameter at step end
 * @param state0 State at lambda0
 * @param r_target Target radius
 * @param stepper Integration step function
 * @param tol_r Radial tolerance for convergence [geometric units]
 * @param max_iter Maximum bisection iterations
 * @return EventResult with crossing location
 */
template <typename State, typename Stepper>
EventResult bisect_radial_crossing(
    double lambda0, double lambda1,
    const State& state0,
    double r_target,
    Stepper&& stepper,
    double tol_r = 1e-10,
    int max_iter = 50) {

  EventResult result;
  result.type = EventType::RadialThreshold;

  double la = lambda0;
  double lb = lambda1;
  State sa = state0;

  for (int i = 0; i < max_iter; ++i) {
    double lm = 0.5 * (la + lb);
    State sm = stepper(la, lm, sa);

    double r_a = sa.x1;
    double r_m = sm.x1;

    if (std::abs(r_m - r_target) < tol_r) {
      result.detected = true;
      result.lambda = lm;
      result.r = r_m;
      result.theta = sm.x2;
      result.n_bisections = i + 1;
      return result;
    }

    if ((r_a - r_target) * (r_m - r_target) < 0.0) {
      // Crossing is in [la, lm]
      lb = lm;
    } else {
      // Crossing is in [lm, lb]
      la = lm;
      sa = sm;
    }
  }

  // Did not converge to tolerance, return best estimate
  double lm = 0.5 * (la + lb);
  State sm = stepper(la, lm, sa);
  result.detected = true;
  result.lambda = lm;
  result.r = sm.x1;
  result.theta = sm.x2;
  result.n_bisections = max_iter;
  return result;
}

/**
 * @brief Refine a turning point via bisection.
 *
 * Locates where dr/dlambda = 0 (radial velocity crosses zero).
 *
 * @tparam State State vector type (must have .v1 for dr/dlambda)
 * @tparam Stepper Callable: State(lambda_start, lambda_end, State)
 */
template <typename State, typename Stepper>
EventResult bisect_turning_point(
    double lambda0, double lambda1,
    const State& state0,
    Stepper&& stepper,
    double tol_vr = 1e-12,
    int max_iter = 50) {

  EventResult result;
  result.type = EventType::TurningPoint;

  double la = lambda0;
  double lb = lambda1;
  State sa = state0;

  for (int i = 0; i < max_iter; ++i) {
    double lm = 0.5 * (la + lb);
    State sm = stepper(la, lm, sa);

    if (std::abs(sm.v1) < tol_vr) {
      result.detected = true;
      result.lambda = lm;
      result.r = sm.x1;
      result.theta = sm.x2;
      result.n_bisections = i + 1;
      return result;
    }

    if (sa.v1 * sm.v1 < 0.0) {
      lb = lm;
    } else {
      la = lm;
      sa = sm;
    }
  }

  double lm = 0.5 * (la + lb);
  State sm = stepper(la, lm, sa);
  result.detected = true;
  result.lambda = lm;
  result.r = sm.x1;
  result.theta = sm.x2;
  result.n_bisections = max_iter;
  return result;
}

/**
 * @brief Count the number of half-orbits completed by a photon.
 *
 * A photon completes a half-orbit each time it passes through
 * a radial turning point. The subring index n counts the number
 * of half-orbits before the photon escapes or is absorbed.
 *
 *   n = 0: direct image (no turning point)
 *   n = 1: one half-orbit (first photon ring)
 *   n = 2: two half-orbits (second photon ring)
 *
 * @param turning_point_count Number of radial turning points detected
 * @return Photon ring subring index n
 */
inline int photon_subring_index(int turning_point_count) {
  return turning_point_count;
}

} // namespace physics

#endif // PHYSICS_EVENT_DETECTION_H
