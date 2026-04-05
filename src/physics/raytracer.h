/**
 * @file raytracer.h
 * @brief Photon raytracing in curved spacetime.
 *
 * Provides numerical integration of null geodesics for:
 * - Black hole shadow calculation
 * - Gravitational lensing visualization
 * - Accretion disk imaging
 * - Photon sphere visualization
 *
 * Uses 4th-order Runge-Kutta integration of geodesic equations:
 *   d²xᵘ/dλ² + Γᵘ_αβ (dxᵅ/dλ)(dxᵝ/dλ) = 0
 *
 * References:
 *   - Luminet (1979) "Image of a spherical black hole"
 *   - James et al. (2015) "Visualizing Interstellar's Wormhole"
 *
 * Cleanroom implementation based on standard GR geodesic equations.
 */

#ifndef PHYSICS_RAYTRACER_H
#define PHYSICS_RAYTRACER_H

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <vector>

#include "constants.h"
#include "geodesics.h"
#include "kerr.h"
#include "math_types.h"
#include "safe_limits.h"
#include "schwarzschild.h"

namespace physics {

// ============================================================================
// Ray Types and Status
// ============================================================================

/**
 * @brief Status of photon ray propagation.
 */
enum class RayStatus {
  PROPAGATING, ///< Still traveling
  ESCAPED,     ///< Escaped to infinity
  CAPTURED,    ///< Fell into black hole
  HitDisk,     ///< Hit accretion disk
  MaxSteps     ///< Exceeded maximum integration steps
};

/**
 * @brief Photon ray in curved spacetime.
 */
struct PhotonRay {
  math::Vec3d position{};                    ///< (r, theta, phi) in spherical coords [cm, rad, rad]
  math::Vec3d direction{};                   ///< Unit direction vector (normalized)
  double frequency = 0.0;                    ///< Photon frequency [Hz]
  RayStatus status = RayStatus::PROPAGATING; ///< Current status

  // Conserved quantities (for Kerr)
  double energy = 0.0;          ///< E = -p_t
  double angularMomentum = 0.0; ///< L = p_phi
  double carterConstant = 0.0;  ///< Q (Carter constant for Kerr)
};

/**
 * @brief Result of ray tracing.
 */
struct RayTraceResult {
  math::Vec3d finalPosition{};               ///< Final position
  double totalDistance = 0.0;                ///< Proper distance traveled [cm]
  double redshift = 0.0;                     ///< Total gravitational redshift
  int stepsTaken = 0;                        ///< Number of integration steps
  RayStatus status = RayStatus::PROPAGATING; ///< Final status
  std::vector<math::Vec3d> path;             ///< Path points (if recorded)
};

// ============================================================================
// Schwarzschild Raytracer
// ============================================================================

/**
 * @brief Raytracer for Schwarzschild spacetime.
 *
 * Uses effective potential formulation for efficiency.
 */
class SchwarzschildRaytracer {
public:
  /**
   * @brief Construct raytracer for given black hole mass.
   *
   * @param mass Black hole mass [g]
   */
  explicit SchwarzschildRaytracer(double mass)
      : mass_(mass), rS_(schwarzschildRadius(mass)), rCapture_(1.5 * rS_), // Photon sphere
        rEscape_(1000.0 * rS_),                                            // Consider escaped
        stepSize_(0.1 * rS_) {}

  // Configuration
  void setStepSize(double h) { stepSize_ = h; }
  void setMaxSteps(int n) { maxSteps_ = n; }
  void setEscapeRadius(double r) { rEscape_ = r; }
  void setRecordPath(bool record) { recordPath_ = record; }

  /**
   * @brief Trace a photon ray through spacetime.
   *
   * @param ray Initial ray configuration
   * @return RayTraceResult with final state and path
   */
  [[nodiscard]] RayTraceResult trace(const PhotonRay &ray) const {
    RayTraceResult result;
    result.stepsTaken = 0;
    result.totalDistance = 0.0;
    result.redshift = 1.0;

    // State: [r, theta, phi, dr/dlambda, dtheta/dlambda, dphi/dlambda]
    std::array<double, 6> state{};
    state.at(0) = ray.position.x; // r
    state.at(1) = ray.position.y; // theta
    state.at(2) = ray.position.z; // phi

    const double r = state.at(0);
    const double theta = state.at(1);

    // Compute impact parameter from initial direction
    const double b = computeImpactParameter(ray);
    const double angMom = b;
    const double f = 1.0 - (rS_ / r);

    // dr/dlambda from null geodesic: (dr/dlambda)^2 = E^2 - V_eff
    const double vEff = (f * angMom * angMom) / (r * r);
    const double drSq = 1.0 - vEff;

    if (drSq < 0) {
      state.at(3) = 0.0; // Turning point - ray is purely tangential
    } else {
      const double drSign = (ray.direction.x > 0) ? 1.0 : -1.0;
      state.at(3) = drSign * std::sqrt(drSq);
    }

    const double sinTheta = std::sin(theta);
    state.at(4) = 0.0; // Assume equatorial for simplicity
    state.at(5) = angMom / (r * r * sinTheta * sinTheta);

    if (recordPath_) {
      result.path.emplace_back(state.at(0), state.at(1), state.at(2));
    }

    // RK4 integration
    while (result.stepsTaken < maxSteps_) {
      if (state.at(0) <= (rS_ * 1.01)) {
        result.status = RayStatus::CAPTURED;
        break;
      }
      if (state.at(0) >= rEscape_) {
        result.status = RayStatus::ESCAPED;
        break;
      }

      const auto k1 = derivativesOf(state);
      const auto stateK2 = addScaled(state, k1, stepSize_ / 2);
      const auto k2 = derivativesOf(stateK2);
      const auto stateK3 = addScaled(state, k2, stepSize_ / 2);
      const auto k3 = derivativesOf(stateK3);
      const auto stateK4 = addScaled(state, k3, stepSize_);
      const auto k4 = derivativesOf(stateK4);

      for (std::size_t i = 0; i < state.size(); ++i) {
        state.at(i) +=
            stepSize_ * (k1.at(i) + (2.0 * k2.at(i)) + (2.0 * k3.at(i)) + k4.at(i)) / 6.0;
      }

      state.at(1) = std::clamp(state.at(1), 1e-6, PI - 1e-6);
      state.at(2) = std::fmod(state.at(2), TWO_PI);
      if (state.at(2) < 0) {
        state.at(2) += TWO_PI;
      }

      result.totalDistance += stepSize_;
      ++result.stepsTaken;

      if (recordPath_) {
        result.path.emplace_back(state.at(0), state.at(1), state.at(2));
      }
    }

    if (result.stepsTaken >= maxSteps_) {
      result.status = RayStatus::MaxSteps;
    }

    result.finalPosition = math::Vec3d(state.at(0), state.at(1), state.at(2));

    const double rInitial = ray.position.x;
    const double rFinal = state.at(0);
    if (rFinal > rS_ && rInitial > rS_) {
      const double zInitial = 1.0 / std::sqrt(1.0 - (rS_ / rInitial));
      const double zFinal = 1.0 / std::sqrt(1.0 - (rS_ / rFinal));
      result.redshift = zFinal / zInitial;
    }

    return result;
  }

  /**
   * @brief Compute black hole shadow boundary.
   *
   * Returns impact parameters that define the shadow edge.
   *
   * @param nPoints Number of points around shadow
   * @return Vector of (b_x, b_y) impact parameters
   */
  [[nodiscard]] std::vector<math::Vec2d> computeShadow(int nPoints = 100) const {
    std::vector<math::Vec2d> shadow;
    shadow.reserve(static_cast<std::size_t>(nPoints));

    const double bCrit = criticalImpactParameter(mass_);

    for (int i = 0; i < nPoints; ++i) {
      const double phi = TWO_PI * i / nPoints;
      shadow.emplace_back(bCrit * std::cos(phi), bCrit * std::sin(phi));
    }

    return shadow;
  }

private:
  double mass_;
  double rS_;
  [[maybe_unused]] double rCapture_;
  double rEscape_;
  double stepSize_;
  int maxSteps_{10000};
  bool recordPath_{false};

  [[nodiscard]] static double computeImpactParameter(const PhotonRay &ray) {
    const double r = ray.position.x;
    const double sinAngle = std::sqrt(1.0 - (ray.direction.x * ray.direction.x));
    return r * sinAngle;
  }

  [[nodiscard]] std::array<double, 6> derivativesOf(const std::array<double, 6> &state) const {
    std::array<double, 6> deriv{};

    const double r = state.at(0);
    const double theta = state.at(1);
    const double dr = state.at(3);
    const double dtheta = state.at(4);
    const double dphi = state.at(5);

    if (r <= rS_) {
      return {0.0, 0.0, 0.0, 0.0, 0.0, 0.0};
    }

    const double f = 1.0 - (rS_ / r);
    const double sinTheta = std::sin(theta);
    const double cosTheta = std::cos(theta);

    deriv.at(0) = dr;
    deriv.at(1) = dtheta;
    deriv.at(2) = dphi;

    const double gammaRTt = (rS_ * f) / (2.0 * r * r);
    const double gammaRRr = -(rS_ / (2.0 * r * r * f));
    const double gammaRThth = -(r * f);
    const double gammaRPhph = -(r * f * sinTheta * sinTheta);
    const double dtDlambda = 1.0 / f;

    deriv.at(3) = -(gammaRTt * dtDlambda * dtDlambda) - (gammaRRr * dr * dr) -
                  (gammaRThth * dtheta * dtheta) - (gammaRPhph * dphi * dphi);

    const double gammaThRth = 1.0 / r;
    const double gammaThPhph = -(sinTheta * cosTheta);

    deriv.at(4) = -(2.0 * gammaThRth * dr * dtheta) - (gammaThPhph * dphi * dphi);

    const double gammaPhRph = 1.0 / r;
    const double gammaPhThph = cosTheta / sinTheta;

    deriv.at(5) = -(2.0 * gammaPhRph * dr * dphi) - (2.0 * gammaPhThph * dtheta * dphi);

    return deriv;
  }

  [[nodiscard]] static std::array<double, 6>
  addScaled(const std::array<double, 6> &x, const std::array<double, 6> &dx, double scale) {
    std::array<double, 6> result{};
    for (std::size_t i = 0; i < result.size(); ++i) {
      result.at(i) = x.at(i) + (scale * dx.at(i));
    }
    return result;
  }
};

// ============================================================================
// Kerr Raytracer (Mino-time stepping)
// ============================================================================

/**
 * @brief Raytracer for Kerr spacetime using conserved quantities.
 *
 * This integrates the Kerr geodesic equations in Mino time using
 * the potentials from physics::Kerr. Callers provide the
 * conserved quantities (E, Lz, Q) and initial signs for r/theta.
 */
class KerrRaytracer {
public:
  KerrRaytracer(double mass, double spinParam)
      : kerr_(mass, spinParam), rS_(schwarzschildRadius(mass)), rHorizon_(kerr_.outerHorizon()),
        rEscape_(1000.0 * rS_), stepSize_(0.02 * rS_) {
    if (!safeIsfinite(rHorizon_) || rHorizon_ <= 0.0) {
      rHorizon_ = rS_;
    }
  }

  void setStepSize(double h) { stepSize_ = h; }
  void setMaxSteps(int n) { maxSteps_ = n; }
  void setEscapeRadius(double r) { rEscape_ = r; }
  void setRecordPath(bool record) { recordPath_ = record; }

  [[nodiscard]] RayTraceResult trace(const KerrGeodesicState &initial,
                                     const KerrGeodesicConsts &c) const {
    RayTraceResult result;
    result.stepsTaken = 0;
    result.totalDistance = 0.0;
    result.redshift = 1.0;
    result.status = RayStatus::PROPAGATING;

    KerrGeodesicState state = initial;

    if (recordPath_) {
      result.path.emplace_back(state.r, state.theta, state.phi);
    }

    for (int step = 0; step < maxSteps_; ++step) {
      if (state.r <= (rHorizon_ * 1.001)) {
        result.status = RayStatus::CAPTURED;
        break;
      }
      if (state.r >= rEscape_) {
        result.status = RayStatus::ESCAPED;
        break;
      }

      const KerrPotentials p = kerr_.potentials(state.r, state.theta, c);
      KerrGeodesicState next = state;
      if (p.rPot < 0.0) {
        next.signR = -next.signR;
      }
      if (p.thetaPot < 0.0) {
        next.signTheta = -next.signTheta;
      }

      next = kerr_.stepMino(next, c, stepSize_);
      state = next;

      result.totalDistance += stepSize_;
      ++result.stepsTaken;

      if (recordPath_) {
        result.path.emplace_back(state.r, state.theta, state.phi);
      }
    }

    if (result.status == RayStatus::PROPAGATING) {
      result.status = (result.stepsTaken >= maxSteps_) ? RayStatus::MaxSteps : RayStatus::ESCAPED;
    }

    result.finalPosition = math::Vec3d(state.r, state.theta, state.phi);
    if (state.r > (rHorizon_ * 1.001)) {
      result.redshift = 1.0 + kerr_.redshift(state.r, state.theta);
    }

    return result;
  }

  [[nodiscard]] RayTraceResult traceEquatorial(double r, double phi, double impactParam,
                                               double signR, double energy = 1.0) const {
    const KerrGeodesicConsts c = kerrEquatorialConsts(impactParam, energy);
    const KerrGeodesicState state = kerrEquatorialState(r, phi, signR);
    return trace(state, c);
  }

private:
  Kerr kerr_;
  double rS_;
  double rHorizon_;
  double rEscape_;
  double stepSize_;
  int maxSteps_{10000};
  bool recordPath_{false};
};

// ============================================================================
// Camera for Image Plane
// ============================================================================

/**
 * @brief Virtual camera for rendering black hole images.
 */
struct Camera {
  math::Vec3d position{}; ///< Camera position (r, theta, phi)
  math::Vec3d lookAt{};   ///< Point camera looks at
  double fov = 0.0;       ///< Field of view [rad]
  int width = 0;          ///< Image width in pixels
  int height = 0;         ///< Image height in pixels

  /**
   * @brief Generate ray for given pixel.
   *
   * @param px Pixel x coordinate
   * @param py Pixel y coordinate
   * @return PhotonRay from camera through pixel
   */
  [[nodiscard]] PhotonRay generateRay(int px, int py) const {
    PhotonRay ray;
    ray.position = position;
    ray.status = RayStatus::PROPAGATING;
    ray.frequency = 1e15; // Visible light
    ray.energy = 1.0;
    ray.angularMomentum = 0.0;
    ray.carterConstant = 0.0;

    // Convert pixel to normalized device coordinates
    const double ndcX = ((2.0 * px / width) - 1.0) * std::tan(fov / 2.0);
    const double ndcY = ((2.0 * py / height) - 1.0) * std::tan(fov / 2.0) * height / width;

    const math::Vec3d delta = lookAt - position;
    const double len = math::length(delta);
    const math::Vec3d forward = delta / len;

    math::Vec3d up(0.0, 0.0, 1.0);
    math::Vec3d right = math::cross(forward, up);
    const double rightLen = math::length(right);
    if (rightLen > 1e-10) {
      right = right / rightLen;
    }

    up = math::cross(right, forward);

    ray.direction = math::normalize(forward + (ndcX * right) + (ndcY * up));

    return ray;
  }
};

} // namespace physics

#endif // PHYSICS_RAYTRACER_H
