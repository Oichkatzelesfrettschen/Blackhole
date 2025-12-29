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

#include "constants.h"
#include "schwarzschild.h"
#include "kerr.h"
#include <array>
#include <cmath>
#include <functional>
#include <limits>
#include <vector>

namespace physics {

// ============================================================================
// Ray Types and Status
// ============================================================================

/**
 * @brief Status of photon ray propagation.
 */
enum class RayStatus {
  PROPAGATING,  ///< Still traveling
  ESCAPED,      ///< Escaped to infinity
  CAPTURED,     ///< Fell into black hole
  HIT_DISK,     ///< Hit accretion disk
  MAX_STEPS     ///< Exceeded maximum integration steps
};

/**
 * @brief Photon ray in curved spacetime.
 */
struct PhotonRay {
  std::array<double, 3> position;    ///< (r, θ, φ) in spherical coords [cm, rad, rad]
  std::array<double, 3> direction;   ///< Unit direction vector (normalized)
  double frequency;                   ///< Photon frequency [Hz]
  RayStatus status;                   ///< Current status

  // Conserved quantities (for Kerr)
  double energy;                      ///< E = -p_t
  double angular_momentum;            ///< L = p_φ
  double carter_constant;             ///< Q (Carter constant for Kerr)
};

/**
 * @brief Result of ray tracing.
 */
struct RayTraceResult {
  std::array<double, 3> final_position;  ///< Final position
  double total_distance;                  ///< Proper distance traveled [cm]
  double redshift;                        ///< Total gravitational redshift
  int steps_taken;                        ///< Number of integration steps
  RayStatus status;                       ///< Final status
  std::vector<std::array<double, 3>> path; ///< Path points (if recorded)
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
      : mass_(mass),
        r_s_(schwarzschild_radius(mass)),
        r_capture_(1.5 * r_s_),      // Photon sphere
        r_escape_(1000.0 * r_s_),    // Consider escaped
        step_size_(0.1 * r_s_),
        max_steps_(10000),
        record_path_(false) {}

  // Configuration
  void set_step_size(double h) { step_size_ = h; }
  void set_max_steps(int n) { max_steps_ = n; }
  void set_escape_radius(double r) { r_escape_ = r; }
  void set_record_path(bool record) { record_path_ = record; }

  /**
   * @brief Trace a photon ray through spacetime.
   *
   * @param ray Initial ray configuration
   * @return RayTraceResult with final state and path
   */
  RayTraceResult trace(const PhotonRay &ray) const {
    RayTraceResult result;
    result.steps_taken = 0;
    result.total_distance = 0;
    result.redshift = 1.0;

    // State: [r, θ, φ, dr/dλ, dθ/dλ, dφ/dλ]
    std::array<double, 6> state;
    state[0] = ray.position[0];  // r
    state[1] = ray.position[1];  // θ
    state[2] = ray.position[2];  // φ

    // Convert direction to coordinate velocities
    // For initial setup, use impact parameter formulation
    double r = state[0];
    double theta = state[1];

    // Compute impact parameter from initial direction
    double b = compute_impact_parameter(ray);

    // Initial velocities from geodesic constraints
    // E = 1 (normalized), L = b*E = b
    double L = b;
    double f = 1.0 - r_s_ / r;

    // dr/dλ from null geodesic: (dr/dλ)² = E² - V_eff
    // V_eff = (1 - r_s/r) × L²/r²
    double V_eff = f * L * L / (r * r);
    double dr_sq = 1.0 - V_eff;

    if (dr_sq < 0) {
      // Turning point - ray is purely tangential
      state[3] = 0;
    } else {
      // Determine sign from initial direction
      double dr_sign = (ray.direction[0] > 0) ? 1.0 : -1.0;
      state[3] = dr_sign * std::sqrt(dr_sq);
    }

    // dθ/dλ and dφ/dλ
    double sin_theta = std::sin(theta);
    state[4] = 0; // Assume equatorial for simplicity
    state[5] = L / (r * r * sin_theta * sin_theta);

    if (record_path_) {
      result.path.push_back({state[0], state[1], state[2]});
    }

    // RK4 integration
    while (result.steps_taken < max_steps_) {
      // Check termination conditions
      if (state[0] <= r_s_ * 1.01) {
        result.status = RayStatus::CAPTURED;
        break;
      }
      if (state[0] >= r_escape_) {
        result.status = RayStatus::ESCAPED;
        break;
      }

      // RK4 step
      auto k1 = derivatives(state);
      auto state_k2 = add_scaled(state, k1, step_size_ / 2);
      auto k2 = derivatives(state_k2);
      auto state_k3 = add_scaled(state, k2, step_size_ / 2);
      auto k3 = derivatives(state_k3);
      auto state_k4 = add_scaled(state, k3, step_size_);
      auto k4 = derivatives(state_k4);

      // Update state
      for (int i = 0; i < 6; ++i) {
        state[i] += step_size_ * (k1[i] + 2*k2[i] + 2*k3[i] + k4[i]) / 6.0;
      }

      // Keep angles in bounds
      state[1] = std::clamp(state[1], 1e-6, PI - 1e-6);
      state[2] = std::fmod(state[2], TWO_PI);
      if (state[2] < 0) state[2] += TWO_PI;

      result.total_distance += step_size_;
      ++result.steps_taken;

      if (record_path_) {
        result.path.push_back({state[0], state[1], state[2]});
      }
    }

    if (result.steps_taken >= max_steps_) {
      result.status = RayStatus::MAX_STEPS;
    }

    result.final_position = {state[0], state[1], state[2]};

    // Compute total redshift
    double r_initial = ray.position[0];
    double r_final = state[0];
    if (r_final > r_s_ && r_initial > r_s_) {
      double z_initial = 1.0 / std::sqrt(1.0 - r_s_ / r_initial);
      double z_final = 1.0 / std::sqrt(1.0 - r_s_ / r_final);
      result.redshift = z_final / z_initial;
    }

    return result;
  }

  /**
   * @brief Compute black hole shadow boundary.
   *
   * Returns impact parameters that define the shadow edge.
   *
   * @param n_points Number of points around shadow
   * @return Vector of (b_x, b_y) impact parameters
   */
  std::vector<std::array<double, 2>> compute_shadow(int n_points = 100) const {
    std::vector<std::array<double, 2>> shadow;

    // For Schwarzschild, shadow is circular with radius b_crit
    double b_crit = critical_impact_parameter(mass_);

    for (int i = 0; i < n_points; ++i) {
      double phi = TWO_PI * i / n_points;
      shadow.push_back({b_crit * std::cos(phi), b_crit * std::sin(phi)});
    }

    return shadow;
  }

private:
  double mass_;
  double r_s_;
  double r_capture_;
  double r_escape_;
  double step_size_;
  int max_steps_;
  bool record_path_;

  double compute_impact_parameter(const PhotonRay &ray) const {
    // Impact parameter from perpendicular distance to origin
    double r = ray.position[0];
    double theta = ray.position[1];

    // Direction perpendicular component
    double sin_angle = std::sqrt(1.0 - ray.direction[0] * ray.direction[0]);
    return r * sin_angle;
  }

  std::array<double, 6> derivatives(const std::array<double, 6> &state) const {
    std::array<double, 6> deriv;

    double r = state[0];
    double theta = state[1];
    double dr = state[3];
    double dtheta = state[4];
    double dphi = state[5];

    if (r <= r_s_) {
      return {0, 0, 0, 0, 0, 0};
    }

    double f = 1.0 - r_s_ / r;
    double sin_theta = std::sin(theta);
    double cos_theta = std::cos(theta);

    // Coordinate velocities
    deriv[0] = dr;
    deriv[1] = dtheta;
    deriv[2] = dphi;

    // Geodesic accelerations from Christoffel symbols
    // d²r/dλ² = -Γʳ_tt (dt/dλ)² - Γʳ_rr (dr/dλ)² - Γʳ_θθ (dθ/dλ)² - Γʳ_φφ (dφ/dλ)²
    // For null geodesics with E=1 normalization
    double Gamma_r_tt = r_s_ * f / (2.0 * r * r);
    double Gamma_r_rr = -r_s_ / (2.0 * r * r * f);
    double Gamma_r_thth = -r * f;
    double Gamma_r_phph = -r * f * sin_theta * sin_theta;

    // dt/dλ from null condition (approximately)
    double dt_dlambda = 1.0 / f;

    deriv[3] = -Gamma_r_tt * dt_dlambda * dt_dlambda
               - Gamma_r_rr * dr * dr
               - Gamma_r_thth * dtheta * dtheta
               - Gamma_r_phph * dphi * dphi;

    // d²θ/dλ² = -2 Γᶿ_rθ (dr/dλ)(dθ/dλ) - Γᶿ_φφ (dφ/dλ)²
    double Gamma_th_rth = 1.0 / r;
    double Gamma_th_phph = -sin_theta * cos_theta;

    deriv[4] = -2.0 * Gamma_th_rth * dr * dtheta
               - Gamma_th_phph * dphi * dphi;

    // d²φ/dλ² = -2 Γᵠ_rφ (dr/dλ)(dφ/dλ) - 2 Γᵠ_θφ (dθ/dλ)(dφ/dλ)
    double Gamma_ph_rph = 1.0 / r;
    double Gamma_ph_thph = cos_theta / sin_theta;

    deriv[5] = -2.0 * Gamma_ph_rph * dr * dphi
               - 2.0 * Gamma_ph_thph * dtheta * dphi;

    return deriv;
  }

  std::array<double, 6> add_scaled(const std::array<double, 6> &a,
                                    const std::array<double, 6> &b,
                                    double scale) const {
    std::array<double, 6> result;
    for (int i = 0; i < 6; ++i) {
      result[i] = a[i] + scale * b[i];
    }
    return result;
  }
};

// ============================================================================
// Camera for Image Plane
// ============================================================================

/**
 * @brief Virtual camera for rendering black hole images.
 */
struct Camera {
  std::array<double, 3> position;  ///< Camera position (r, θ, φ)
  std::array<double, 3> look_at;   ///< Point camera looks at
  double fov;                       ///< Field of view [rad]
  int width;                        ///< Image width in pixels
  int height;                       ///< Image height in pixels

  /**
   * @brief Generate ray for given pixel.
   *
   * @param px Pixel x coordinate
   * @param py Pixel y coordinate
   * @return PhotonRay from camera through pixel
   */
  PhotonRay generate_ray(int px, int py) const {
    PhotonRay ray;
    ray.position = position;
    ray.status = RayStatus::PROPAGATING;
    ray.frequency = 1e15; // Visible light

    // Convert pixel to normalized device coordinates
    double ndc_x = (2.0 * px / width - 1.0) * std::tan(fov / 2.0);
    double ndc_y = (2.0 * py / height - 1.0) * std::tan(fov / 2.0) * height / width;

    // Compute camera basis vectors
    double dx = look_at[0] - position[0];
    double dy = look_at[1] - position[1];
    double dz = look_at[2] - position[2];
    double len = std::sqrt(dx*dx + dy*dy + dz*dz);

    // Forward direction
    std::array<double, 3> forward = {dx/len, dy/len, dz/len};

    // Up vector (approximate)
    std::array<double, 3> up = {0, 0, 1};

    // Right vector
    std::array<double, 3> right = {
      forward[1] * up[2] - forward[2] * up[1],
      forward[2] * up[0] - forward[0] * up[2],
      forward[0] * up[1] - forward[1] * up[0]
    };
    double right_len = std::sqrt(right[0]*right[0] + right[1]*right[1] + right[2]*right[2]);
    if (right_len > 1e-10) {
      right[0] /= right_len;
      right[1] /= right_len;
      right[2] /= right_len;
    }

    // Recalculate up
    up = {
      right[1] * forward[2] - right[2] * forward[1],
      right[2] * forward[0] - right[0] * forward[2],
      right[0] * forward[1] - right[1] * forward[0]
    };

    // Ray direction
    ray.direction = {
      forward[0] + ndc_x * right[0] + ndc_y * up[0],
      forward[1] + ndc_x * right[1] + ndc_y * up[1],
      forward[2] + ndc_x * right[2] + ndc_y * up[2]
    };

    // Normalize
    double dir_len = std::sqrt(ray.direction[0]*ray.direction[0] +
                               ray.direction[1]*ray.direction[1] +
                               ray.direction[2]*ray.direction[2]);
    ray.direction[0] /= dir_len;
    ray.direction[1] /= dir_len;
    ray.direction[2] /= dir_len;

    return ray;
  }
};

} // namespace physics

#endif // PHYSICS_RAYTRACER_H
