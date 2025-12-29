/**
 * @file kerr.h
 * @brief Kerr spacetime metric for rotating black holes.
 *
 * The Kerr metric describes spacetime around a rotating, uncharged black hole:
 *
 *   ds² = -(1 - r_s r/Σ)c²dt² - (2r_s r a sin²θ/Σ) c dt dφ
 *       + (Σ/Δ)dr² + Σ dθ² + (r² + a² + r_s r a² sin²θ/Σ)sin²θ dφ²
 *
 * where:
 *   a = J/(Mc) = spin parameter [cm]
 *   Σ = r² + a² cos²θ
 *   Δ = r² - r_s r + a²
 *   r_s = 2GM/c² = Schwarzschild radius
 *
 * Key features:
 *   - Reduces to Schwarzschild when a = 0
 *   - Has inner (r_-) and outer (r_+) horizons
 *   - Ergosphere where frame-dragging is mandatory
 *   - Spin-dependent ISCO and photon orbits
 *
 * References:
 *   - Bardeen, Press, Teukolsky (1972) for ISCO formulas
 *   - Chandrasekhar "Mathematical Theory of Black Holes"
 *
 * Cleanroom implementation based on standard GR textbook formulas.
 */

#ifndef PHYSICS_KERR_H
#define PHYSICS_KERR_H

#include "constants.h"
#include "schwarzschild.h"
#include <cmath>
#include <limits>

namespace physics {

// ============================================================================
// Kerr Metric Functions
// ============================================================================

/**
 * @brief Compute spin parameter from angular momentum.
 *
 * a = J/(Mc) where J is angular momentum
 *
 * @param J Angular momentum [g cm²/s]
 * @param mass Black hole mass [g]
 * @return Spin parameter a [cm]
 */
inline double spin_parameter(double J, double mass) {
  return J / (mass * C);
}

/**
 * @brief Compute dimensionless spin from spin parameter.
 *
 * a* = a/M = Jc/(GM²) where 0 ≤ |a*| ≤ 1
 *
 * @param a Spin parameter [cm]
 * @param mass Black hole mass [g]
 * @return Dimensionless spin a* (unitless)
 */
inline double dimensionless_spin(double a, double mass) {
  double M = G * mass / C2; // Geometric mass in cm
  return a / M;
}

/**
 * @brief Compute Kerr metric Σ function.
 *
 * Σ = r² + a² cos²θ
 *
 * @param r Radial coordinate [cm]
 * @param a Spin parameter [cm]
 * @param theta Polar angle [rad]
 * @return Σ [cm²]
 */
inline double kerr_sigma(double r, double a, double theta) {
  double cos_theta = std::cos(theta);
  return r * r + a * a * cos_theta * cos_theta;
}

/**
 * @brief Compute Kerr metric Δ function.
 *
 * Δ = r² - r_s r + a² = (r - r_+)(r - r_-)
 *
 * Horizons exist where Δ = 0.
 *
 * @param r Radial coordinate [cm]
 * @param a Spin parameter [cm]
 * @param r_s Schwarzschild radius [cm]
 * @return Δ [cm²]
 */
inline double kerr_delta(double r, double a, double r_s) {
  return r * r - r_s * r + a * a;
}

// ============================================================================
// Horizon Radii
// ============================================================================

/**
 * @brief Compute outer (event) horizon radius.
 *
 * r_+ = (r_s/2) + √((r_s/2)² - a²) = M + √(M² - a²)
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Outer horizon radius [cm], NaN if a > M (naked singularity)
 */
inline double kerr_outer_horizon(double mass, double a) {
  double M = G * mass / C2; // Geometric mass
  double discriminant = M * M - a * a;
  if (discriminant < 0) {
    return std::numeric_limits<double>::quiet_NaN(); // Naked singularity
  }
  return M + std::sqrt(discriminant);
}

/**
 * @brief Compute inner (Cauchy) horizon radius.
 *
 * r_- = (r_s/2) - √((r_s/2)² - a²) = M - √(M² - a²)
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Inner horizon radius [cm], NaN if a > M
 */
inline double kerr_inner_horizon(double mass, double a) {
  double M = G * mass / C2;
  double discriminant = M * M - a * a;
  if (discriminant < 0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return M - std::sqrt(discriminant);
}

// ============================================================================
// Ergosphere
// ============================================================================

/**
 * @brief Compute ergosphere outer boundary.
 *
 * r_ergo(θ) = M + √(M² - a² cos²θ)
 *
 * Inside the ergosphere, no static observer can exist.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @param theta Polar angle [rad]
 * @return Ergosphere radius [cm]
 */
inline double ergosphere_radius(double mass, double a, double theta) {
  double M = G * mass / C2;
  double cos_theta = std::cos(theta);
  double discriminant = M * M - a * a * cos_theta * cos_theta;
  if (discriminant < 0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return M + std::sqrt(discriminant);
}

// ============================================================================
// ISCO (Innermost Stable Circular Orbit) - Bardeen-Press-Teukolsky 1972
// ============================================================================

/**
 * @brief Compute ISCO radius for equatorial orbits.
 *
 * Uses the Bardeen-Press-Teukolsky (1972) formula.
 *
 * r_ISCO/M = 3 + Z2 ∓ √((3 - Z1)(3 + Z1 + 2Z2))
 *
 * where:
 *   Z1 = 1 + (1 - a*²)^(1/3) * ((1 + a*)^(1/3) + (1 - a*)^(1/3))
 *   Z2 = √(3a*² + Z1²)
 *
 * Minus sign for prograde (co-rotating), plus for retrograde.
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @param prograde true for prograde orbit, false for retrograde
 * @return ISCO radius [cm]
 */
inline double kerr_isco_radius(double mass, double a, bool prograde = true) {
  double M = G * mass / C2; // Geometric mass in cm
  double a_star = a / M;    // Dimensionless spin

  // Clamp to valid range
  if (std::abs(a_star) > 1.0) {
    a_star = (a_star > 0) ? 1.0 : -1.0;
  }

  // For retrograde, use negative spin convention
  double a_eff = prograde ? a_star : -a_star;

  // BPT formula
  double one_minus_a2 = 1.0 - a_eff * a_eff;
  double cbrt_factor = std::cbrt(one_minus_a2);
  double cbrt_plus = std::cbrt(1.0 + a_eff);
  double cbrt_minus = std::cbrt(1.0 - a_eff);

  double Z1 = 1.0 + cbrt_factor * (cbrt_plus + cbrt_minus);
  double Z2 = std::sqrt(3.0 * a_eff * a_eff + Z1 * Z1);

  double sqrt_term = std::sqrt((3.0 - Z1) * (3.0 + Z1 + 2.0 * Z2));

  // Prograde: minus sign; Retrograde: plus sign
  double r_isco_over_M = 3.0 + Z2 - sqrt_term;

  return r_isco_over_M * M;
}

// ============================================================================
// Photon Orbits
// ============================================================================

/**
 * @brief Compute prograde photon orbit radius.
 *
 * r_ph = 2M(1 + cos(2/3 * arccos(-a*)))
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Prograde photon orbit radius [cm]
 */
inline double kerr_photon_orbit_prograde(double mass, double a) {
  double M = G * mass / C2;
  double a_star = std::min(std::abs(a / M), 1.0);
  if (a < 0)
    a_star = -a_star;

  double angle = (2.0 / 3.0) * std::acos(-a_star);
  return 2.0 * M * (1.0 + std::cos(angle));
}

/**
 * @brief Compute retrograde photon orbit radius.
 *
 * r_ph = 2M(1 + cos(2/3 * arccos(a*)))
 *
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Retrograde photon orbit radius [cm]
 */
inline double kerr_photon_orbit_retrograde(double mass, double a) {
  double M = G * mass / C2;
  double a_star = std::min(std::abs(a / M), 1.0);
  if (a < 0)
    a_star = -a_star;

  double angle = (2.0 / 3.0) * std::acos(a_star);
  return 2.0 * M * (1.0 + std::cos(angle));
}

// ============================================================================
// Frame Dragging (Lense-Thirring Effect)
// ============================================================================

/**
 * @brief Compute frame-dragging angular velocity.
 *
 * ω = (2Ma r c) / (Σ(r² + a²) + 2Ma²r sin²θ)
 *
 * This is the angular velocity at which local inertial frames are dragged.
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Frame-dragging angular velocity [rad/s]
 */
inline double frame_dragging_omega(double r, double theta, double mass, double a) {
  double M = G * mass / C2;
  double sigma = kerr_sigma(r, a, theta);
  double sin_theta = std::sin(theta);
  double sin2_theta = sin_theta * sin_theta;

  double r2_plus_a2 = r * r + a * a;
  double numerator = 2.0 * M * a * r * C;
  double denominator = sigma * r2_plus_a2 + 2.0 * M * a * a * r * sin2_theta;

  if (denominator < 1e-30) {
    return 0.0;
  }

  return numerator / denominator;
}

/**
 * @brief Compute gravitational time dilation for Kerr.
 *
 * For a zero-angular-momentum observer (ZAMO):
 * dτ/dt = √(-g_tt - 2ω g_tφ - ω² g_φφ) / c
 *
 * Simplified at equator (θ = π/2):
 * dτ/dt = √(Δ Σ) / (r² + a² + 2Ma²/r) / c
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Time dilation factor dτ/dt
 */
inline double kerr_time_dilation(double r, double theta, double mass, double a) {
  double r_s = schwarzschild_radius(mass);
  double sigma = kerr_sigma(r, a, theta);
  double delta = kerr_delta(r, a, r_s);

  if (delta <= 0 || sigma <= 0) {
    return 0.0; // Inside horizon
  }

  double sin_theta = std::sin(theta);
  double sin2_theta = sin_theta * sin_theta;
  double r2_plus_a2 = r * r + a * a;

  // g_tt component
  double g_tt = -(1.0 - r_s * r / sigma);

  // For static observer (not ZAMO), simpler formula
  return std::sqrt(-g_tt);
}

// ============================================================================
// Kerr Redshift
// ============================================================================

/**
 * @brief Compute gravitational redshift for Kerr spacetime.
 *
 * For a photon emitted at radius r and observed at infinity:
 * 1 + z = 1/√(-g_tt) = 1/√(1 - r_s r/Σ)
 *
 * @param r Radial coordinate [cm]
 * @param theta Polar angle [rad]
 * @param mass Black hole mass [g]
 * @param a Spin parameter [cm]
 * @return Redshift z
 */
inline double kerr_redshift(double r, double theta, double mass, double a) {
  double r_s = schwarzschild_radius(mass);
  double sigma = kerr_sigma(r, a, theta);

  double factor = 1.0 - r_s * r / sigma;
  if (factor <= 0) {
    return std::numeric_limits<double>::infinity();
  }

  return 1.0 / std::sqrt(factor) - 1.0;
}

// ============================================================================
// Convenience Class
// ============================================================================

/**
 * @brief Kerr black hole spacetime.
 *
 * Encapsulates rotating black hole calculations.
 */
class Kerr {
public:
  /**
   * @brief Construct Kerr spacetime.
   *
   * @param mass Black hole mass [g]
   * @param spin_param Spin parameter a [cm], or use dimensionless a* with second
   * constructor
   */
  explicit Kerr(double mass, double spin_param = 0.0)
      : mass_(mass), a_(spin_param) {
    M_ = G * mass / C2;
    r_s_ = schwarzschild_radius(mass);
    a_star_ = a_ / M_;

    // Clamp to valid spin
    if (std::abs(a_star_) > 1.0) {
      a_star_ = (a_star_ > 0) ? 0.998 : -0.998; // Thorne limit
      a_ = a_star_ * M_;
    }

    r_plus_ = kerr_outer_horizon(mass, a_);
    r_minus_ = kerr_inner_horizon(mass, a_);
    r_isco_pro_ = kerr_isco_radius(mass, a_, true);
    r_isco_ret_ = kerr_isco_radius(mass, a_, false);
    r_ph_pro_ = kerr_photon_orbit_prograde(mass, a_);
    r_ph_ret_ = kerr_photon_orbit_retrograde(mass, a_);
  }

  /**
   * @brief Construct from dimensionless spin a*.
   */
  static Kerr from_dimensionless_spin(double mass, double a_star) {
    double M = G * mass / C2;
    return Kerr(mass, a_star * M);
  }

  // Accessors
  double mass() const { return mass_; }
  double spin() const { return a_; }
  double dimensionless_spin() const { return a_star_; }
  double outer_horizon() const { return r_plus_; }
  double inner_horizon() const { return r_minus_; }
  double isco_prograde() const { return r_isco_pro_; }
  double isco_retrograde() const { return r_isco_ret_; }
  double photon_orbit_prograde() const { return r_ph_pro_; }
  double photon_orbit_retrograde() const { return r_ph_ret_; }

  // Metric functions at point
  double sigma(double r, double theta) const { return kerr_sigma(r, a_, theta); }
  double delta(double r) const { return kerr_delta(r, a_, r_s_); }
  double ergosphere(double theta) const { return ergosphere_radius(mass_, a_, theta); }
  double frame_dragging(double r, double theta) const {
    return frame_dragging_omega(r, theta, mass_, a_);
  }
  double redshift(double r, double theta) const {
    return kerr_redshift(r, theta, mass_, a_);
  }

  // Check if point is outside horizon
  bool is_exterior(double r) const { return r > r_plus_; }

  // Check if point is in ergosphere
  bool in_ergosphere(double r, double theta) const {
    return r < ergosphere(theta) && r > r_plus_;
  }

private:
  double mass_;      // Mass [g]
  double a_;         // Spin parameter [cm]
  double a_star_;    // Dimensionless spin
  double M_;         // Geometric mass [cm]
  double r_s_;       // Schwarzschild radius [cm]
  double r_plus_;    // Outer horizon [cm]
  double r_minus_;   // Inner horizon [cm]
  double r_isco_pro_; // Prograde ISCO [cm]
  double r_isco_ret_; // Retrograde ISCO [cm]
  double r_ph_pro_;  // Prograde photon orbit [cm]
  double r_ph_ret_;  // Retrograde photon orbit [cm]
};

} // namespace physics

#endif // PHYSICS_KERR_H
