/**
 * @file schwarzschild.h
 * @brief Schwarzschild spacetime metric functions.
 *
 * The Schwarzschild metric describes spacetime around a non-rotating,
 * uncharged, spherically symmetric mass:
 *
 *   ds² = -(1 - r_s/r)c²dt² + (1 - r_s/r)⁻¹dr² + r²dΩ²
 *
 * where r_s = 2GM/c² is the Schwarzschild radius.
 *
 * Cleanroom implementation based on standard GR textbook formulas.
 */

#ifndef PHYSICS_SCHWARZSCHILD_H
#define PHYSICS_SCHWARZSCHILD_H

#include <cmath>
#include <limits>

namespace physics {

// ============================================================================
// Core Schwarzschild Functions
// ============================================================================

/**
 * @brief Compute Schwarzschild radius r_s = 2GM/c².
 *
 * @param mass Black hole mass [g]
 * @return Schwarzschild radius [cm]
 */
double schwarzschild_radius(double mass);

/**
 * @brief Compute photon sphere radius r_ph = 1.5 r_s = 3GM/c².
 *
 * The photon sphere is where circular null orbits can exist.
 * Light at this radius orbits the black hole.
 *
 * @param mass Black hole mass [g]
 * @return Photon sphere radius [cm]
 */
double photon_sphere_radius(double mass);

/**
 * @brief Compute Innermost Stable Circular Orbit (ISCO) radius.
 *
 * For Schwarzschild: r_ISCO = 6GM/c² = 3 r_s
 *
 * @param mass Black hole mass [g]
 * @return ISCO radius [cm]
 */
double isco_radius(double mass);

// ============================================================================
// Metric Components
// ============================================================================

/**
 * @brief Schwarzschild metric component g_tt.
 *
 * g_tt = -(1 - r_s/r) * c²
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return g_tt metric component, NaN if r <= r_s
 */
double schwarzschild_g_tt(double r, double mass);

/**
 * @brief Schwarzschild metric component g_rr.
 *
 * g_rr = (1 - r_s/r)⁻¹
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return g_rr metric component, NaN if r <= r_s
 */
double schwarzschild_g_rr(double r, double mass);

/**
 * @brief Metric factor f(r) = 1 - r_s/r.
 *
 * This is the common factor appearing in the Schwarzschild metric.
 *
 * @param r Radial coordinate [cm]
 * @param r_s Schwarzschild radius [cm]
 * @return f(r) = 1 - r_s/r
 */
double metric_factor(double r, double r_s);

// ============================================================================
// Christoffel Symbols
// ============================================================================

/**
 * @brief Non-zero Christoffel symbols for Schwarzschild metric.
 *
 * In Schwarzschild coordinates (t, r, θ, φ), the non-zero symbols are:
 *
 *   Γ^t_tr = Γ^t_rt = r_s / (2r(r - r_s))
 *   Γ^r_tt = c² r_s (r - r_s) / (2r³)
 *   Γ^r_rr = -r_s / (2r(r - r_s))
 *   Γ^r_θθ = -(r - r_s)
 *   Γ^r_φφ = -(r - r_s) sin²θ
 *   Γ^θ_rθ = Γ^θ_θr = 1/r
 *   Γ^θ_φφ = -sinθ cosθ
 *   Γ^φ_rφ = Γ^φ_φr = 1/r
 *   Γ^φ_θφ = Γ^φ_φθ = cotθ
 */

/// Γ^t_tr = Γ^t_rt: time-radius mixing
double christoffel_t_tr(double r, double r_s);

/// Γ^r_tt: radial acceleration from time flow
double christoffel_r_tt(double r, double r_s);

/// Γ^r_rr: radial self-coupling
double christoffel_r_rr(double r, double r_s);

/// Γ^r_θθ: radial acceleration from theta motion
double christoffel_r_thth(double r, double r_s);

/// Γ^r_φφ: radial acceleration from phi motion
double christoffel_r_phph(double r, double r_s, double theta);

/// Γ^θ_rθ = 1/r: theta change from radial motion
double christoffel_th_rth(double r);

/// Γ^θ_φφ = -sinθ cosθ: theta acceleration from phi motion
double christoffel_th_phph(double theta);

/// Γ^φ_rφ = 1/r: phi change from radial motion
double christoffel_ph_rph(double r);

/// Γ^φ_θφ = cotθ: phi change from theta motion
double christoffel_ph_thph(double theta);

// ============================================================================
// Orbital Dynamics
// ============================================================================

/**
 * @brief Compute gravitational redshift factor.
 *
 * z = 1/√(1 - r_s/r) - 1
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Redshift z, infinity if r <= r_s
 */
double gravitational_redshift(double r, double mass);

/**
 * @brief Compute escape velocity at radius r.
 *
 * v_esc = c * √(r_s/r) = √(2GM/r)
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Escape velocity [cm/s], c if r <= r_s
 */
double escape_velocity(double r, double mass);

/**
 * @brief Compute orbital velocity for circular orbit.
 *
 * v = √(GM/r)
 *
 * @param r Orbital radius [cm]
 * @param mass Black hole mass [g]
 * @return Orbital velocity [cm/s], NaN if r <= r_s
 */
double orbital_velocity(double r, double mass);

/**
 * @brief Compute coordinate orbital period for circular orbit.
 *
 * T = 2π √(r³/GM)
 *
 * @param r Orbital radius [cm]
 * @param mass Black hole mass [g]
 * @return Orbital period [s], NaN if r <= r_s
 */
double orbital_period(double r, double mass);

/**
 * @brief Compute surface gravity at radius r.
 *
 * κ = GM / (r² √(1 - r_s/r))
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Surface gravity [cm/s²], infinity if r <= r_s
 */
double surface_gravity(double r, double mass);

// ============================================================================
// Convenience Class
// ============================================================================

/**
 * @brief Schwarzschild black hole spacetime.
 *
 * Provides a convenient object-oriented interface for metric calculations.
 */
class Schwarzschild {
public:
  /**
   * @brief Construct Schwarzschild spacetime for given mass.
   *
   * @param mass Black hole mass [g]
   */
  explicit Schwarzschild(double mass);

  /// Black hole mass [g]
  double mass() const { return mass_; }

  /// Event horizon radius [cm]
  double horizon() const { return r_s_; }

  /// Photon sphere radius [cm]
  double photon_sphere() const { return r_ph_; }

  /// ISCO radius [cm]
  double isco() const { return r_isco_; }

  /// Metric component g_tt at radius r
  double g_tt(double r) const;

  /// Metric component g_rr at radius r
  double g_rr(double r) const;

  /// Gravitational redshift at radius r
  double redshift(double r) const;

  /// Escape velocity at radius r
  double v_escape(double r) const;

  /// Check if radius is outside horizon
  bool is_exterior(double r) const { return r > r_s_; }

private:
  double mass_;   // Black hole mass [g]
  double r_s_;    // Schwarzschild radius [cm]
  double r_ph_;   // Photon sphere radius [cm]
  double r_isco_; // ISCO radius [cm]
};

} // namespace physics

#endif // PHYSICS_SCHWARZSCHILD_H
