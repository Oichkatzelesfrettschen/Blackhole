/**
 * @file schwarzschild.h
 * @brief Schwarzschild spacetime metric functions.
 *
 * The Schwarzschild metric describes spacetime around a non-rotating,
 * uncharged, spherically symmetric mass:
 *
 *   ds^2 = -(1 - r_s/r)c^2 dt^2 + (1 - r_s/r)^-1 dr^2 + r^2 dOmega^2
 *
 * where r_s = 2GM/c^2 is the Schwarzschild radius.
 *
 * Cleanroom implementation based on standard GR textbook formulas.
 */

#ifndef PHYSICS_SCHWARZSCHILD_H
#define PHYSICS_SCHWARZSCHILD_H

namespace physics {

// ============================================================================
// Core Schwarzschild Functions
// ============================================================================

/**
 * @brief Compute Schwarzschild radius r_s = 2GM/c^2.
 *
 * @param mass Black hole mass [g]
 * @return Schwarzschild radius [cm]
 */
[[nodiscard]] double schwarzschildRadius(double mass);

/**
 * @brief Compute photon sphere radius r_ph = 1.5 r_s = 3GM/c^2.
 *
 * The photon sphere is where circular null orbits can exist.
 * Light at this radius orbits the black hole.
 *
 * @param mass Black hole mass [g]
 * @return Photon sphere radius [cm]
 */
[[nodiscard]] double photonSphereRadius(double mass);

/**
 * @brief Compute Innermost Stable Circular Orbit (ISCO) radius.
 *
 * For Schwarzschild: r_ISCO = 6GM/c^2 = 3 r_s
 *
 * @param mass Black hole mass [g]
 * @return ISCO radius [cm]
 */
[[nodiscard]] double iscoRadius(double mass);

// ============================================================================
// Metric Components
// ============================================================================

/**
 * @brief Schwarzschild metric component g_tt.
 *
 * g_tt = -(1 - r_s/r) * c^2
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return g_tt metric component, NaN if r <= r_s
 */
[[nodiscard]] double schwarzschildGTt(double r, double mass);

/**
 * @brief Schwarzschild metric component g_rr.
 *
 * g_rr = (1 - r_s/r)^-1
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return g_rr metric component, NaN if r <= r_s
 */
[[nodiscard]] double schwarzschildGRr(double r, double mass);

/**
 * @brief Metric factor f(r) = 1 - r_s/r.
 *
 * This is the common factor appearing in the Schwarzschild metric.
 *
 * @param r Radial coordinate [cm]
 * @param rS Schwarzschild radius [cm]
 * @return f(r) = 1 - rS/r
 */
[[nodiscard]] double metricFactor(double r, double rS);

// ============================================================================
// Christoffel Symbols
// ============================================================================

/**
 * @brief Non-zero Christoffel symbols for Schwarzschild metric.
 *
 * In Schwarzschild coordinates (t, r, theta, phi), the non-zero symbols are:
 *
 *   Gamma^t_tr = r_s / (2r(r - r_s))
 *   Gamma^r_tt = c^2 r_s (r - r_s) / (2r^3)
 *   Gamma^r_rr = -r_s / (2r(r - r_s))
 *   Gamma^r_thth = -(r - r_s)
 *   Gamma^r_phph = -(r - r_s) sin^2(theta)
 *   Gamma^th_rth = 1/r
 *   Gamma^th_phph = -sin(theta) cos(theta)
 *   Gamma^ph_rph = 1/r
 *   Gamma^ph_thph = cot(theta)
 */

/// Gamma^t_tr: time-radius mixing
[[nodiscard]] double christoffelTTr(double r, double rS);

/// Gamma^r_tt: radial acceleration from time flow
[[nodiscard]] double christoffelRTt(double r, double rS);

/// Gamma^r_rr: radial self-coupling
[[nodiscard]] double christoffelRRr(double r, double rS);

/// Gamma^r_thth: radial acceleration from theta motion
[[nodiscard]] double christoffelRThth(double r, double rS);

/// Gamma^r_phph: radial acceleration from phi motion
[[nodiscard]] double christoffelRPhph(double r, double rS, double theta);

/// Gamma^th_rth = 1/r: theta change from radial motion
[[nodiscard]] double christoffelThRth(double r);

/// Gamma^th_phph = -sin(theta) cos(theta): theta acceleration from phi motion
[[nodiscard]] double christoffelThPhph(double theta);

/// Gamma^ph_rph = 1/r: phi change from radial motion
[[nodiscard]] double christoffelPhRph(double r);

/// Gamma^ph_thph = cot(theta): phi change from theta motion
[[nodiscard]] double christoffelPhThph(double theta);

// ============================================================================
// Orbital Dynamics
// ============================================================================

/**
 * @brief Compute gravitational redshift factor.
 *
 * z = 1/sqrt(1 - r_s/r) - 1
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Redshift z, infinity if r <= r_s
 */
[[nodiscard]] double gravitationalRedshift(double r, double mass);

/**
 * @brief Compute escape velocity at radius r.
 *
 * v_esc = c * sqrt(r_s/r) = sqrt(2GM/r)
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Escape velocity [cm/s], c if r <= r_s
 */
[[nodiscard]] double escapeVelocity(double r, double mass);

/**
 * @brief Compute orbital velocity for circular orbit.
 *
 * v = sqrt(GM/r)
 *
 * @param r Orbital radius [cm]
 * @param mass Black hole mass [g]
 * @return Orbital velocity [cm/s], NaN if r <= r_s
 */
[[nodiscard]] double orbitalVelocity(double r, double mass);

/**
 * @brief Compute coordinate orbital period for circular orbit.
 *
 * T = 2*pi * sqrt(r^3/GM)
 *
 * @param r Orbital radius [cm]
 * @param mass Black hole mass [g]
 * @return Orbital period [s], NaN if r <= r_s
 */
[[nodiscard]] double orbitalPeriod(double r, double mass);

/**
 * @brief Compute surface gravity at radius r.
 *
 * kappa = GM / (r^2 * sqrt(1 - r_s/r))
 *
 * @param r Radial coordinate [cm]
 * @param mass Black hole mass [g]
 * @return Surface gravity [cm/s^2], infinity if r <= r_s
 */
[[nodiscard]] double surfaceGravity(double r, double mass);

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
  [[nodiscard]] double mass() const { return mass_; }

  /// Event horizon radius [cm]
  [[nodiscard]] double horizon() const { return r_s_; }

  /// Photon sphere radius [cm]
  [[nodiscard]] double photonSphere() const { return r_ph_; }

  /// ISCO radius [cm]
  [[nodiscard]] double isco() const { return r_isco_; }

  /// Metric component g_tt at radius r
  [[nodiscard]] double gTt(double r) const;

  /// Metric component g_rr at radius r
  [[nodiscard]] double gRr(double r) const;

  /// Gravitational redshift at radius r
  [[nodiscard]] double redshift(double r) const;

  /// Escape velocity at radius r
  [[nodiscard]] double vEscape(double r) const;

  /// Check if radius is outside horizon
  [[nodiscard]] bool isExterior(double r) const { return r > r_s_; }

private:
  double mass_;   // Black hole mass [g]
  double r_s_;    // Schwarzschild radius [cm]
  double r_ph_;   // Photon sphere radius [cm]
  double r_isco_; // ISCO radius [cm]
};

} // namespace physics

#endif // PHYSICS_SCHWARZSCHILD_H
