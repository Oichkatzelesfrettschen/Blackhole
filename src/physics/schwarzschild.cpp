/**
 * @file schwarzschild.cpp
 * @brief Implementation of Schwarzschild spacetime metric functions.
 */

#include "schwarzschild.h"
#include "constants.h"

namespace physics {

// ============================================================================
// Core Schwarzschild Functions
// ============================================================================

double schwarzschild_radius(double mass) {
  // r_s = 2GM/c²
  return TWO_G_OVER_C2 * mass;
}

double photon_sphere_radius(double mass) {
  // r_ph = 1.5 r_s = 3GM/c²
  return 1.5 * schwarzschild_radius(mass);
}

double isco_radius(double mass) {
  // r_ISCO = 3 r_s = 6GM/c²
  return 3.0 * schwarzschild_radius(mass);
}

// ============================================================================
// Metric Components
// ============================================================================

double metric_factor(double r, double r_s) {
  // f(r) = 1 - r_s/r
  return 1.0 - r_s / r;
}

double schwarzschild_g_tt(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // g_tt = -(1 - r_s/r) * c²
  return -(1.0 - r_s / r) * C2;
}

double schwarzschild_g_rr(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // g_rr = (1 - r_s/r)⁻¹
  return 1.0 / (1.0 - r_s / r);
}

// ============================================================================
// Christoffel Symbols
// ============================================================================

double christoffel_t_tr(double r, double r_s) {
  // Γ^t_tr = r_s / (2r(r - r_s))
  if (r <= r_s) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return r_s / (2.0 * r * (r - r_s));
}

double christoffel_r_tt(double r, double r_s) {
  // Γ^r_tt = c² r_s (r - r_s) / (2r³)
  if (r <= r_s) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  double r3 = r * r * r;
  return C2 * r_s * (r - r_s) / (2.0 * r3);
}

double christoffel_r_rr(double r, double r_s) {
  // Γ^r_rr = -r_s / (2r(r - r_s))
  if (r <= r_s) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return -r_s / (2.0 * r * (r - r_s));
}

double christoffel_r_thth(double r, double r_s) {
  // Γ^r_θθ = -(r - r_s)
  return -(r - r_s);
}

double christoffel_r_phph(double r, double r_s, double theta) {
  // Γ^r_φφ = -(r - r_s) sin²θ
  double sin_theta = std::sin(theta);
  return -(r - r_s) * sin_theta * sin_theta;
}

double christoffel_th_rth(double r) {
  // Γ^θ_rθ = 1/r
  if (r <= 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return 1.0 / r;
}

double christoffel_th_phph(double theta) {
  // Γ^θ_φφ = -sinθ cosθ = -sin(2θ)/2
  return -std::sin(theta) * std::cos(theta);
}

double christoffel_ph_rph(double r) {
  // Γ^φ_rφ = 1/r
  if (r <= 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return 1.0 / r;
}

double christoffel_ph_thph(double theta) {
  // Γ^φ_θφ = cotθ = cosθ/sinθ
  double sin_theta = std::sin(theta);
  if (std::abs(sin_theta) < 1e-10) {
    return std::numeric_limits<double>::quiet_NaN(); // Pole singularity
  }
  return std::cos(theta) / sin_theta;
}

// ============================================================================
// Orbital Dynamics
// ============================================================================

double gravitational_redshift(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return std::numeric_limits<double>::infinity();
  }
  // z = 1/√(1 - r_s/r) - 1
  return 1.0 / std::sqrt(1.0 - r_s / r) - 1.0;
}

double escape_velocity(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return C; // At or below horizon, escape velocity equals c
  }
  // v_esc = c * √(r_s/r)
  return C * std::sqrt(r_s / r);
}

double orbital_velocity(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // v = √(GM/r)
  return std::sqrt(G * mass / r);
}

double orbital_period(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // T = 2π √(r³/GM)
  return TWO_PI * std::sqrt(r * r * r / (G * mass));
}

double surface_gravity(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return std::numeric_limits<double>::infinity();
  }
  // κ = GM / (r² √(1 - r_s/r))
  return (G * mass) / (r * r * std::sqrt(1.0 - r_s / r));
}

// ============================================================================
// Schwarzschild Class Implementation
// ============================================================================

Schwarzschild::Schwarzschild(double mass)
    : mass_(mass), r_s_(schwarzschild_radius(mass)),
      r_ph_(photon_sphere_radius(mass)), r_isco_(isco_radius(mass)) {}

double Schwarzschild::g_tt(double r) const {
  return schwarzschild_g_tt(r, mass_);
}

double Schwarzschild::g_rr(double r) const {
  return schwarzschild_g_rr(r, mass_);
}

double Schwarzschild::redshift(double r) const {
  return gravitational_redshift(r, mass_);
}

double Schwarzschild::v_escape(double r) const {
  return escape_velocity(r, mass_);
}

} // namespace physics
