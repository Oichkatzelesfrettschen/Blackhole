/**
 * @file geodesics.cpp
 * @brief Implementation of geodesic calculations.
 */

#include "geodesics.h"
#include "constants.h"
#include "schwarzschild.h"

namespace physics {

// ============================================================================
// Light Deflection
// ============================================================================

double gravitational_deflection(double impact_param, double mass) {
  // δφ = 4GM/(bc²)
  return FOUR_G_OVER_C2 * mass / impact_param;
}

double critical_impact_parameter(double mass) {
  // b_crit = (3√3/2) r_s
  // This comes from the condition that the photon orbit is unstable
  double r_s = schwarzschild_radius(mass);
  return (3.0 * std::sqrt(3.0) / 2.0) * r_s;
}

bool is_photon_captured(double impact_param, double mass) {
  return impact_param < critical_impact_parameter(mass);
}

// ============================================================================
// Time Effects
// ============================================================================

double shapiro_delay(double r1, double r2, double impact_param, double mass) {
  // Δt = (2GM/c³) ln((r₁ + r₂ + d)/(r₁ + r₂ - d))
  // where d = √((r₁ + r₂)² - b²)
  double sum = r1 + r2;
  double d = std::sqrt(sum * sum - impact_param * impact_param);
  double factor = 2.0 * G * mass / (C * C * C);
  return factor * std::log((sum + d) / (sum - d));
}

double time_dilation_factor(double r, double mass) {
  double r_s = schwarzschild_radius(mass);
  if (r <= r_s) {
    return 0.0; // At or below horizon
  }
  // dτ/dt = √(1 - r_s/r)
  return std::sqrt(1.0 - r_s / r);
}

// ============================================================================
// Ray Tracing Helpers
// ============================================================================

double null_effective_potential(double r, double r_s) {
  // V_eff(r) = (1 - r_s/r) / r²
  return (1.0 - r_s / r) / (r * r);
}

double null_radial_derivative_squared(double r, double r_s, double b) {
  // (dr/dφ)² = r⁴/b² - r²(1 - r_s/r)
  double r2 = r * r;
  double r4 = r2 * r2;
  return r4 / (b * b) - r2 * (1.0 - r_s / r);
}

double photon_turning_point(double impact_param, double mass) {
  double r_s = schwarzschild_radius(mass);
  double b_crit = critical_impact_parameter(mass);

  // If b < b_crit, photon is captured - no turning point
  if (impact_param <= b_crit) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  // For b > b_crit, solve r⁴/b² = r²(1 - r_s/r)
  // This gives r³ - b²r + b²r_s = 0
  // Use numerical approximation or analytic solution

  // For large b >> r_s, turning point ≈ b (straight line)
  // For b near b_crit, need more careful calculation

  // Simple approximation: r_turn ≈ b for b >> b_crit
  // More accurate: iterative refinement
  double r_turn = impact_param;
  for (int i = 0; i < 10; ++i) {
    double r3 = r_turn * r_turn * r_turn;
    double f = r3 - impact_param * impact_param * r_turn +
               impact_param * impact_param * r_s;
    double df = 3.0 * r_turn * r_turn - impact_param * impact_param;
    if (std::abs(df) < 1e-20) {
      break;
    }
    r_turn -= f / df;
    if (r_turn < r_s) {
      r_turn = r_s * 1.001; // Clamp above horizon
    }
  }

  return r_turn;
}

// ============================================================================
// Coordinate Transformations
// ============================================================================

void schwarzschild_to_cartesian(double r, double theta, double phi, double &x,
                                double &y, double &z) {
  double sin_theta = std::sin(theta);
  x = r * sin_theta * std::cos(phi);
  y = r * sin_theta * std::sin(phi);
  z = r * std::cos(theta);
}

void cartesian_to_schwarzschild(double x, double y, double z, double &r,
                                double &theta, double &phi) {
  r = std::sqrt(x * x + y * y + z * z);
  if (r < 1e-20) {
    theta = 0.0;
    phi = 0.0;
    return;
  }
  theta = std::acos(z / r);
  phi = std::atan2(y, x);
}

} // namespace physics
