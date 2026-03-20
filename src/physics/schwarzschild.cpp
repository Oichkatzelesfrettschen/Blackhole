/**
 * @file schwarzschild.cpp
 * @brief Implementation of Schwarzschild spacetime metric functions.
 */

#include "schwarzschild.h"
#include "constants.h"
#include "safe_limits.h"

#include <cmath>
#include <limits>

namespace physics {

// ============================================================================
// Core Schwarzschild Functions
// ============================================================================

double schwarzschildRadius(double mass) {
  // r_s = 2GM/c^2
  return TWO_G_OVER_C2 * mass;
}

double photonSphereRadius(double mass) {
  // r_ph = 1.5 r_s = 3GM/c^2
  return 1.5 * schwarzschildRadius(mass);
}

double iscoRadius(double mass) {
  // r_ISCO = 3 r_s = 6GM/c^2
  return 3.0 * schwarzschildRadius(mass);
}

// ============================================================================
// Metric Components
// ============================================================================

double metricFactor(double r, double rS) {
  // f(r) = 1 - rS/r
  return 1.0 - (rS / r);
}

double schwarzschildGTt(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // g_tt = -(1 - rS/r) * c^2
  return -(1.0 - (rS / r)) * C2;
}

double schwarzschildGRr(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // g_rr = (1 - rS/r)^-1
  return 1.0 / (1.0 - (rS / r));
}

// ============================================================================
// Christoffel Symbols
// ============================================================================

double christoffelTTr(double r, double rS) {
  // Gamma^t_tr = rS / (2r(r - rS))
  if (r <= rS) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return rS / (2.0 * r * (r - rS));
}

double christoffelRTt(double r, double rS) {
  // Gamma^r_tt = c^2 rS (r - rS) / (2r^3)
  if (r <= rS) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  const double r3 = r * r * r;
  return (C2 * rS * (r - rS)) / (2.0 * r3);
}

double christoffelRRr(double r, double rS) {
  // Gamma^r_rr = -rS / (2r(r - rS))
  if (r <= rS) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return -rS / (2.0 * r * (r - rS));
}

double christoffelRThth(double r, double rS) {
  // Gamma^r_thth = -(r - rS)
  return -(r - rS);
}

double christoffelRPhph(double r, double rS, double theta) {
  // Gamma^r_phph = -(r - rS) sin^2(theta)
  const double sinTheta = std::sin(theta);
  return -(r - rS) * sinTheta * sinTheta;
}

double christoffelThRth(double r) {
  // Gamma^th_rth = 1/r
  if (r <= 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return 1.0 / r;
}

double christoffelThPhph(double theta) {
  // Gamma^th_phph = -sin(theta) cos(theta)
  return -std::sin(theta) * std::cos(theta);
}

double christoffelPhRph(double r) {
  // Gamma^ph_rph = 1/r
  if (r <= 0.0) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  return 1.0 / r;
}

double christoffelPhThph(double theta) {
  // Gamma^ph_thph = cot(theta) = cos(theta)/sin(theta)
  const double sinTheta = std::sin(theta);
  if (std::abs(sinTheta) < 1e-10) {
    return std::numeric_limits<double>::quiet_NaN(); // Pole singularity
  }
  return std::cos(theta) / sinTheta;
}

// ============================================================================
// Orbital Dynamics
// ============================================================================

double gravitationalRedshift(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return safeInfinity<double>();
  }
  // z = 1/sqrt(1 - rS/r) - 1
  return (1.0 / std::sqrt(1.0 - (rS / r))) - 1.0;
}

double escapeVelocity(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return C; // At or below horizon, escape velocity equals c
  }
  // v_esc = c * sqrt(rS/r)
  return C * std::sqrt(rS / r);
}

double orbitalVelocity(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // v = sqrt(GM/r)
  return std::sqrt(G * mass / r);
}

double orbitalPeriod(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return std::numeric_limits<double>::quiet_NaN();
  }
  // T = 2*pi * sqrt(r^3/GM)
  return TWO_PI * std::sqrt((r * r * r) / (G * mass));
}

double surfaceGravity(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return safeInfinity<double>();
  }
  // kappa = GM / (r^2 * sqrt(1 - rS/r))
  return (G * mass) / (r * r * std::sqrt(1.0 - (rS / r)));
}

// ============================================================================
// Schwarzschild Class Implementation
// ============================================================================

Schwarzschild::Schwarzschild(double mass)
    : mass_(mass), r_s_(schwarzschildRadius(mass)),
      r_ph_(photonSphereRadius(mass)), r_isco_(iscoRadius(mass)) {}

double Schwarzschild::gTt(double r) const {
  return schwarzschildGTt(r, mass_);
}

double Schwarzschild::gRr(double r) const {
  return schwarzschildGRr(r, mass_);
}

double Schwarzschild::redshift(double r) const {
  return gravitationalRedshift(r, mass_);
}

double Schwarzschild::vEscape(double r) const {
  return escapeVelocity(r, mass_);
}

} // namespace physics
