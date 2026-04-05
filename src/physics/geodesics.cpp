/**
 * @file geodesics.cpp
 * @brief Implementation of geodesic calculations.
 */

#include "geodesics.h"

#include <cmath>
#include <limits>
#include <numbers>

#include "constants.h"
#include "schwarzschild.h"

namespace physics {

// ============================================================================
// Light Deflection
// ============================================================================

double gravitationalDeflection(double impactParam, double mass) {
  // delta_phi = 4GM/(bc^2)
  return FOUR_G_OVER_C2 * mass / impactParam;
}

double criticalImpactParameter(double mass) {
  // b_crit = (3*sqrt(3)/2) * r_s
  // WHY: comes from unstable circular photon orbit condition
  const double rS = schwarzschildRadius(mass);
  return (3.0 * std::numbers::sqrt3 / 2.0) * rS;
}

bool isPhotonCaptured(double impactParam, double mass) {
  return impactParam < criticalImpactParameter(mass);
}

// ============================================================================
// Time Effects
// ============================================================================

double shapiroDelay(double r1, double r2, double impactParam, double mass) {
  // delta_t = (2GM/c^3) * ln((r1+r2+d)/(r1+r2-d))
  // where d = sqrt((r1+r2)^2 - b^2)
  const double sum = r1 + r2;
  const double d = std::sqrt((sum * sum) - (impactParam * impactParam));
  const double factor = (2.0 * G * mass) / (C * C * C);
  return factor * std::log((sum + d) / (sum - d));
}

double timeDilationFactor(double r, double mass) {
  const double rS = schwarzschildRadius(mass);
  if (r <= rS) {
    return 0.0; // At or below horizon
  }
  // dtau/dt = sqrt(1 - rS/r)
  return std::sqrt(1.0 - (rS / r));
}

// ============================================================================
// Ray Tracing Helpers
// ============================================================================

double nullEffectivePotential(double r, double rS) {
  // V_eff(r) = (1 - rS/r) / r^2
  return (1.0 - (rS / r)) / (r * r);
}

double nullRadialDerivativeSquared(double r, double rS, double b) {
  // (dr/dphi)^2 = r^4/b^2 - r^2*(1 - rS/r)
  const double r2 = r * r;
  const double r4 = r2 * r2;
  return (r4 / (b * b)) - (r2 * (1.0 - (rS / r)));
}

double photonTurningPoint(double impactParam, double mass) {
  const double rS = schwarzschildRadius(mass);
  const double bCrit = criticalImpactParameter(mass);

  // If b < b_crit, photon is captured -- no turning point
  if (impactParam <= bCrit) {
    return std::numeric_limits<double>::quiet_NaN();
  }

  // For b > b_crit, solve r^3 - b^2*r + b^2*rS = 0 via Newton's method.
  // WHY: comes from (dr/dphi)^2 = 0 condition for null geodesic.
  // Initial guess: r ≈ b (valid for b >> b_crit)
  double rTurn = impactParam;
  for (int i = 0; i < 10; ++i) {
    const double r3 = rTurn * rTurn * rTurn;
    const double f = (r3 - (impactParam * impactParam * rTurn)) + (impactParam * impactParam * rS);
    const double df = (3.0 * rTurn * rTurn) - (impactParam * impactParam);
    if (std::abs(df) < 1e-20) {
      break;
    }
    rTurn -= f / df;
    if (rTurn < rS) {
      rTurn = rS * 1.001; // Clamp above horizon
    }
  }

  return rTurn;
}

// ============================================================================
// Coordinate Transformations
// ============================================================================

void schwarzschildToCartesian(double r, double theta, double phi, double &x, double &y, double &z) {
  const double sinTheta = std::sin(theta);
  x = r * sinTheta * std::cos(phi);
  y = r * sinTheta * std::sin(phi);
  z = r * std::cos(theta);
}

void cartesianToSchwarzschild(double x, double y, double z, double &r, double &theta, double &phi) {
  r = std::sqrt((x * x) + (y * y) + (z * z));
  if (r < 1e-20) {
    theta = 0.0;
    phi = 0.0;
    return;
  }
  theta = std::acos(z / r);
  phi = std::atan2(y, x);
}

} // namespace physics
