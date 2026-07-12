/**
 * @file kerr_time_field.cpp
 * @brief Kerr equatorial TimeField implementation.
 */

#include "game/kerr_time_field.h"

#include <algorithm>
#include <cassert>
#include <cmath>
#include <numbers>

#include "constants.h"     // physics::G, physics::C, physics::C2
#include "kerr.h"          // physics::kerrDelta, kerrOuterHorizon, ergosphereRadius, frameDraggingOmega
#include "schwarzschild.h" // physics::schwarzschildRadius

namespace game {

namespace {
constexpr double K_MAX_SPIN_STAR = 0.998; // Thorne limit; keeps r_+ - r_- well separated.
const double K_EQUATOR_THETA = std::numbers::pi / 2.0;
} // namespace

KerrTimeField::KerrTimeField(double blackHoleMassG, double spinDimensionless)
    : blackHoleMassG_(blackHoleMassG),
      spinStar_(std::clamp(spinDimensionless, -K_MAX_SPIN_STAR, K_MAX_SPIN_STAR)),
      gravitationalRadiusCm_(physics::G * blackHoleMassG / physics::C2),
      schwarzschildRadiusCm_(physics::schwarzschildRadius(blackHoleMassG)),
      spinCm_(spinStar_ * gravitationalRadiusCm_),
      outerHorizonCm_(physics::kerrOuterHorizon(blackHoleMassG, spinCm_)),
      innerHorizonCm_(physics::kerrInnerHorizon(blackHoleMassG, spinCm_)),
      ergosphereCm_(physics::ergosphereRadius(blackHoleMassG, spinCm_, K_EQUATOR_THETA)) {
  assert(std::isfinite(outerHorizonCm_) && std::isfinite(innerHorizonCm_));
  assert(outerHorizonCm_ > innerHorizonCm_);
}

double KerrTimeField::properTimeRate(double radiusCm) const {
  const double delta = physics::kerrDelta(radiusCm, spinCm_, schwarzschildRadiusCm_);
  if (delta <= 0.0) {
    return 0.0; // at or inside the outer horizon
  }
  // Equatorial ZAMO lapse alpha = sqrt(Sigma * Delta / A), Sigma = r^2 (cos = 0),
  // A = (r^2 + a^2)^2 - a^2 * Delta * sin^2 = (r^2 + a^2)^2 - a^2 * Delta.
  const double sigma = radiusCm * radiusCm;
  const double r2PlusA2 = (radiusCm * radiusCm) + (spinCm_ * spinCm_);
  const double bigA = (r2PlusA2 * r2PlusA2) - (spinCm_ * spinCm_ * delta);
  return std::sqrt((sigma * delta) / bigA);
}

bool KerrTimeField::isValidStationRadius(double radiusCm) const {
  return std::isfinite(radiusCm) && radiusCm > outerHorizonCm_;
}

double KerrTimeField::signalDelaySec(double fromRadiusCm, double toRadiusCm) const {
  assert(isValidStationRadius(fromRadiusCm));
  assert(isValidStationRadius(toRadiusCm));
  const double innerRadiusCm = std::fmin(fromRadiusCm, toRadiusCm);
  const double outerRadiusCm = std::fmax(fromRadiusCm, toRadiusCm);
  if (innerRadiusCm == outerRadiusCm) {
    return 0.0;
  }
  // Coordinate time along an ingoing/outgoing principal null geodesic:
  // dt = (r^2 + a^2)/Delta dr, and (r^2 + a^2) = Delta + r_s r, so
  // delta_t = (r2 - r1) + r_s * integral r/Delta dr, with
  // integral r/Delta dr = [r_+ ln(r-r_+) - r_- ln(r-r_-)] / (r_+ - r_-).
  // At a = 0 (r_+ = r_s, r_- = 0) this is the Schwarzschild radial delay.
  const double horizonGap = outerHorizonCm_ - innerHorizonCm_; // 2 sqrt(M^2 - a^2) > 0
  const double logPlus =
      outerHorizonCm_ * std::log((outerRadiusCm - outerHorizonCm_) / (innerRadiusCm - outerHorizonCm_));
  const double logMinus =
      innerHorizonCm_ * std::log((outerRadiusCm - innerHorizonCm_) / (innerRadiusCm - innerHorizonCm_));
  const double shapiroCm = (schwarzschildRadiusCm_ / horizonGap) * (logPlus - logMinus);
  const double delaySec = ((outerRadiusCm - innerRadiusCm) + shapiroCm) / physics::C;
  assert(std::isfinite(delaySec) && delaySec > 0.0);
  return delaySec;
}

double KerrTimeField::frameDragRateRadPerSec(double radiusCm) const {
  return physics::frameDraggingOmega(radiusCm, K_EQUATOR_THETA, blackHoleMassG_, spinCm_);
}

} // namespace game
