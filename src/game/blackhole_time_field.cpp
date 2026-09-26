/**
 * @file blackhole_time_field.cpp
 * @brief Schwarzschild TimeField adapter implementation.
 */

#include "game/blackhole_time_field.h"

#include <cassert>
#include <cmath>

#include "constants.h"     // physics::C
#include "game/observer.h"
#include "geodesics.h"     // physics::timeDilationFactor
#include "schwarzschild.h" // physics::schwarzschildRadius

namespace game {

BlackholeTimeField::BlackholeTimeField(double blackHoleMassG)
    : blackHoleMassG_(blackHoleMassG),
      horizonRadiusCm_(physics::schwarzschildRadius(blackHoleMassG)) {}

double BlackholeTimeField::properTimeRate(double radiusCm, Observer observer) const {
  if (observer == Observer::Hovering) {
    return physics::timeDilationFactor(radiusCm, blackHoleMassG_);
  }
  // Circular geodesic: dtau/dt = sqrt(1 - 3M/r) = sqrt(1 - 1.5 r_s/r), real
  // outside the photon sphere 1.5 r_s.
  const double radicand = 1.0 - (1.5 * horizonRadiusCm_ / radiusCm);
  return radicand > 0.0 ? std::sqrt(radicand) : 0.0;
}

bool BlackholeTimeField::admitsStableOrbit(double radiusCm, Observer observer) const {
  // Stable at or outside the ISCO 6M = 3 r_s, with the same relative
  // tolerance as the Kerr field for a band placed on it.
  constexpr double iscoRelativeTolerance = 1e-9;
  return observer != Observer::Hovering && admitsObserver(radiusCm, observer) &&
         radiusCm >= 3.0 * horizonRadiusCm_ * (1.0 - iscoRelativeTolerance);
}

bool BlackholeTimeField::admitsObserver(double radiusCm, Observer observer) const {
  if (!isValidStationRadius(radiusCm)) {
    return false;
  }
  // Bound circular orbits exist only outside r_mb = 4M = 2 r_s.
  return observer == Observer::Hovering || radiusCm > 2.0 * horizonRadiusCm_;
}

bool BlackholeTimeField::isValidStationRadius(double radiusCm) const {
  return std::isfinite(radiusCm) && radiusCm > horizonRadiusCm_;
}

double BlackholeTimeField::signalDelaySec(double fromRadiusCm, double toRadiusCm) const {
  assert(isValidStationRadius(fromRadiusCm));
  assert(isValidStationRadius(toRadiusCm));
  const double innerRadiusCm = std::fmin(fromRadiusCm, toRadiusCm);
  const double outerRadiusCm = std::fmax(fromRadiusCm, toRadiusCm);
  if (innerRadiusCm == outerRadiusCm) {
    return 0.0;
  }
  // Radial null geodesic in Schwarzschild coordinate time:
  // dt = dr / (c * (1 - r_s/r))  integrates to
  // delta_t = (r2 - r1)/c + (r_s/c) * ln((r2 - r_s)/(r1 - r_s)).
  const double flightSec = (outerRadiusCm - innerRadiusCm) / physics::C;
  const double shapiroSec = (horizonRadiusCm_ / physics::C) *
                            std::log((outerRadiusCm - horizonRadiusCm_) /
                                     (innerRadiusCm - horizonRadiusCm_));
  const double delaySec = flightSec + shapiroSec;
  assert(std::isfinite(delaySec) && delaySec > 0.0);
  return delaySec;
}

} // namespace game
