/**
 * @file blackhole_time_field.cpp
 * @brief Schwarzschild TimeField adapter implementation.
 */

#include "game/blackhole_time_field.h"

#include <cassert>
#include <cmath>

#include "constants.h"     // physics::C
#include "geodesics.h"     // physics::timeDilationFactor
#include "schwarzschild.h" // physics::schwarzschildRadius

namespace game {

BlackholeTimeField::BlackholeTimeField(double blackHoleMassG)
    : blackHoleMassG_(blackHoleMassG),
      horizonRadiusCm_(physics::schwarzschildRadius(blackHoleMassG)) {}

double BlackholeTimeField::properTimeRate(double radiusCm) const {
  return physics::timeDilationFactor(radiusCm, blackHoleMassG_);
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
