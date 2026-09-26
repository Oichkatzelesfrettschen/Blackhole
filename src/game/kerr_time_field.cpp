/**
 * @file kerr_time_field.cpp
 * @brief Kerr equatorial TimeField implementation.
 */

#include "game/kerr_time_field.h"

#include <algorithm>
#include <cassert>
#include <cmath>

#include "constants.h"     // physics::G, physics::C, physics::C2
#include "kerr_observer.h" // equatorial Kerr primitives in (epsilon, x)

namespace game {

namespace ko = physics::kerr_observer;

KerrTimeField::KerrTimeField(double blackHoleMassG, double spinDimensionless)
    : KerrTimeField(
          blackHoleMassG,
          SpinDeficit{.epsilon = 1.0 - std::fabs(std::clamp(spinDimensionless, -1.0, 1.0))}) {
  spinSign_ = spinDimensionless < 0.0 ? -1.0 : 1.0;
}

KerrTimeField::KerrTimeField(double blackHoleMassG, SpinDeficit deficit)
    : epsilon_(std::clamp(deficit.epsilon, 0.0, 1.0)), spinSign_(1.0),
      gravitationalRadiusCm_(physics::G * blackHoleMassG / physics::C2),
      schwarzschildRadiusCm_(2.0 * gravitationalRadiusCm_),
      outerHorizonCm_(gravitationalRadiusCm_ * (1.0 + ko::horizonOffset(epsilon_))),
      ergosphereCm_(2.0 * gravitationalRadiusCm_) {
  assert(std::isfinite(gravitationalRadiusCm_) && gravitationalRadiusCm_ > 0.0);
}

double KerrTimeField::properTimeRate(double radiusCm) const {
  if (!isValidStationRadius(radiusCm)) {
    return 0.0; // at or inside the outer horizon
  }
  return ko::equatorialFrame(epsilon_, radialOffset(radiusCm)).alpha;
}

bool KerrTimeField::isValidStationRadius(double radiusCm) const {
  return std::isfinite(radiusCm) && radialOffset(radiusCm) > ko::horizonOffset(epsilon_);
}

double KerrTimeField::signalDelaySec(double fromRadiusCm, double toRadiusCm) const {
  assert(isValidStationRadius(fromRadiusCm));
  assert(isValidStationRadius(toRadiusCm));
  if (fromRadiusCm == toRadiusCm) {
    return 0.0;
  }
  // Coordinate time along the principal null congruence, dt = (r^2 + a^2)/Delta dr,
  // in the atanh form that stays exact as r_+ - r_- -> 0 (kerr_observer.h). At
  // a = 0 it is the Schwarzschild radial delay.
  const double delayM =
      ko::principalNullDelay(epsilon_, radialOffset(fromRadiusCm), radialOffset(toRadiusCm));
  const double delaySec = delayM * gravitationalRadiusCm_ / physics::C;
  assert(std::isfinite(delaySec) && delaySec > 0.0);
  return delaySec;
}

double KerrTimeField::frameDragRateRadPerSec(double radiusCm) const {
  if (!isValidStationRadius(radiusCm)) {
    return 0.0;
  }
  // omega is in radians per unit M of coordinate time; M/c seconds per unit.
  const double omegaPerM = ko::equatorialFrame(epsilon_, radialOffset(radiusCm)).omega;
  return spinSign_ * omegaPerM * physics::C / gravitationalRadiusCm_;
}

} // namespace game
