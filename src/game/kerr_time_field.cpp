/**
 * @file kerr_time_field.cpp
 * @brief Kerr equatorial TimeField implementation.
 */

#include "game/kerr_time_field.h"

#include <algorithm>
#include <cassert>
#include <cmath>

#include "constants.h"     // physics::G, physics::C, physics::C2
#include "game/observer.h"
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
    : epsilon_(std::clamp(deficit.epsilon, K_MIN_SPIN_DEFICIT, 1.0)), spinSign_(1.0),
      gravitationalRadiusCm_(physics::G * blackHoleMassG / physics::C2),
      schwarzschildRadiusCm_(2.0 * gravitationalRadiusCm_),
      outerHorizonCm_(gravitationalRadiusCm_ * (1.0 + ko::horizonOffset(epsilon_))),
      ergosphereCm_(2.0 * gravitationalRadiusCm_) {
  assert(std::isfinite(gravitationalRadiusCm_) && gravitationalRadiusCm_ > 0.0);
}

namespace {

// Orbital sense relative to the hole's rotation; epsilon already folds |a|, so
// prograde here is prograde in kerr_observer.h for either spin sign.
ko::OrbitSense senseOf(Observer orbit) {
  return orbit == Observer::CircularOrbitRetrograde ? ko::OrbitSense::Retrograde
                                                    : ko::OrbitSense::Prograde;
}

} // namespace

double KerrTimeField::properTimeRate(double radiusCm, Observer observer) const {
  if (!isValidStationRadius(radiusCm)) {
    return 0.0; // at or inside the outer horizon
  }
  const double x = radialOffset(radiusCm);
  if (observer == Observer::Hovering) {
    return ko::equatorialFrame(epsilon_, x).alpha;
  }
  // Zero where no timelike circular orbit of this sense exists (inside its
  // photon orbit); admitsObserver keeps such placements out of the game.
  return ko::circularOrbit(epsilon_, x, senseOf(observer)).properTimeRate;
}

bool KerrTimeField::admitsObserver(double radiusCm, Observer observer) const {
  if (!isValidStationRadius(radiusCm)) {
    return false;
  }
  if (observer == Observer::Hovering) {
    return true;
  }
  return radialOffset(radiusCm) > ko::marginallyBoundOffset(epsilon_, senseOf(observer));
}

bool KerrTimeField::admitsStableOrbit(double radiusCm, Observer observer) const {
  if (observer == Observer::Hovering || !admitsObserver(radiusCm, observer)) {
    return false;
  }
  // A band placed on the ISCO comes back from cm within a few ulps of it
  // (Miller's round trip lands 3.2e-17 M above iscoOffset); the relative
  // tolerance keeps that band stable without admitting any band measurably
  // inside the ISCO.
  constexpr double iscoRelativeTolerance = 1e-9;
  const double xIsco = ko::iscoOffset(epsilon_, senseOf(observer));
  return radialOffset(radiusCm) >= xIsco * (1.0 - iscoRelativeTolerance);
}

double KerrTimeField::marginallyBoundRadiusCm(Observer orbit) const {
  return gravitationalRadiusCm_ * (1.0 + ko::marginallyBoundOffset(epsilon_, senseOf(orbit)));
}

double KerrTimeField::iscoRadiusCm(Observer orbit) const {
  return gravitationalRadiusCm_ * (1.0 + ko::iscoOffset(epsilon_, senseOf(orbit)));
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
