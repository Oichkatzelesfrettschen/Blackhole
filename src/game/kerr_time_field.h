/**
 * @file kerr_time_field.h
 * @brief Rotating (Kerr) equatorial TimeField with frame dragging.
 *
 * A hovering station is a zero-angular-momentum observer (ZAMO): its clock is
 * the ZAMO lapse, which stays positive and finite into the ergoregion where no
 * static observer can exist. An orbiting station is a circular geodesic of its
 * sense and carries the Bardeen-Press-Teukolsky orbital clock; the field admits
 * it only strictly outside that sense's marginally bound radius, where a bound
 * circular orbit exists. Between that radius and the ISCO the orbit is
 * unstable and the station holds it with station-keeping thrust -- its clock
 * is still the circular geodesic's -- and admitsStableOrbit tells the two
 * apart (the default M87 band at 6M is such an orbit for the retrograde lane,
 * r_mb = 5.657M against an ISCO of 8.717M). At zero spin the lapse, the orbital clock, and the
 * signal delay reduce exactly to the Schwarzschild BlackholeTimeField.
 *
 * The field stores the spin deficit epsilon = 1 - |a| rather than a and
 * delegates every metric quantity to physics/kerr_observer.h, which works in
 * (epsilon, x = r/M - 1). Near-extremal spins therefore keep their physics:
 * Gargantua's 1 - a = 1.33e-14 would round to two significant digits of
 * 1 - a^2 as a double a. The field's interface speaks absolute radii in cm,
 * which resolve x only to about 1e-16, so the deficit has a floor,
 * K_MIN_SPIN_DEFICIT = 1e-24: there the horizon (x = 1.41e-12), photon orbit
 * (1.63e-12), and marginally bound radius (2.00e-12) sit thousands of ulp
 * apart and the ISCO (1.59e-8) far above them. A smaller deficit, exact
 * extremality included, is raised to the floor; spinDeficit() reports it.
 *
 * physics::kerrZamoLapse evaluates the same ZAMO lapse sqrt(Sigma Delta / A)
 * in (a, r) form; physics::kerrStaticTimeDilation is the static-observer rate,
 * which has no value inside the ergoregion.
 */

#ifndef BLACKHOLE_GAME_KERR_TIME_FIELD_H
#define BLACKHOLE_GAME_KERR_TIME_FIELD_H

#include "game/time_field.h"

namespace game {

/** @brief Spin given as its deficit from extremal, epsilon = 1 - |a| in
 *         [KerrTimeField::K_MIN_SPIN_DEFICIT, 1]. */
struct SpinDeficit {
  double epsilon = 1.0;
};

class KerrTimeField final : public TimeField {
public:
  /// Smallest deficit whose characteristic radii the cm interface resolves.
  static constexpr double K_MIN_SPIN_DEFICIT = 1e-24;

  /** @brief spinDimensionless is a/M in [-1, 1] (clamped there); the field
   *         keeps epsilon = 1 - |a|, raised to K_MIN_SPIN_DEFICIT, and the
   *         sign of a. */
  KerrTimeField(double blackHoleMassG, double spinDimensionless);

  /** @brief Prograde-positive spin a = 1 - epsilon given by its deficit, for
   *         spins a double a cannot resolve. epsilon is clamped to
   *         [K_MIN_SPIN_DEFICIT, 1]. */
  KerrTimeField(double blackHoleMassG, SpinDeficit deficit);

  [[nodiscard]] double properTimeRate(double radiusCm, Observer observer) const override;
  [[nodiscard]] bool admitsObserver(double radiusCm, Observer observer) const override;
  [[nodiscard]] bool admitsStableOrbit(double radiusCm, Observer observer) const override;
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override;
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override;
  [[nodiscard]] double innerBoundaryRadiusCm() const override { return outerHorizonCm_; }
  [[nodiscard]] double ergosphereRadiusCm() const override { return ergosphereCm_; }
  [[nodiscard]] double frameDragRateRadPerSec(double radiusCm) const override;
  [[nodiscard]] double spinDimensionless() const override { return spinSign_ * (1.0 - epsilon_); }

  /** @brief epsilon = 1 - |a|, exact as constructed. */
  [[nodiscard]] double spinDeficit() const override { return epsilon_; }
  [[nodiscard]] double gravitationalRadiusCm() const { return gravitationalRadiusCm_; }
  [[nodiscard]] double schwarzschildRadiusCm() const { return schwarzschildRadiusCm_; }
  [[nodiscard]] double outerHorizonCm() const { return outerHorizonCm_; }
  /** @brief Radius inside which no bound circular orbit of this sense exists
   *         (r_mb); prograde relative to the hole's rotation. */
  [[nodiscard]] double marginallyBoundRadiusCm(Observer orbit) const;
  /** @brief Innermost stable circular orbit radius of the orbit's sense. */
  [[nodiscard]] double iscoRadiusCm(Observer orbit) const override;
  /** @brief x = r/M - 1, the radial coordinate kerr_observer.h works in. */
  [[nodiscard]] double radialOffset(double radiusCm) const {
    return (radiusCm / gravitationalRadiusCm_) - 1.0;
  }

private:
  double epsilon_;               ///< 1 - |a|.
  double spinSign_;              ///< +1 or -1: the sense of the hole's rotation.
  double gravitationalRadiusCm_; ///< M = GM/c^2.
  double schwarzschildRadiusCm_; ///< 2M (spin-independent length scale).
  double outerHorizonCm_;        ///< r_+ = M (1 + sqrt(epsilon (2 - epsilon))).
  double ergosphereCm_;          ///< Equatorial ergosphere, 2M.
};

} // namespace game

#endif // BLACKHOLE_GAME_KERR_TIME_FIELD_H
