/**
 * @file kerr_time_field.h
 * @brief Rotating (Kerr) equatorial TimeField with frame dragging.
 *
 * A hovering station is a zero-angular-momentum observer (ZAMO): its clock is
 * the ZAMO lapse, which stays positive and finite into the ergoregion where no
 * static observer can exist. An orbiting station is a circular geodesic of its
 * sense and carries the Bardeen-Press-Teukolsky orbital clock; the field admits
 * it only strictly outside that sense's marginally bound radius, where a bound
 * circular orbit exists. At zero spin the lapse, the orbital clock, and the
 * signal delay reduce exactly to the Schwarzschild BlackholeTimeField.
 *
 * The field stores the spin deficit epsilon = 1 - |a| rather than a and
 * delegates every metric quantity to physics/kerr_observer.h, which works in
 * (epsilon, x = r/M - 1). Spins arbitrarily close to extremal therefore keep
 * their physics: Gargantua's 1 - a = 1.33e-14 would round to two significant
 * digits of 1 - a^2 as a double a.
 *
 * physics::kerrTimeDilation is deliberately NOT used: its docstring claims a
 * ZAMO quantity but its body returns sqrt(-g_tt), the static-observer
 * expression (kerr.h:360).
 */

#ifndef BLACKHOLE_GAME_KERR_TIME_FIELD_H
#define BLACKHOLE_GAME_KERR_TIME_FIELD_H

#include "game/time_field.h"

namespace game {

/** @brief Spin given as its deficit from extremal, epsilon = 1 - |a| in [0, 1]. */
struct SpinDeficit {
  double epsilon = 1.0;
};

class KerrTimeField final : public TimeField {
public:
  /** @brief spinDimensionless is a/M in [-1, 1] (clamped there); the field
   *         keeps epsilon = 1 - |a| and the sign of a. */
  KerrTimeField(double blackHoleMassG, double spinDimensionless);

  /** @brief Prograde-positive spin a = 1 - epsilon given by its deficit, for
   *         spins a double a cannot resolve. epsilon is clamped to [0, 1]. */
  KerrTimeField(double blackHoleMassG, SpinDeficit deficit);

  [[nodiscard]] double properTimeRate(double radiusCm, Observer observer) const override;
  [[nodiscard]] bool admitsObserver(double radiusCm, Observer observer) const override;
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
  [[nodiscard]] double iscoRadiusCm(Observer orbit) const;
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
