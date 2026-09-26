/**
 * @file kerr_time_field.h
 * @brief Rotating (Kerr) equatorial TimeField with frame dragging.
 *
 * Every fleet is modelled as a zero-angular-momentum observer (ZAMO): its
 * clock is the ZAMO lapse, which stays positive and finite into the ergoregion
 * where no static observer can exist. This uniform choice keeps the proper-time
 * rate continuous across the ergosphere (a static-observer clock would go
 * imaginary at r_ergo). At zero spin the lapse and the signal delay reduce
 * exactly to the Schwarzschild BlackholeTimeField.
 *
 * The lapse is the ZAMO expression sqrt(Sigma Delta / A) that
 * physics::kerrZamoLapse also evaluates; physics::kerrStaticTimeDilation is
 * the static-observer rate, which has no value inside the ergoregion.
 */

#ifndef BLACKHOLE_GAME_KERR_TIME_FIELD_H
#define BLACKHOLE_GAME_KERR_TIME_FIELD_H

#include "game/time_field.h"

namespace game {

class KerrTimeField final : public TimeField {
public:
  /** @brief spinDimensionless is a/M; clamped to +/-0.998 (Thorne limit) so
   *         the outer and inner horizons stay well separated and the
   *         signal-delay closed form is well-conditioned. */
  KerrTimeField(double blackHoleMassG, double spinDimensionless);

  [[nodiscard]] double properTimeRate(double radiusCm) const override;
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override;
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override;
  [[nodiscard]] double innerBoundaryRadiusCm() const override { return outerHorizonCm_; }
  [[nodiscard]] double ergosphereRadiusCm() const override { return ergosphereCm_; }
  [[nodiscard]] double frameDragRateRadPerSec(double radiusCm) const override;
  [[nodiscard]] double spinDimensionless() const override { return spinStar_; }

  [[nodiscard]] double gravitationalRadiusCm() const { return gravitationalRadiusCm_; }
  [[nodiscard]] double schwarzschildRadiusCm() const { return schwarzschildRadiusCm_; }
  [[nodiscard]] double outerHorizonCm() const { return outerHorizonCm_; }

private:
  double blackHoleMassG_;
  double spinStar_;              ///< a/M, clamped.
  double gravitationalRadiusCm_; ///< M = GM/c^2.
  double schwarzschildRadiusCm_; ///< 2M (spin-independent length scale).
  double spinCm_;                ///< a = spinStar * M, in cm.
  double outerHorizonCm_;        ///< r_+ = M + sqrt(M^2 - a^2).
  double innerHorizonCm_;        ///< r_- = M - sqrt(M^2 - a^2).
  double ergosphereCm_;          ///< Equatorial ergosphere, 2M.
};

} // namespace game

#endif // BLACKHOLE_GAME_KERR_TIME_FIELD_H
