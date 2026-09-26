/**
 * @file blackhole_time_field.h
 * @brief Schwarzschild TimeField adapter over the physics:: primitives.
 */

#ifndef BLACKHOLE_GAME_BLACKHOLE_TIME_FIELD_H
#define BLACKHOLE_GAME_BLACKHOLE_TIME_FIELD_H

#include "game/time_field.h"

namespace game {

/**
 * @brief Schwarzschild field around one black hole.
 *
 * A hovering station is the static observer, dtau/dt = sqrt(1 - r_s/r)
 * (physics::timeDilationFactor, zero at or inside the horizon); a circular
 * orbit of either sense carries sqrt(1 - 3M/r) and is admitted only outside
 * the marginally bound radius 4M = 2 r_s; between 4M and the 6M ISCO it is
 * unstable and held by station-keeping thrust. signalDelaySec integrates
 * the radial null coordinate time exactly:
 *
 *   delta_t = (r2 - r1)/c + (r_s/c) * ln((r2 - r_s)/(r1 - r_s))
 *
 * The logarithm term is the Shapiro delay for radial exchange; it diverges as
 * the inner station approaches the horizon, which is exactly the stale-telemetry
 * pressure the campaign wants. physics::shapiroDelay is NOT used: it is a
 * radar-echo grazing-chord formula whose impact parameter is undefined for two
 * stations given by radius alone, and its b->0 limit is +inf.
 */
class BlackholeTimeField final : public TimeField {
public:
  explicit BlackholeTimeField(double blackHoleMassG);

  [[nodiscard]] double properTimeRate(double radiusCm, Observer observer) const override;
  [[nodiscard]] bool admitsObserver(double radiusCm, Observer observer) const override;
  [[nodiscard]] bool admitsStableOrbit(double radiusCm, Observer observer) const override;
  [[nodiscard]] double iscoRadiusCm(Observer /*orbit*/) const override {
    return 3.0 * horizonRadiusCm_;
  }
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override;
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override;

  [[nodiscard]] double innerBoundaryRadiusCm() const override { return horizonRadiusCm_; }

  [[nodiscard]] double horizonRadiusCm() const { return horizonRadiusCm_; }

private:
  double blackHoleMassG_;
  double horizonRadiusCm_;
};

} // namespace game

#endif // BLACKHOLE_GAME_BLACKHOLE_TIME_FIELD_H
