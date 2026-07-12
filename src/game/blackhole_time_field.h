/**
 * @file blackhole_time_field.h
 * @brief Schwarzschild TimeField adapter over the physics:: primitives.
 */

#ifndef BLACKHOLE_GAME_BLACKHOLE_TIME_FIELD_H
#define BLACKHOLE_GAME_BLACKHOLE_TIME_FIELD_H

#include "game/time_field.h"

namespace game {

/**
 * @brief Stationary-observer Schwarzschild field around one black hole.
 *
 * properTimeRate delegates to physics::timeDilationFactor (dtau/dt =
 * sqrt(1 - r_s/r), zero at or inside the horizon). signalDelaySec integrates
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

  [[nodiscard]] double properTimeRate(double radiusCm) const override;
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override;
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override;

  [[nodiscard]] double horizonRadiusCm() const { return horizonRadiusCm_; }

private:
  double blackHoleMassG_;
  double horizonRadiusCm_;
};

} // namespace game

#endif // BLACKHOLE_GAME_BLACKHOLE_TIME_FIELD_H
