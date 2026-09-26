/**
 * @file time_field.h
 * @brief Proper-time rate and signal-delay interface the campaign core plays on.
 *
 * The campaign never touches a metric directly: every gravitational effect it
 * consumes -- how fast a station's local clock runs, how long a signal takes
 * between orbital radii, whether a station radius is physically admissible --
 * arrives through this interface. Tests substitute a fake field. A clock rate
 * is a property of a worldline, not of a radius, so every rate query names the
 * Observer that carries the clock.
 */

#ifndef BLACKHOLE_GAME_TIME_FIELD_H
#define BLACKHOLE_GAME_TIME_FIELD_H

#include <cmath>

#include "game/observer.h"

namespace game {

class TimeField {
public:
  virtual ~TimeField() = default;

  /** @brief dtau/dt for `observer` at radiusCm; in (0, 1] wherever
   *         admitsObserver(radiusCm, observer) holds. */
  [[nodiscard]] virtual double properTimeRate(double radiusCm, Observer observer) const = 0;

  /** @brief True when `observer` can be stationed at radiusCm: a hovering
   *         station needs a valid station radius, an orbit additionally needs a
   *         bound circular orbit of its sense there. A field without orbital
   *         structure admits every observer on every valid radius. */
  [[nodiscard]] virtual bool admitsObserver(double radiusCm, Observer /*observer*/) const {
    return isValidStationRadius(radiusCm);
  }

  /** @brief One-way coordinate-time delay in seconds for a light signal
   *         exchanged between stations at the two radii. Finite and
   *         non-negative for valid radii; zero only when the radii coincide. */
  [[nodiscard]] virtual double signalDelaySec(double fromRadiusCm, double toRadiusCm) const = 0;

  /** @brief True when a station can exist at radiusCm. A rejected radius must
   *         never reach properTimeRate or signalDelaySec. */
  [[nodiscard]] virtual bool isValidStationRadius(double radiusCm) const = 0;

  /** @brief Radius below which no station can exist (the horizon for a black
   *         hole field). Zero for fields without an inner boundary; the map
   *         draws it as the forbidden core. */
  [[nodiscard]] virtual double innerBoundaryRadiusCm() const { return 0.0; }

  /** @brief Angular velocity (rad/s) at which local inertial frames are
   *         dragged around the axis at radiusCm. Zero for a non-rotating
   *         field; positive and rising toward the horizon for a Kerr field. */
  [[nodiscard]] virtual double frameDragRateRadPerSec(double /*radiusCm*/) const { return 0.0; }

  /** @brief Radius of the static limit (ergosphere). Inside it no observer can
   *         hold a fixed angular position; retrograde holds are impossible.
   *         Coincides with the inner boundary when the field does not rotate. */
  [[nodiscard]] virtual double ergosphereRadiusCm() const { return innerBoundaryRadiusCm(); }

  /** @brief Dimensionless spin a/M in [-1, 1]; zero for a non-rotating field. */
  [[nodiscard]] virtual double spinDimensionless() const { return 0.0; }

  /** @brief Spin deficit epsilon = 1 - |a|, the exact spin parameter a field
   *         near extremal stores; derived from spinDimensionless unless the
   *         field keeps it directly. */
  [[nodiscard]] virtual double spinDeficit() const { return 1.0 - std::fabs(spinDimensionless()); }
};

} // namespace game

#endif // BLACKHOLE_GAME_TIME_FIELD_H
