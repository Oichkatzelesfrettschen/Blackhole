/**
 * @file time_field.h
 * @brief Proper-time rate and signal-delay interface the campaign core plays on.
 *
 * The campaign never touches a metric directly: every gravitational effect it
 * consumes -- how fast a fleet's local clock runs, how long a signal takes
 * between orbital radii, whether a station radius is physically admissible --
 * arrives through this interface. Tests substitute a fake field; a Kerr field
 * can slot in behind the same three calls later.
 */

#ifndef BLACKHOLE_GAME_TIME_FIELD_H
#define BLACKHOLE_GAME_TIME_FIELD_H

namespace game {

class TimeField {
public:
  virtual ~TimeField() = default;

  /** @brief dtau/dt for a stationary observer at radiusCm; in (0, 1] for every
   *         radius that isValidStationRadius accepts. */
  [[nodiscard]] virtual double properTimeRate(double radiusCm) const = 0;

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
};

} // namespace game

#endif // BLACKHOLE_GAME_TIME_FIELD_H
