/**
 * @file observer.h
 * @brief Which worldline a station follows, and so which clock it carries.
 *
 * A fleet, colony, or authority at a given radius runs a different proper-time
 * rate depending on how it holds that radius. A free-falling circular orbit
 * is a geodesic and carries the orbital clock; a station that hovers on thrust
 * with zero angular momentum (a ZAMO) carries the lapse. At r = 6M around a
 * spin-0.9 hole the two differ by ten percent.
 *
 * Circular orbits of one sense exist from infinity in to that sense's photon
 * orbit, but only those outside the marginally bound radius r_mb are bound
 * (E < 1); the game admits orbital stations there and nowhere closer, so a
 * station below r_mb hovers. Between r_mb and the ISCO a circular orbit is a
 * geodesic whose clock is exact but which is unstable: any perturbation grows,
 * so the station holds it with station-keeping thrust. TimeField reports
 * which admitted orbits are stable (admitsStableOrbit) so the interface can
 * label the rest "unstable (station-keeping)".
 */

#ifndef BLACKHOLE_GAME_OBSERVER_H
#define BLACKHOLE_GAME_OBSERVER_H

#include <cstdint>

namespace game {

/** @brief The clock-carrying worldline of a station. Values are serialized. */
enum class Observer : std::uint8_t {
  Hovering = 0,                ///< Zero-angular-momentum station on thrust (ZAMO; static at zero spin).
  CircularOrbitPrograde = 1,   ///< Circular geodesic co-rotating with the hole.
  CircularOrbitRetrograde = 2, ///< Circular geodesic counter-rotating.
};

/** @brief How a fleet holds its band: in free fall on a circular orbit, or
 *         hovering on thrust. Values are serialized. */
enum class StationKeeping : std::uint8_t {
  Orbit = 0,
  Hover = 1,
};

[[nodiscard]] constexpr const char *observerName(Observer observer) {
  switch (observer) {
  case Observer::Hovering:
    return "hovering";
  case Observer::CircularOrbitPrograde:
    return "prograde orbit";
  case Observer::CircularOrbitRetrograde:
    return "retrograde orbit";
  }
  return "unknown";
}

} // namespace game

#endif // BLACKHOLE_GAME_OBSERVER_H
