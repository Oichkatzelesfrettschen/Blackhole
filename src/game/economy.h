/**
 * @file economy.h
 * @brief Pure economy atoms shared by every deterministic game core.
 *
 * These are the scalar relationships the campaign economy is built from, factored
 * out of any particular state object so both the single-hole CampaignState and
 * the multi-system Constellation compute yield, ergoregion depth, and the
 * instability erosion identically. Each is a pure function of its arguments: no
 * field references, no mutation, so a scenario expressed in either core prices a
 * unit of near-horizon work the same way.
 */

#ifndef BLACKHOLE_GAME_ECONOMY_H
#define BLACKHOLE_GAME_ECONOMY_H

#include <algorithm>

namespace game::economy {

inline constexpr double K_SECONDS_PER_HOUR = 3600.0;
inline constexpr double K_SECONDS_PER_DAY = 86400.0;

/** @brief Base coordinate-side value of a completed task: properHours *
 *         (1/dtau_dt) * reliability. An hour of local work deep in the well is
 *         scarce, so it is worth more coordinate-side; a rate of zero (at or
 *         inside the horizon) yields nothing. */
inline double taskYieldUnits(double properTimeCostSec, double properTimeRate, double reliability) {
  const double properHours = properTimeCostSec / K_SECONDS_PER_HOUR;
  return properTimeRate > 0.0 ? (properHours / properTimeRate) * reliability : 0.0;
}

/** @brief Prograde ergoregion depth in [0,1]: 0 at the static limit, 1 at the
 *         horizon. Zero outside the ergoregion, for a retrograde fleet, or a
 *         non-rotating field (where the static limit coincides with the horizon).
 *         Deeper prograde work taps more of the hole's rotational energy. */
inline double ergoregionDepth(double radiusCm, double ergosphereRadiusCm, double horizonCm,
                              bool prograde) {
  if (!prograde || radiusCm >= ergosphereRadiusCm || ergosphereRadiusCm <= horizonCm) {
    return 0.0;
  }
  return std::clamp((ergosphereRadiusCm - radiusCm) / (ergosphereRadiusCm - horizonCm), 0.0, 1.0);
}

/** @brief Yield erosion from the disturbance: 1 / (1 + instability * penalty).
 *         Saturates in (0,1], so productive work slows as instability grows but
 *         never turns negative -- escalating pressure, not a death gate. */
inline double instabilityYieldFactor(double instability, double penaltyPerUnit) {
  return 1.0 / (1.0 + (instability * penaltyPerUnit));
}

/** @brief Prograde ergoregion yield multiplier (>= 1): 1 + bonus * depth. A
 *         bonus of zero, or depth zero, leaves yield unscaled. */
inline double frameDragYieldFactor(double frameDragYieldBonus, double depth) {
  return frameDragYieldBonus > 0.0 ? 1.0 + (frameDragYieldBonus * depth) : 1.0;
}

} // namespace game::economy

#endif // BLACKHOLE_GAME_ECONOMY_H
