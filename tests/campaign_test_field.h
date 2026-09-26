/**
 * @file campaign_test_field.h
 * @brief Shared programmable TimeField and canonical fake config for the
 *        campaign test suite.
 *
 * The fake makes every arrival turn exact by construction: delay is the plain
 * radial separation in seconds, the proper-time rate is 0.1 below radius 970
 * and 1.0 at or above it, and the config runs one-second turns. Authority at
 * 1000 with bands {960, 995} gives delays of 40 and 5 turns and rates of 0.1
 * and 1.0 -- every campaign test reasons against these numbers.
 */

#ifndef BLACKHOLE_TESTS_CAMPAIGN_TEST_FIELD_H
#define BLACKHOLE_TESTS_CAMPAIGN_TEST_FIELD_H

#include <cmath>

#include "game/campaign.h"
#include "game/time_field.h"

namespace campaign_test {

class FakeTimeField final : public game::TimeField {
public:
  [[nodiscard]] double properTimeRate(double radiusCm, game::Observer /*observer*/) const override {
    return radiusCm < 970.0 ? 0.1 : 1.0;
  }
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override {
    return std::fabs(toRadiusCm - fromRadiusCm);
  }
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override {
    return std::isfinite(radiusCm) && radiusCm > 1.0;
  }
};

/** @brief A fake with a rotating field bolted on: a static limit at radius 970
 *         (so band 960 sits inside the ergoregion, band 995 outside) and a
 *         frame-drag rate that rises inward. Lets the lane gate and the
 *         prograde ergoregion bonus be reasoned about with round numbers. */
class FakeSpinningField final : public game::TimeField {
public:
  [[nodiscard]] double properTimeRate(double radiusCm, game::Observer /*observer*/) const override {
    return radiusCm < 970.0 ? 0.1 : 1.0;
  }
  [[nodiscard]] double signalDelaySec(double fromRadiusCm, double toRadiusCm) const override {
    return std::fabs(toRadiusCm - fromRadiusCm);
  }
  [[nodiscard]] bool isValidStationRadius(double radiusCm) const override {
    return std::isfinite(radiusCm) && radiusCm > 950.0; // horizon at 950
  }
  [[nodiscard]] double innerBoundaryRadiusCm() const override { return 950.0; }
  [[nodiscard]] double ergosphereRadiusCm() const override { return 970.0; }
  [[nodiscard]] double frameDragRateRadPerSec(double radiusCm) const override {
    return radiusCm > 950.0 ? 1.0 / (radiusCm - 950.0) : 0.0;
  }
  [[nodiscard]] double spinDimensionless() const override { return 0.9; }
};

inline game::CampaignConfig fakeConfig() {
  game::CampaignConfig config;
  config.seed = 11;
  config.secondsPerTurn = 1.0;
  config.authorityRadiusCm = 1000.0; // rate 1.0 at the authority station
  config.bandRadiusCm = {960.0, 995.0}; // near: delay 40, rate 0.1; far: delay 5, rate 1.0
  return config;
}

} // namespace campaign_test

#endif // BLACKHOLE_TESTS_CAMPAIGN_TEST_FIELD_H
