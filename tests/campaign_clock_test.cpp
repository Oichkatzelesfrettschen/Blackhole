/**
 * @file campaign_clock_test.cpp
 * @brief Falsification gates for the campaign clocks: proper-time rate range
 *        and monotonicity, derived coordinate time, ceil quantization, and
 *        batch-vs-single-step advance order-determinism.
 */

#include <gtest/gtest.h>

#include <cstdint>
#include <vector>

#include "game/blackhole_time_field.h"
#include "game/campaign.h"
#include "game/fleet.h"
#include "game/temporal_clock.h"

namespace {

constexpr double K_SOLAR_MASS_G = 1.989e33;
constexpr double K_M87_MASS_G = 6.5e9 * K_SOLAR_MASS_G;

game::CampaignConfig canonicalConfig(const game::BlackholeTimeField &field) {
  const double horizonCm = field.horizonRadiusCm();
  game::CampaignConfig config;
  config.seed = 7;
  config.secondsPerTurn = 3600.0;
  config.authorityRadiusCm = 200.0 * horizonCm;
  config.bandRadiusCm = {3.0 * horizonCm, 10.0 * horizonCm, 50.0 * horizonCm};
  return config;
}

void populateCanonicalScenario(game::CampaignState &campaign) {
  const game::FleetId inner = campaign.addFleet(game::FleetCapability::Extraction, 0);
  const game::FleetId middle = campaign.addFleet(game::FleetCapability::Fabrication, 1);
  const game::FleetId outer = campaign.addFleet(game::FleetCapability::Verification, 2);
  ASSERT_NE(inner, game::K_INVALID_FLEET_ID);
  ASSERT_NE(middle, game::K_INVALID_FLEET_ID);
  ASSERT_NE(outer, game::K_INVALID_FLEET_ID);
  game::Command assign;
  assign.type = game::CommandType::AssignTask;
  assign.properTimeCostSec = 5.0 * 3600.0;
  for (const game::FleetId fleetId : {inner, middle, outer}) {
    assign.fleet = fleetId;
    ASSERT_TRUE(campaign.issueCommand(assign));
  }
}

} // namespace

TEST(CampaignClock, ProperTimeRateStaysInUnitIntervalAndRisesWithRadius) {
  const game::BlackholeTimeField field(K_M87_MASS_G);
  const double horizonCm = field.horizonRadiusCm();
  double previousRate = 0.0;
  for (const double multiple : {1.0001, 1.01, 1.5, 3.0, 10.0, 50.0, 200.0, 1000.0}) {
    const double radiusCm = multiple * horizonCm;
    const double rate = field.properTimeRate(radiusCm);
    EXPECT_GT(rate, 0.0) << "radius multiple " << multiple;
    EXPECT_LE(rate, 1.0) << "radius multiple " << multiple;
    EXPECT_GT(rate, previousRate) << "rate must rise monotonically with radius";
    previousRate = rate;
  }
}

TEST(CampaignClock, CoordinateTimeIsDerivedNotAccumulated) {
  game::TemporalClock clock(3600.0);
  EXPECT_EQ(clock.turn(), 0);
  EXPECT_DOUBLE_EQ(clock.coordinateTimeSec(), 0.0);
  clock.advance(5);
  EXPECT_EQ(clock.turn(), 5);
  EXPECT_DOUBLE_EQ(clock.coordinateTimeSec(), 5.0 * 3600.0);
}

TEST(CampaignClock, CeilTurnsNeverDeliversEarly) {
  const game::TemporalClock clock(3600.0);
  EXPECT_EQ(clock.ceilTurns(0.0), 0);
  EXPECT_EQ(clock.ceilTurns(1.0), 1);
  EXPECT_EQ(clock.ceilTurns(3600.0), 1);
  EXPECT_EQ(clock.ceilTurns(3600.0001), 2);
  EXPECT_EQ(clock.ceilTurns(7200.0), 2);
}

TEST(CampaignClock, ProperDeltaIsRateTimesTurnLength) {
  EXPECT_DOUBLE_EQ(game::properDeltaSec(0.25, 3600.0), 900.0);
  EXPECT_DOUBLE_EQ(game::properDeltaSec(1.0, 3600.0), 3600.0);
}

TEST(CampaignClock, BatchAdvanceMatchesSingleStepAdvanceByteForByte) {
  const game::BlackholeTimeField field(K_M87_MASS_G);

  game::CampaignState batched(canonicalConfig(field), field);
  ASSERT_TRUE(batched.valid());
  populateCanonicalScenario(batched);

  game::CampaignState stepped(canonicalConfig(field), field);
  ASSERT_TRUE(stepped.valid());
  populateCanonicalScenario(stepped);

  constexpr std::int64_t turnCount = 10;
  batched.advanceTurns(turnCount);
  for (std::int64_t step = 0; step < turnCount; ++step) {
    stepped.advanceTurn();
  }

  EXPECT_EQ(batched.turn(), stepped.turn());
  const std::vector<std::uint8_t> batchedBytes = batched.serializeState();
  const std::vector<std::uint8_t> steppedBytes = stepped.serializeState();
  EXPECT_EQ(batchedBytes, steppedBytes);
  EXPECT_EQ(batched.stateDigest(), stepped.stateDigest());
}
