#include <cstddef>
#include <cstdint>
#include <memory>
#include <vector>

#include <gtest/gtest.h>

#include "game/campaign_view.h"
#include "game/constellation.h"
#include "game/constellation_view.h"
#include "game/desktop_game.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "ui/constellation_panels.h"

namespace {

void expectCorruptSaveRejected(const std::vector<std::uint8_t> &saved) {
  game::SaveError error = game::SaveError::None;
  std::vector<std::uint8_t> corrupt = saved;
  corrupt.back() ^= 1U;
  EXPECT_EQ(game::DesktopGame::load(corrupt, error), nullptr);
  EXPECT_EQ(error, game::SaveError::DigestMismatch);
  corrupt = saved;
  corrupt.at(4) = 2;
  EXPECT_EQ(game::DesktopGame::load(corrupt, error), nullptr);
  EXPECT_EQ(error, game::SaveError::Schema);
}

TEST(DesktopGame, PreviewUsesKnownFleetAndTypedRejections) {
  game::DesktopGame session(9);
  const game::ConstellationViewSnapshot snapshot = session.snapshot();
  ASSERT_EQ(snapshot.systems.size(), 2U);
  ASSERT_EQ(snapshot.fleets.size(), 4U);
  const game::FleetId fleet = snapshot.fleets.front().id;
  const game::ConstellationCommand invalidFleet{
      .fleet = game::K_INVALID_FLEET_ID, .targetSystem = 0, .targetBand = 2};
  EXPECT_EQ(session.preview(invalidFleet).rejection, game::OrderRejection::UnknownFleet);
  const game::ConstellationCommand invalidBand{.fleet = fleet, .targetSystem = 0, .targetBand = 20};
  EXPECT_EQ(session.issue(invalidBand), game::OrderRejection::InvalidTarget);
  const game::ConstellationCommand order{.fleet = fleet, .targetSystem = 1, .targetBand = 2};
  const game::OrderPreview preview = session.preview(order);
  EXPECT_EQ(preview.rejection, game::OrderRejection::None);
  EXPECT_GT(preview.signalTurns, 0);
  EXPECT_GT(preview.travelTurns, 0);
  EXPECT_EQ(preview.arrivalTurn, preview.effectTurn + preview.travelTurns);
  EXPECT_GT(preview.remainingFuel, 0.0);
  EXPECT_FALSE(preview.riskKnown);
  EXPECT_EQ(session.issue(order), game::OrderRejection::None);
  EXPECT_EQ(session.issue(order), game::OrderRejection::DuplicateOrder);
}

TEST(DesktopGame, FleetReportConfirmsDeliveredOrder) {
  game::DesktopGame session(9);
  const game::FleetId fleet = session.snapshot().fleets.front().id;
  const game::ConstellationCommand order{.fleet = fleet, .targetSystem = 1, .targetBand = 2};
  ASSERT_EQ(session.issue(order), game::OrderRejection::None);
  ASSERT_EQ(session.snapshot().orders.size(), 1U);
  EXPECT_EQ(session.snapshot().orders.front().status, game::PlayerOrderStatus::AwaitingReport);
  for (int turn = 0; turn < 600 && session.snapshot().orders.front().status ==
                                       game::PlayerOrderStatus::AwaitingReport;
       ++turn) {
    session.advanceTurn();
  }
  EXPECT_EQ(session.snapshot().orders.front().status,
            game::PlayerOrderStatus::ConfirmedByFleetReport);
}

TEST(DesktopGame, SaveReplaysEveryTurnAndRejectsCorruptionBeforeReplacement) {
  game::DesktopGame live(17);
  const game::FleetId fleet = live.snapshot().fleets.front().id;
  const game::ConstellationCommand order{
      .fleet = fleet, .targetSystem = 0, .targetBand = 0, .station = game::StationKeeping::Hover};
  ASSERT_EQ(live.issue(order), game::OrderRejection::None);
  for (int turn = 0; turn < 85; ++turn) {
    live.advanceTurn();
  }
  const std::vector<std::uint8_t> saved = live.save();
  game::SaveError error = game::SaveError::None;
  std::unique_ptr<game::DesktopGame> replayed = game::DesktopGame::load(saved, error);
  ASSERT_NE(replayed, nullptr);
  EXPECT_EQ(error, game::SaveError::None);
  EXPECT_EQ(replayed->turnDigests(), live.turnDigests());
  EXPECT_EQ(replayed->state().stateDigest(), live.state().stateDigest());
  EXPECT_EQ(replayed->state().overallStatus(), live.state().overallStatus());
  for (std::size_t system = 0; system < live.snapshot().systems.size(); ++system) {
    EXPECT_EQ(replayed->snapshot().systems.at(system).observationSourceTurn,
              live.snapshot().systems.at(system).observationSourceTurn);
    EXPECT_EQ(replayed->snapshot().systems.at(system).observationArrivalTurn,
              live.snapshot().systems.at(system).observationArrivalTurn);
  }
  expectCorruptSaveRejected(saved);
}

TEST(DesktopGame, FixedSeedRivalAndSelectionPreserveReplay) {
  for (const std::uint64_t seed : {1ULL, 7ULL}) {
    ui::ConstellationUiState view;
    view.session = std::make_unique<game::DesktopGame>(seed);
    game::DesktopGame &live = *view.session;
    game::DesktopGame reference(seed);
    ASSERT_TRUE(ui::selectConstellationSystem(view, live.snapshot(), 1));
    EXPECT_EQ(view.selectedSystem, 1U);
    live.advanceTurn();
    reference.advanceTurn();
    EXPECT_EQ(live.state().stateDigest(), reference.state().stateDigest());
    for (int turn = 0; turn < 1400 && live.state().overallStatus() == game::CampaignStatus::Ongoing;
         ++turn) {
      live.advanceTurn();
    }
    EXPECT_NE(live.state().overallStatus(), game::CampaignStatus::Ongoing);
    game::SaveError error = game::SaveError::None;
    std::unique_ptr<game::DesktopGame> replayed = game::DesktopGame::load(live.save(), error);
    ASSERT_NE(replayed, nullptr);
    EXPECT_EQ(replayed->turnDigests(), live.turnDigests());
    EXPECT_EQ(replayed->state().overallStatus(), live.state().overallStatus());
  }
}

bool isDecisionNotice(game::GameEventKind kind) {
  return kind == game::GameEventKind::FleetReport || kind == game::GameEventKind::ArrivalReport ||
         kind == game::GameEventKind::ControlObservation ||
         kind == game::GameEventKind::ContestedOrUnknown;
}

bool anyDecisionNotice(const std::vector<game::GameEvent> &events, std::size_t first) {
  for (std::size_t index = first; index < events.size(); ++index) {
    if (isDecisionNotice(events.at(index).kind)) {
      return true;
    }
  }
  return false;
}

// Runs one batched advance and the same number of single steps on `stepped`,
// returning the turns advanced; the two sessions must stay digest-identical.
std::int64_t advanceBoth(game::DesktopGame &batched, game::DesktopGame &stepped, std::int64_t cap) {
  const std::int64_t advanced = batched.advanceToNextNotice(cap);
  for (std::int64_t turn = 0; turn < advanced; ++turn) {
    stepped.advanceTurn();
  }
  EXPECT_EQ(batched.state().stateDigest(), stepped.state().stateDigest());
  return advanced;
}

TEST(DesktopGame, AdvanceToNextNoticeMatchesSingleSteppingAndStopsOnNotices) {
  constexpr std::int64_t kCap = 250;
  game::DesktopGame batched(3);
  game::DesktopGame stepped(3);
  const game::FleetId fleet = batched.snapshot().fleets.front().id;
  const game::ConstellationCommand order{.fleet = fleet, .targetSystem = 1, .targetBand = 2};
  ASSERT_EQ(batched.issue(order), game::OrderRejection::None);
  ASSERT_EQ(stepped.issue(order), game::OrderRejection::None);
  int stops = 0;
  while (batched.state().overallStatus() == game::CampaignStatus::Ongoing && stops < 2000) {
    const std::size_t eventsBefore = batched.events().size();
    const std::int64_t advanced = advanceBoth(batched, stepped, kCap);
    ASSERT_TRUE(advanced > 0 && advanced <= kCap);
    const bool stoppedEarly =
        advanced < kCap && batched.state().overallStatus() == game::CampaignStatus::Ongoing;
    EXPECT_TRUE(!stoppedEarly || anyDecisionNotice(batched.events(), eventsBefore));
    ++stops;
  }
  EXPECT_NE(batched.state().overallStatus(), game::CampaignStatus::Ongoing);
  EXPECT_EQ(batched.turnDigests(), stepped.turnDigests());
  EXPECT_EQ(batched.advanceToNextNotice(kCap), 0);
  EXPECT_LT(stops, static_cast<int>(batched.turnDigests().size()));
}

} // namespace
