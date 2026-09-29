#include <cstddef>
#include <string>

#include <gtest/gtest.h>

#include "game/constellation.h"
#include "game/constellation_view.h"
#include "game/desktop_game.h"
#include "game/first_play_briefing.h"
#include "game/fleet.h"

namespace {

// evaluateBriefing takes the session by const reference, so evaluation cannot
// touch game state; this checks the shape and the ASCII-only player text.
game::Briefing evaluateChecked(const game::DesktopGame &session) {
  game::Briefing briefing = game::evaluateBriefing(session);
  EXPECT_EQ(briefing.steps.size(), 5U);
  for (const game::BriefingStep &step : briefing.steps) {
    for (const char character : step.title) {
      EXPECT_LT(static_cast<unsigned char>(character), 128U);
    }
    for (const char character : step.body) {
      EXPECT_LT(static_cast<unsigned char>(character), 128U);
    }
  }
  return briefing;
}

TEST(FirstPlayBriefing, OrdersSignalsAndReportsAdvanceTheBriefing) {
  game::DesktopGame session(9);
  game::Briefing briefing = evaluateChecked(session);
  EXPECT_EQ(briefing.currentIndex, 0U);

  const game::FleetId fleet = session.snapshot().fleets.front().id;
  const game::ConstellationCommand order{.fleet = fleet, .targetSystem = 1, .targetBand = 2};
  const game::OrderPreview preview = session.preview(order);
  ASSERT_EQ(preview.rejection, game::OrderRejection::None);
  ASSERT_GT(preview.effectTurn, session.snapshot().turn);
  ASSERT_EQ(session.issue(order), game::OrderRejection::None);
  briefing = evaluateChecked(session);
  EXPECT_TRUE(briefing.steps.at(0).complete);
  EXPECT_FALSE(briefing.steps.at(1).complete);
  EXPECT_EQ(briefing.currentIndex, 1U);

  while (session.snapshot().turn < preview.effectTurn) {
    session.advanceTurn();
    evaluateChecked(session);
  }
  briefing = evaluateChecked(session);
  EXPECT_TRUE(briefing.steps.at(1).complete);

  for (int turn = 0; turn < 600 && !briefing.steps.at(2).complete; ++turn) {
    session.advanceTurn();
    briefing = evaluateChecked(session);
  }
  ASSERT_TRUE(briefing.steps.at(2).complete);
  const game::ConstellationViewSnapshot snapshot = session.snapshot();
  const std::string reportTurn =
      "Report turn " + std::to_string(snapshot.fleets.front().reportedTurn);
  EXPECT_NE(briefing.steps.at(2).body.find(reportTurn), std::string::npos);
  EXPECT_NE(briefing.steps.at(2).body.find("current turn " + std::to_string(snapshot.turn)),
            std::string::npos);
}

TEST(FirstPlayBriefing, ObservationsAndCommitmentsUsePlayerRecords) {
  game::DesktopGame session(9);
  const game::ConstellationViewSnapshot initial = session.snapshot();
  for (std::size_t index = 0; index < 3; ++index) {
    const game::ConstellationCommand order{
        .fleet = initial.fleets.at(index).id, .targetSystem = 1, .targetBand = 2};
    ASSERT_EQ(session.issue(order), game::OrderRejection::None);
  }
  game::Briefing briefing = evaluateChecked(session);
  EXPECT_TRUE(briefing.steps.at(4).complete);
  for (int turn = 0; turn < 600 && !briefing.steps.at(3).complete; ++turn) {
    session.advanceTurn();
    briefing = evaluateChecked(session);
  }
  EXPECT_TRUE(briefing.steps.at(3).complete);
}

} // namespace
