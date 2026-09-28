/**
 * @file campaign_ui_state_test.cpp
 * @brief Falsification gates for the panel state that names one session's
 *        entities: replacing the session clears it, and the composer clamps
 *        it to the session it draws.
 */

#include <memory>
#include <string>

#include <gtest/gtest.h>

#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "ui/campaign_panels.h"
#include "ui/ux_explanations.h"

TEST(CampaignUiState, FocusAndTechnologyDiscloseTheirEffects) {
  EXPECT_NE(ui::K_FOCUS_EFFECT_TEXT.find("perceived information"), std::string_view::npos);
  EXPECT_NE(ui::K_FOCUS_EFFECT_TEXT.find("order origin"), std::string_view::npos);
  EXPECT_EQ(ui::technologyMilestoneText("Signal lock", 1, 1, 5),
            "Signal lock (1 point): raises the colony outcome tier");
  EXPECT_EQ(ui::technologyMilestoneText("Horizon engineering", 100, 5, 5),
            "Horizon engineering (100 points): reaches the colony victory objective");
  EXPECT_EQ(ui::campaignPauseReason("collapse", 17),
            "collapse arrival at the acting station on turn 17; read the inbox.");
}

TEST(CampaignUiState, MapLabelsStayInsideTheCanvas) {
  const ui::BoundedLabelPosition right =
      ui::boundedMapLabel(190.0f, 90.0f, 45.0f, 12.0f, 10.0f, 20.0f, 200.0f, 100.0f);
  EXPECT_FLOAT_EQ(right.x, 165.0f);
  EXPECT_FLOAT_EQ(right.y, 90.0f);
  const ui::BoundedLabelPosition bottom =
      ui::boundedMapLabel(-20.0f, 130.0f, 45.0f, 12.0f, 10.0f, 20.0f, 200.0f, 100.0f);
  EXPECT_FLOAT_EQ(bottom.x, 10.0f);
  EXPECT_FLOAT_EQ(bottom.y, 108.0f);
}

// Falsifier: a fleet id or band index chosen in the six-fleet, four-band
// default session surviving into the colony story (one fleet, two bands),
// where the composer would address a fleet and band that do not exist.
TEST(CampaignUiState, ReplacingTheSessionClearsItsSelection) {
  ui::CampaignUiState uiState;
  uiState.selectedFleet = 6;
  uiState.composerTargetBand = 3;
  uiState.composerLane = game::OrbitLane::Retrograde;
  uiState.composerStation = game::StationKeeping::Hover;
  uiState.lastCommandAccepted = false;
  uiState.composerCostHours = 12.0f;
  ui::resetSessionSelection(uiState);
  EXPECT_EQ(uiState.selectedFleet, game::K_INVALID_FLEET_ID);
  EXPECT_EQ(uiState.composerTargetBand, 0);
  EXPECT_EQ(uiState.composerLane, game::OrbitLane::Prograde);
  EXPECT_EQ(uiState.composerStation, game::StationKeeping::Orbit);
  EXPECT_TRUE(uiState.lastCommandAccepted);
  EXPECT_FLOAT_EQ(uiState.composerCostHours, 12.0f); // a preference, kept

  const game::EventLoadResult loaded = game::loadEventSetFile(std::string(BLACKHOLE_SOURCE_DIR) +
                                                              "/assets/events/host_goes_dark.json");
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  const game::CampaignSession colony(1, loaded.story, game::K_MILLER_BAND);
  const game::CampaignViewSnapshot view =
      colony.state().perceivedSnapshot(game::K_FIRST_COLONY_NODE);
  uiState.selectedFleet = 6;
  uiState.composerTargetBand = 3;
  ui::clampSelectionToView(uiState, view);
  EXPECT_EQ(uiState.selectedFleet, game::K_INVALID_FLEET_ID);
  EXPECT_EQ(uiState.composerTargetBand, 1);
  uiState.selectedFleet = 1; // the colony story's survey fleet
  ui::clampSelectionToView(uiState, view);
  EXPECT_EQ(uiState.selectedFleet, 1U);
}

// Falsifier: the composer offering orders from a station that can send none --
// the shallow colony after its 365-local-day mission (about 371 turns at
// dtau/dt 0.985) -- or refusing them before then.
TEST(CampaignUiState, ComposerIsBlockedAtADarkStation) {
  const game::EventLoadResult loaded = game::loadEventSetFile(std::string(BLACKHOLE_SOURCE_DIR) +
                                                              "/assets/events/host_goes_dark.json");
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  game::CampaignSession colony(1, loaded.story, game::K_SURVEY_BAND);
  ui::CampaignUiState uiState;
  uiState.focusNode = game::K_FIRST_COLONY_NODE;
  colony.state().advanceTurns(300);
  EXPECT_EQ(ui::composerBlockedReason(colony.state().perceivedSnapshot(game::K_FIRST_COLONY_NODE),
                                      uiState),
            nullptr);
  colony.state().advanceTurns(100);
  ASSERT_TRUE(colony.state().nodes().at(game::K_FIRST_COLONY_NODE).dark());
  EXPECT_NE(ui::composerBlockedReason(colony.state().perceivedSnapshot(game::K_FIRST_COLONY_NODE),
                                      uiState),
            nullptr);
  EXPECT_FALSE(colony.issueAssignTask(1, 1.0, game::K_FIRST_COLONY_NODE));
}

TEST(CampaignUiState, InferredVictoryShowsUnknownClearTurn) {
  game::CampaignViewSnapshot view;
  view.status = game::CampaignStatus::Won;
  view.clearedTurn = -1;
  EXPECT_EQ(ui::victoryOutcomeText(view),
            "VICTORY -- host energy objective reached (clear turn unknown)");
  const ui::CampaignUiState uiState;
  EXPECT_NE(ui::composerBlockedReason(view, uiState), nullptr);
  view.clearedTurn = 20;
  EXPECT_EQ(ui::victoryOutcomeText(view), "VICTORY -- objective cleared on turn 20");
}

// Falsifier: real time advancing only while the panels are drawn -- the pump
// must run from main every frame on its own (no rendering here at all): ten
// wall seconds at Miller focus are 7 one-day turns.
TEST(CampaignUiState, RealtimePumpRunsWithoutThePanels) {
  const game::EventLoadResult loaded = game::loadEventSetFile(std::string(BLACKHOLE_SOURCE_DIR) +
                                                              "/assets/events/host_goes_dark.json");
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  game::CampaignSession defaultSession(1);
  ui::CampaignUiState uiState;
  uiState.windowsOpen = true;
  uiState.realtime = true;
  uiState.storySession =
      std::make_unique<game::CampaignSession>(1, loaded.story, game::K_MILLER_BAND);
  uiState.focusNode = game::K_FIRST_COLONY_NODE;
  ui::pumpCampaignRealtime(defaultSession, uiState, 10.0);
  EXPECT_EQ(uiState.storySession->state().turn(), 7);
  EXPECT_EQ(defaultSession.state().turn(), 0);
  uiState.realtime = false;
  ui::pumpCampaignRealtime(defaultSession, uiState, 10.0);
  EXPECT_EQ(uiState.storySession->state().turn(), 7);
}
