/**
 * @file campaign_ui_state_test.cpp
 * @brief Falsification gates for the panel state that names one session's
 *        entities: replacing the session clears it, and the composer clamps
 *        it to the session it draws.
 */

#include <gtest/gtest.h>

#include <string>

#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "ui/campaign_panels.h"

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

  const game::EventLoadResult loaded = game::loadEventSetFile(
      std::string(BLACKHOLE_SOURCE_DIR) + "/assets/events/host_goes_dark.json");
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
