/**
 * @file campaign_panels.h
 * @brief Horizon Command windows: campaign control, order composer, intel log,
 *        and the strategic-map host call.
 *
 * The panels read the campaign exclusively through
 * CampaignState::renderSnapshot() and mutate it exclusively through the
 * CampaignSession command helpers plus advanceTurn -- they never reach into
 * campaign internals and never touch RenderState. All windows live inside the
 * existing ImGui dockspace; every mouse interaction is consumed by ImGui, so
 * the scene camera never sees a map click.
 */

#ifndef BLACKHOLE_UI_CAMPAIGN_PANELS_H
#define BLACKHOLE_UI_CAMPAIGN_PANELS_H

#include "game/campaign_session.h"
#include "game/fleet.h"

namespace ui {

/** @brief Panel-local UI state: window visibility, map selection, and the
 *         order composer's staged values. Owned by main beside the session. */
struct CampaignUiState {
  bool windowsOpen = false;
  game::FleetId selectedFleet = game::K_INVALID_FLEET_ID;
  int composerTargetBand = 0;
  game::OrbitLane composerLane = game::OrbitLane::Prograde;
  float composerCostHours = 24.0f;
  bool lastCommandAccepted = true;
  bool lastCommandValid = true; ///< False once a command has been rejected (shows feedback).
};

/** @brief Reads BLACKHOLE_CAMPAIGN=1 to open the campaign windows at startup. */
void initCampaignUiFromEnv(CampaignUiState &uiState);

/** @brief Draws the Campaign window (always, it hosts the enable toggle) and,
 *         when enabled, the Strategic Map and Intel windows. */
void renderCampaignWindows(game::CampaignSession &session, CampaignUiState &uiState);

} // namespace ui

#endif // BLACKHOLE_UI_CAMPAIGN_PANELS_H
