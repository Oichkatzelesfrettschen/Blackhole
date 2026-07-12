/**
 * @file campaign_panels.h
 * @brief Singularity: GOROROBA windows: campaign control, order composer, intel log,
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
/** @brief A selectable strategic-map backdrop: a name, its GL texture (0 =
 *         the procedural starfield), and the credit line drawn over it. Built
 *         by main from loaded textures. */
struct CampaignBackdrop {
  const char *name = "";
  unsigned int textureId = 0;
  const char *credit = "";
};

struct CampaignUiState {
  bool windowsOpen = false;
  game::FleetId selectedFleet = game::K_INVALID_FLEET_ID;
  int composerTargetBand = 0;
  game::OrbitLane composerLane = game::OrbitLane::Prograde;
  float composerCostHours = 24.0f;
  bool lastCommandAccepted = true;
  bool lastCommandValid = true; ///< False once a command has been rejected (shows feedback).
  int selectedBackdrop = 0;     ///< Index into the backdrop list passed to renderCampaignWindows.
};

/** @brief Reads BLACKHOLE_CAMPAIGN=1 to open the campaign windows at startup. */
void initCampaignUiFromEnv(CampaignUiState &uiState);

/** @brief Draws the Campaign window (always, it hosts the enable toggle) and,
 *         when enabled, the Strategic Map and Intel windows. backdrops is the
 *         selectable map-backdrop list (null/empty = procedural starfield); the
 *         panel offers a picker and draws the chosen one behind the map. */
void renderCampaignWindows(game::CampaignSession &session, CampaignUiState &uiState,
                           const CampaignBackdrop *backdrops = nullptr, int backdropCount = 0);

} // namespace ui

#endif // BLACKHOLE_UI_CAMPAIGN_PANELS_H
