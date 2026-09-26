/**
 * @file campaign_panels.h
 * @brief Singularity: GOROROBA windows: campaign control, order composer, intel log,
 *        and the strategic-map host call.
 *
 * The panels read the campaign exclusively through
 * CampaignState::perceivedSnapshot() at the focused station (the full
 * snapshot at the authority, only what has arrived at a colony) and mutate it
 * exclusively through the CampaignSession command helpers plus advanceTurn --
 * they never reach into
 * campaign internals and never touch RenderState. All windows live inside the
 * existing ImGui dockspace; every mouse interaction is consumed by ImGui, so
 * the scene camera never sees a map click.
 */

#ifndef BLACKHOLE_UI_CAMPAIGN_PANELS_H
#define BLACKHOLE_UI_CAMPAIGN_PANELS_H

#include <algorithm>
#include <memory>
#include <string>

#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/inbox.h"
#include "game/realtime_driver.h"

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
  game::StationKeeping composerStation = game::StationKeeping::Orbit;
  float composerCostHours = 24.0f;
  bool lastCommandAccepted = true;
  bool lastCommandValid = true; ///< False once a command has been rejected (shows feedback).
  int selectedBackdrop = 0;     ///< Index into the backdrop list passed to renderCampaignWindows.

  // The Miller colony story and real-time play. The story session, once
  // started, replaces the default session in every window; the driver and the
  // inbox are player-side state outside the deterministic campaign.
  std::unique_ptr<game::CampaignSession> storySession;
  std::string storyError;
  bool realtime = false;
  float localSecondsPerWallSecond = 1.0f; ///< 1 = real time at the focused station.
  game::RealtimeDriver driver;
  game::Inbox inbox{game::K_FIRST_COLONY_NODE};    ///< The colony's inbox.
  game::Inbox hostInbox{game::K_AUTHORITY_NODE};   ///< The host's inbox.
  game::NodeId focusNode = game::K_FIRST_COLONY_NODE;
  game::NodeId commandOrigin = game::K_AUTHORITY_NODE;
  bool lagging = false;
  bool inboxOpen = true;
};

/** @brief Clears the selection and composer state that names things in one
 *         session (a fleet id, a band index, the last order's feedback), for
 *         when another session replaces it. The player's preferences (task
 *         cost, backdrop, pause categories) are kept. */
inline void resetSessionSelection(CampaignUiState &uiState) {
  uiState.selectedFleet = game::K_INVALID_FLEET_ID;
  uiState.composerTargetBand = 0;
  uiState.composerLane = game::OrbitLane::Prograde;
  uiState.composerStation = game::StationKeeping::Orbit;
  uiState.lastCommandAccepted = true;
  uiState.lastCommandValid = true;
}

/** @brief Drops a selected fleet the view does not list and clamps the target
 *         band to the view's bands, so the composer never names an entity of
 *         another session. */
inline void clampSelectionToView(CampaignUiState &uiState, const game::CampaignViewSnapshot &view) {
  if (std::ranges::none_of(view.fleets, [&uiState](const game::FleetView &fleet) {
        return fleet.id == uiState.selectedFleet;
      })) {
    uiState.selectedFleet = game::K_INVALID_FLEET_ID;
  }
  const int bandCount = static_cast<int>(view.bands.size());
  uiState.composerTargetBand =
      bandCount == 0 ? 0 : std::clamp(uiState.composerTargetBand, 0, bandCount - 1);
}

/** @brief Why the order composer cannot send from the focused station, or
 *         nullptr when it can: the campaign is decided, or the station itself
 *         is dark (the host gone silent, a colony past its mission) and
 *         issueCommand would refuse every order from it. */
[[nodiscard]] inline const char *composerBlockedReason(const game::CampaignViewSnapshot &view,
                                                       const CampaignUiState &uiState) {
  if (view.status == game::CampaignStatus::Ended) {
    return "the deadline has passed -- no further orders";
  }
  if (view.status != game::CampaignStatus::Ongoing) {
    return "campaign decided -- no further orders";
  }
  const auto focus = std::ranges::find(view.nodes, uiState.focusNode, &game::NodeView::id);
  if (focus != view.nodes.end() && focus->dark) {
    return focus->isColony ? "the colony is dark (its mission is over): it can send no orders"
                           : "the host is dark: it can send no orders";
  }
  return nullptr;
}

/** @brief Advances the active session one turn and feeds both stations'
 *         inboxes; true when an arrival this turn at the focused station is
 *         in a pause category. */
bool stepCampaignTurn(game::CampaignSession &session, CampaignUiState &uiState);

/** @brief Runs real time for one frame of `wallDtSec` wall seconds: whole
 *         turns at the focused station's rate, stopping on a flagged arrival.
 *         Called every frame from main whether or not the panels are drawn,
 *         so hiding the UI does not freeze the campaign. */
void pumpCampaignRealtime(game::CampaignSession &defaultSession, CampaignUiState &uiState,
                          double wallDtSec);

/** @brief Reads BLACKHOLE_CAMPAIGN=1 to open the campaign windows at startup.
 *         For desktop captures without synthetic input:
 *         BLACKHOLE_CAMPAIGN_STORY=deep|shallow starts the host story with the
 *         colony on Miller's orbit or the 100M orbit, BLACKHOLE_CAMPAIGN_FOCUS=
 *         colony|host sets the focused station, and
 *         BLACKHOLE_CAMPAIGN_ADVANCE=N advances the story up to N turns
 *         (at most 1e5) as the Advance buttons do, stopping on a flagged
 *         arrival at the focused station, and BLACKHOLE_CAMPAIGN_REALTIME=S
 *         (1..3600) runs real time at S local seconds per wall second. */
void initCampaignUiFromEnv(CampaignUiState &uiState);

/** @brief Draws the Campaign window (always, it hosts the enable toggle) and,
 *         when enabled, the Strategic Map, Intel, Inbox, and Tech windows; in
 *         real-time mode, advances the active session by the frame's wall time. backdrops is the
 *         selectable map-backdrop list (null/empty = procedural starfield); the
 *         panel offers a picker and draws the chosen one behind the map. */
void renderCampaignWindows(game::CampaignSession &session, CampaignUiState &uiState,
                           const CampaignBackdrop *backdrops = nullptr, int backdropCount = 0);

} // namespace ui

#endif // BLACKHOLE_UI_CAMPAIGN_PANELS_H
