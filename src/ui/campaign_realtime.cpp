/**
 * @file campaign_realtime.cpp
 * @brief The campaign's turn stepping and real-time pump, GL-free.
 *
 * The pump runs every frame from main whether or not the panels are drawn,
 * so hiding the UI never freezes the outside world.
 */

#include <vector>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/event.h"
#include "game/realtime_driver.h"
#include "game/station_node.h"
#include "ui/campaign_panels.h"
#include "ui/ux_explanations.h"

namespace ui {

bool stepCampaignTurn(game::CampaignSession &session, CampaignUiState &uiState) {
  session.state().advanceTurn();
  const bool colonyPause = uiState.inbox.sync(session.state().arrivals());
  const bool hostPause = uiState.hostInbox.sync(session.state().arrivals());
  const bool focusPause = uiState.focusNode == game::K_AUTHORITY_NODE ? hostPause : colonyPause;
  if (focusPause) {
    const game::Inbox &focusInbox =
        uiState.focusNode == game::K_AUTHORITY_NODE ? uiState.hostInbox : uiState.inbox;
    if (const auto pauseEntry = focusInbox.lastPauseEntry()) {
      const game::ArrivalRecord &arrival = focusInbox.entries().at(*pauseEntry).arrival;
      uiState.pauseReason =
          campaignPauseReason(game::eventCategoryName(arrival.category), arrival.arrivalTurn);
    }
  }
  return focusPause;
}

void pumpCampaignRealtime(game::CampaignSession &defaultSession, CampaignUiState &uiState,
                          double wallDtSec) {
  if (!uiState.windowsOpen || !uiState.realtime) {
    return;
  }
  game::CampaignSession &session = uiState.storySession ? *uiState.storySession : defaultSession;
  // Wall time enters here and nowhere in the campaign: the driver turns it
  // into whole turns at the focused station's rate, stopping on a flagged
  // arrival's own turn.
  const std::vector<game::StationNode> &nodes = session.state().nodes();
  if (uiState.focusNode < nodes.size()) {
    uiState.driver.setFocusRate(nodes.at(uiState.focusNode).clock.rate());
  }
  const game::RealtimePumpResult pumped = uiState.driver.pump(
      wallDtSec, [&session, &uiState]() { return stepCampaignTurn(session, uiState); });
  uiState.lagging = pumped.lagging;
  if (pumped.pausedByArrival) {
    uiState.inboxOpen = true;
  }
}

} // namespace ui
