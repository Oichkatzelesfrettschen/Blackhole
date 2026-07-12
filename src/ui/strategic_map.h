/**
 * @file strategic_map.h
 * @brief ImDrawList orbital map: horizon core, rate-colored bands, fleet
 *        markers, and signals in flight.
 */

#ifndef BLACKHOLE_UI_STRATEGIC_MAP_H
#define BLACKHOLE_UI_STRATEGIC_MAP_H

#include "game/campaign_view.h"

namespace ui {

struct CampaignUiState;

/** @brief Draws the Strategic Map window from the view snapshot. Clicking a
 *         fleet marker selects it into uiState.selectedFleet; the click is
 *         consumed by an ImGui invisible button, never by the scene camera. */
void renderStrategicMap(const game::CampaignViewSnapshot &view, CampaignUiState &uiState);

} // namespace ui

#endif // BLACKHOLE_UI_STRATEGIC_MAP_H
