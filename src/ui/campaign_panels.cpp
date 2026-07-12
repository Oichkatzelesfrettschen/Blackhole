/**
 * @file campaign_panels.cpp
 * @brief Horizon Command campaign windows implementation.
 */

#include "ui/campaign_panels.h"

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <ranges>

#include <imgui.h>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/fleet.h"
#include "ui/strategic_map.h"

namespace ui {

namespace {

constexpr double K_SECONDS_PER_DAY = 86400.0;

double days(double seconds) { return seconds / K_SECONDS_PER_DAY; }

void renderTimeLedger(const game::CampaignViewSnapshot &view) {
  ImGui::Text("turn %lld  |  t_coordinate %.1f d  |  authority dtau/dt %.4f  |  spin a* %.2f",
              static_cast<long long>(view.turn), days(view.coordinateTimeSec),
              view.authorityProperTimeRate, view.spinDimensionless);
  ImGui::TextDisabled("orders in flight: %zu   reports in flight: %zu   intel: %zu",
                      view.ordersInFlight.size(), view.reportsInFlight.size(),
                      view.intel.size());
  if (view.status == game::CampaignStatus::Won) {
    ImGui::TextColored(ImVec4(0.4f, 1.0f, 0.5f, 1.0f), "VICTORY -- objective banked on turn %lld",
                       static_cast<long long>(view.turn));
  } else if (view.status == game::CampaignStatus::Lost) {
    ImGui::TextColored(ImVec4(1.0f, 0.4f, 0.4f, 1.0f), "DEFEAT -- deadline t%lld passed",
                       static_cast<long long>(view.deadlineTurn));
  } else if (view.victoryEnergyUnits > 0.0) {
    const auto fraction = static_cast<float>(view.energyUnits / view.victoryEnergyUnits);
    char objective[96];
    static_cast<void>(std::snprintf(objective, sizeof(objective),
                                    "energy %.1f / %.0f  (deadline t%lld)", view.energyUnits,
                                    view.victoryEnergyUnits,
                                    static_cast<long long>(view.deadlineTurn)));
    ImGui::ProgressBar(fraction, ImVec2(-1.0f, 0.0f), objective);
  } else {
    ImGui::TextDisabled("energy banked: %.1f (no objective set)", view.energyUnits);
  }
}

void renderFleetRoster(const game::CampaignViewSnapshot &view, CampaignUiState &uiState) {
  if (!ImGui::BeginTable("fleet_roster", 8,
                         ImGuiTableFlags_RowBg | ImGuiTableFlags_BordersInnerV |
                             ImGuiTableFlags_SizingStretchProp)) {
    return;
  }
  ImGui::TableSetupColumn("fleet");
  ImGui::TableSetupColumn("band");
  ImGui::TableSetupColumn("dtau/dt");
  ImGui::TableSetupColumn("tau (d)");
  ImGui::TableSetupColumn("tasks p/a/c");
  ImGui::TableSetupColumn("fuel");
  ImGui::TableSetupColumn("reliability");
  ImGui::TableSetupColumn("lane");
  ImGui::TableHeadersRow();
  for (const game::FleetView &fleet : view.fleets) {
    ImGui::TableNextRow();
    ImGui::TableNextColumn();
    char rowLabel[48];
    static_cast<void>(std::snprintf(rowLabel, sizeof(rowLabel), "%u %s##fleet%u", fleet.id,
                  game::capabilityName(fleet.capability), fleet.id));
    const bool selected = fleet.id == uiState.selectedFleet;
    if (ImGui::Selectable(rowLabel, selected,
                          ImGuiSelectableFlags_SpanAllColumns |
                              ImGuiSelectableFlags_AllowOverlap)) {
      uiState.selectedFleet = fleet.id;
    }
    ImGui::TableNextColumn();
    ImGui::Text("%d", fleet.bandIndex);
    ImGui::TableNextColumn();
    ImGui::Text("%.4f", fleet.properTimeRate);
    ImGui::TableNextColumn();
    ImGui::Text("%.2f", days(fleet.properTimeSec));
    ImGui::TableNextColumn();
    ImGui::Text("%u/%u/%u", fleet.pendingTasks, fleet.activeTasks, fleet.completedTasks);
    ImGui::TableNextColumn();
    ImGui::Text("%.0f", fleet.fuelUnits);
    ImGui::TableNextColumn();
    ImGui::Text("%.2f", fleet.reliability);
    ImGui::TableNextColumn();
    ImGui::Text("%s", game::laneName(fleet.lane));
  }
  ImGui::EndTable();
}

void renderOrderComposer(game::CampaignSession &session, const game::CampaignViewSnapshot &view,
                         CampaignUiState &uiState) {
  ImGui::SeparatorText("Order composer");
  if (view.status != game::CampaignStatus::Ongoing) {
    ImGui::TextDisabled("campaign decided -- no further orders");
    return;
  }
  if (uiState.selectedFleet == game::K_INVALID_FLEET_ID) {
    ImGui::TextDisabled("select a fleet (roster row or map marker)");
    return;
  }
  ImGui::Text("fleet %u selected", uiState.selectedFleet);

  char bandPreview[64];
  static_cast<void>(std::snprintf(bandPreview, sizeof(bandPreview), "band %d", uiState.composerTargetBand));
  if (ImGui::BeginCombo("target band", bandPreview)) {
    for (const game::BandView &band : view.bands) {
      char bandLabel[96];
      if (band.validStation) {
        static_cast<void>(std::snprintf(bandLabel, sizeof(bandLabel), "band %d  (dtau/dt %.3f, delay %.1f d)",
                      band.index, band.properTimeRate,
                      band.delayToAuthoritySec / K_SECONDS_PER_DAY));
      } else {
        static_cast<void>(std::snprintf(bandLabel, sizeof(bandLabel), "band %d  (FORBIDDEN)", band.index));
      }
      if (ImGui::Selectable(bandLabel, band.index == uiState.composerTargetBand)) {
        uiState.composerTargetBand = band.index;
      }
    }
    ImGui::EndCombo();
  }
  // Lane selector: retrograde is offered but the campaign rejects it inside the
  // ergosphere, surfacing the frame-dragging rule as a failed order.
  int laneChoice = uiState.composerLane == game::OrbitLane::Retrograde ? 1 : 0;
  ImGui::TextUnformatted("lane");
  ImGui::SameLine();
  ImGui::RadioButton("prograde", &laneChoice, 0);
  ImGui::SameLine();
  ImGui::RadioButton("retrograde", &laneChoice, 1);
  uiState.composerLane = laneChoice == 1 ? game::OrbitLane::Retrograde : game::OrbitLane::Prograde;
  if (ImGui::Button("Redeploy fleet")) {
    uiState.lastCommandAccepted = session.issuePlaceFleet(
        uiState.selectedFleet, uiState.composerTargetBand, uiState.composerLane);
    uiState.lastCommandValid = true;
  }

  ImGui::SliderFloat("task cost (proper hours)", &uiState.composerCostHours, 1.0f, 500.0f,
                     "%.0f h", ImGuiSliderFlags_Logarithmic);
  ImGui::SameLine();
  if (ImGui::Button("Assign task")) {
    uiState.lastCommandAccepted = session.issueAssignTask(
        uiState.selectedFleet, static_cast<double>(uiState.composerCostHours));
    uiState.lastCommandValid = true;
  }

  if (uiState.lastCommandValid && !uiState.lastCommandAccepted) {
    ImGui::TextColored(ImVec4(1.0f, 0.4f, 0.4f, 1.0f),
                       "order rejected (horizon, retrograde-in-ergosphere, or out of fuel)");
  }
}

void renderIntelWindow(const game::CampaignViewSnapshot &view) {
  ImGui::SetNextWindowPos(ImVec2(980.0f, 40.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(420.0f, 300.0f), ImGuiCond_FirstUseEver);
  if (!ImGui::Begin("Campaign Intel", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::End();
    return;
  }
  ImGui::SeparatorText("Signals in flight");
  for (const game::OrderInFlightView &order : view.ordersInFlight) {
    ImGui::Text("order -> fleet %u  (issued t%lld, lands t%lld)", order.fleet,
                static_cast<long long>(order.issueTurn), static_cast<long long>(order.effectTurn));
  }
  for (const game::ReportInFlightView &report : view.reportsInFlight) {
    ImGui::Text("report <- fleet %u task %u  (done t%lld, arrives t%lld)", report.fleet,
                report.task, static_cast<long long>(report.completedTurn),
                static_cast<long long>(report.effectTurn));
  }
  if (view.ordersInFlight.empty() && view.reportsInFlight.empty()) {
    ImGui::TextDisabled("none");
  }

  ImGui::SeparatorText("Intel log (authority knowledge)");
  if (view.intel.empty()) {
    ImGui::TextDisabled("nothing learned yet");
  }
  // Latest first: the newest arrival is what the player acts on.
  for (const game::IntelView &report : std::ranges::reverse_view(view.intel)) {
    ImGui::Text("t%lld: fleet %u completed task %u at t%lld (+%.1f energy, %lld turns stale)",
                static_cast<long long>(report.receivedTurn), report.fleet, report.task,
                static_cast<long long>(report.completedTurn), report.yieldUnits,
                static_cast<long long>(report.receivedTurn - report.completedTurn));
  }
  ImGui::End();
}

} // namespace

void initCampaignUiFromEnv(CampaignUiState &uiState) {
  if (const char *campaignEnv = std::getenv("BLACKHOLE_CAMPAIGN")) {
    uiState.windowsOpen = (std::strcmp(campaignEnv, "0") != 0);
  }
}

void renderCampaignWindows(game::CampaignSession &session, CampaignUiState &uiState) {
  ImGui::SetNextWindowPos(ImVec2(420.0f, 40.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(540.0f, 420.0f), ImGuiCond_FirstUseEver);
  if (ImGui::Begin("Campaign", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Horizon Command", &uiState.windowsOpen);
    if (uiState.windowsOpen) {
      const game::CampaignViewSnapshot view = session.state().renderSnapshot();
      renderTimeLedger(view);
      if (ImGui::Button("Advance turn")) {
        session.state().advanceTurn();
      }
      ImGui::SameLine();
      if (ImGui::Button("Advance 5")) {
        session.state().advanceTurns(5);
      }
      ImGui::SameLine();
      if (ImGui::Button("Advance 25")) {
        session.state().advanceTurns(25);
      }
      ImGui::SeparatorText("Fleet roster");
      renderFleetRoster(view, uiState);
      renderOrderComposer(session, view, uiState);
    } else {
      ImGui::TextDisabled("enable to command fleets around the black hole");
    }
  }
  ImGui::End();

  if (uiState.windowsOpen) {
    // A fresh snapshot after any button above mutated the campaign this frame.
    const game::CampaignViewSnapshot view = session.state().renderSnapshot();
    renderStrategicMap(view, uiState);
    renderIntelWindow(view);
  }
}

} // namespace ui
