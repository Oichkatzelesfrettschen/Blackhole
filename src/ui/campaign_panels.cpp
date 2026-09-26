/**
 * @file campaign_panels.cpp
 * @brief Singularity: GOROROBA campaign windows implementation.
 */

#include "ui/campaign_panels.h"

#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <format>
#include <ranges>
#include <string>

#include <imgui.h>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "ui/strategic_map.h"

namespace ui {

namespace {

constexpr double K_SECONDS_PER_DAY = 86400.0;

double days(double seconds) { return seconds / K_SECONDS_PER_DAY; }

const char *capabilityEffectText(game::FleetCapability capability) {
  switch (capability) {
  case game::FleetCapability::Research:
    return "high yield";
  case game::FleetCapability::Fabrication:
    return "refuels band";
  case game::FleetCapability::Relay:
    return "cuts delay";
  case game::FleetCapability::Verification:
    return "restores band";
  case game::FleetCapability::Extraction:
    return "top yield";
  }
  return "";
}

void renderTimeLedger(const game::CampaignViewSnapshot &view) {
  ImGui::Text("turn %lld  |  t_coordinate %.1f d  |  authority dtau/dt %.4f  |  spin a* %.2f",
              static_cast<long long>(view.turn), days(view.coordinateTimeSec),
              view.authorityProperTimeRate, view.spinDimensionless);
  ImGui::TextDisabled("orders in flight: %zu   reports in flight: %zu   intel: %zu",
                      view.ordersInFlight.size(), view.reportsInFlight.size(),
                      view.intel.size());
  // The outcome vector: the singularity's disturbance and what a deep
  // prograde lane buys against it. Shown only once the mechanic is engaged.
  if (view.instability > 0.0 || view.stabilization > 0.0) {
    // Full red at the instability an uncontained campaign reaches by the deadline
    // (rise per turn times deadline turns); the label reddens as the disturbance
    // grows toward that ceiling.
    constexpr double kInstabilityFullScale = 24.0;
    const auto threat = static_cast<float>(std::min(1.0, view.instability / kInstabilityFullScale));
    ImGui::TextColored(ImVec4(0.6f + (0.4f * threat), 1.0f - (0.6f * threat), 0.4f, 1.0f),
                       "Gororoba instability %.2f   stabilization %.2f   fleet integrity %.2f",
                       view.instability, view.stabilization, view.fleetIntegrity);
  }
  if (view.status == game::CampaignStatus::Won) {
    // The victory turn is the turn the objective cleared, not the current turn,
    // which keeps flowing as in-flight reports arrive after the decision latches.
    ImGui::TextColored(ImVec4(0.4f, 1.0f, 0.5f, 1.0f), "VICTORY -- objective cleared on turn %lld",
                       static_cast<long long>(view.clearedTurn));
  } else if (view.status == game::CampaignStatus::Lost) {
    ImGui::TextColored(ImVec4(1.0f, 0.4f, 0.4f, 1.0f), "DEFEAT -- deadline t%lld passed",
                       static_cast<long long>(view.deadlineTurn));
  } else if (view.victoryEnergyUnits > 0.0) {
    const auto fraction = static_cast<float>(view.energyUnits / view.victoryEnergyUnits);
    const std::string objective = std::format("energy {:.1f} / {:.0f}  (deadline t{})",
                                              view.energyUnits, view.victoryEnergyUnits,
                                              view.deadlineTurn);
    ImGui::ProgressBar(fraction, ImVec2(-1.0f, 0.0f), objective.c_str());
  } else {
    ImGui::TextDisabled("energy banked: %.1f (no objective set)", view.energyUnits);
  }
  // The alternate victory: tame the singularity. Pursuing it sacrifices energy,
  // so the two bars are rival ends the player chooses between.
  if (view.status == game::CampaignStatus::Ongoing && view.victoryStabilizationUnits > 0.0) {
    const auto fraction = static_cast<float>(view.stabilization / view.victoryStabilizationUnits);
    const std::string objective = std::format("stabilization {:.2f} / {:.0f}",
                                              view.stabilization, view.victoryStabilizationUnits);
    ImGui::ProgressBar(fraction, ImVec2(-1.0f, 0.0f), objective.c_str());
  }
}

void renderFleetRoster(const game::CampaignViewSnapshot &view, CampaignUiState &uiState) {
  if (!ImGui::BeginTable("fleet_roster", 9,
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
  ImGui::TableSetupColumn("effect");
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
    // Reliability turns red once the fleet's telemetry corrupts, and carries a
    // marker so the player sees which fleets need verification.
    if (fleet.telemetryCorrupted) {
      ImGui::TextColored(ImVec4(1.0f, 0.4f, 0.4f, 1.0f), "%.2f !", fleet.reliability);
    } else {
      ImGui::Text("%.2f", fleet.reliability);
    }
    ImGui::TableNextColumn();
    ImGui::Text("%s", fleet.observer == game::Observer::Hovering ? "hover"
                                                                 : game::laneName(fleet.lane));
    ImGui::TableNextColumn();
    ImGui::Text("%s x%.2f", capabilityEffectText(fleet.capability), fleet.yieldMultiplier);
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
      std::string bandLabel;
      if (band.validStation) {
        bandLabel = std::format("band {}  (dtau/dt {:.3f}, delay {:.1f} d)", band.index,
                                band.properTimeRate, band.delayToAuthoritySec / K_SECONDS_PER_DAY);
      } else {
        bandLabel = std::format("band {}  (FORBIDDEN)", band.index);
      }
      if (ImGui::Selectable(bandLabel.c_str(), band.index == uiState.composerTargetBand)) {
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
  // Station keeping: an orbit is a free-fall geodesic and needs a bound orbit
  // at the band; hovering on thrust reaches below the marginally bound radius.
  int stationChoice = uiState.composerStation == game::StationKeeping::Hover ? 1 : 0;
  ImGui::TextUnformatted("station");
  ImGui::SameLine();
  ImGui::RadioButton("orbit", &stationChoice, 0);
  ImGui::SameLine();
  ImGui::RadioButton("hover", &stationChoice, 1);
  uiState.composerStation =
      stationChoice == 1 ? game::StationKeeping::Hover : game::StationKeeping::Orbit;
  if (ImGui::Button("Redeploy fleet")) {
    uiState.lastCommandAccepted =
        session.issuePlaceFleet(uiState.selectedFleet, uiState.composerTargetBand,
                                uiState.composerLane, uiState.composerStation);
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
    const ImVec4 color = report.corrupted ? ImVec4(1.0f, 0.6f, 0.4f, 1.0f)
                                          : ImVec4(1.0f, 1.0f, 1.0f, 1.0f);
    ImGui::TextColored(
        color, "t%lld: fleet %u completed task %u at t%lld (+%.1f energy%s, %lld turns stale)",
        static_cast<long long>(report.receivedTurn), report.fleet, report.task,
        static_cast<long long>(report.completedTurn), report.yieldUnits,
        report.corrupted ? " CORRUPTED" : "",
        static_cast<long long>(report.receivedTurn - report.completedTurn));
  }
  ImGui::End();
}

void renderBackdropPicker(const CampaignBackdrop *backdrops, int backdropCount,
                          CampaignUiState &uiState) {
  if (backdrops == nullptr || backdropCount <= 0) {
    return;
  }
  uiState.selectedBackdrop = std::clamp(uiState.selectedBackdrop, 0, backdropCount - 1);
  if (ImGui::BeginCombo("map backdrop", backdrops[uiState.selectedBackdrop].name)) {
    for (int index = 0; index < backdropCount; ++index) {
      if (ImGui::Selectable(backdrops[index].name, index == uiState.selectedBackdrop)) {
        uiState.selectedBackdrop = index;
      }
    }
    ImGui::EndCombo();
  }

  // Thumbnail swatches: a clickable preview per backdrop, the selected one framed.
  // A backdrop with no texture (the procedural starfield) shows a dark swatch. The
  // preview reuses the same textures the map draws, so this costs no extra load.
  const ImVec2 thumb(48.0f, 27.0f); // 16:9-ish preview
  for (int index = 0; index < backdropCount; ++index) {
    if (index > 0) {
      ImGui::SameLine();
    }
    ImGui::PushID(index);
    const bool selected = index == uiState.selectedBackdrop;
    if (selected) {
      ImGui::PushStyleColor(ImGuiCol_Button, ImVec4(0.35f, 0.75f, 1.0f, 1.0f));
      ImGui::PushStyleColor(ImGuiCol_ButtonHovered, ImVec4(0.45f, 0.85f, 1.0f, 1.0f));
    }
    bool clicked = false;
    if (backdrops[index].textureId != 0) {
      clicked = ImGui::ImageButton("thumb", static_cast<ImTextureID>(backdrops[index].textureId),
                                   thumb);
    } else {
      clicked = ImGui::Button("stars", ImVec2(thumb.x + 8.0f, thumb.y + 8.0f));
    }
    if (selected) {
      ImGui::PopStyleColor(2);
    }
    if (clicked) {
      uiState.selectedBackdrop = index;
    }
    if (ImGui::IsItemHovered()) {
      ImGui::SetTooltip("%s", backdrops[index].name);
    }
    ImGui::PopID();
  }
}

} // namespace

void initCampaignUiFromEnv(CampaignUiState &uiState) {
  if (const char *campaignEnv = std::getenv("BLACKHOLE_CAMPAIGN")) {
    uiState.windowsOpen = (std::strcmp(campaignEnv, "0") != 0);
  }
}

void renderCampaignWindows(game::CampaignSession &session, CampaignUiState &uiState,
                           const CampaignBackdrop *backdrops, int backdropCount) {
  ImGui::SetNextWindowPos(ImVec2(420.0f, 40.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(540.0f, 420.0f), ImGuiCond_FirstUseEver);
  if (ImGui::Begin("Campaign", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Singularity: GOROROBA", &uiState.windowsOpen);
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
      renderBackdropPicker(backdrops, backdropCount, uiState);
      ImGui::SeparatorText("Fleet roster");
      renderFleetRoster(view, uiState);
      renderOrderComposer(session, view, uiState);
    } else {
      ImGui::TextDisabled("enable to command fleets around Gororoba, the singularity");
    }
  }
  ImGui::End();

  if (uiState.windowsOpen) {
    // A fresh snapshot after any button above mutated the campaign this frame.
    const game::CampaignViewSnapshot view = session.state().renderSnapshot();
    unsigned int backdropTextureId = 0;
    const char *backdropCredit = nullptr;
    if (backdrops != nullptr && backdropCount > 0) {
      const CampaignBackdrop &chosen =
          backdrops[std::clamp(uiState.selectedBackdrop, 0, backdropCount - 1)];
      backdropTextureId = chosen.textureId;
      backdropCredit = chosen.credit;
    }
    renderStrategicMap(view, uiState, backdropTextureId, backdropCredit);
    renderIntelWindow(view);
  }
}

} // namespace ui
