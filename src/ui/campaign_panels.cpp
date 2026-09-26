/**
 * @file campaign_panels.cpp
 * @brief Singularity: GOROROBA campaign windows implementation.
 */

#include "ui/campaign_panels.h"

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <format>
#include <memory>
#include <numeric>
#include <ranges>
#include <string>
#include <vector>

#include <imgui.h>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/campaign_view.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/fleet.h"
#include "game/inbox.h"
#include "game/observer.h"
#include "game/realtime_driver.h"
#include "game/station_node.h"
#include "platform/resource_paths.h"
#include "ui/strategic_map.h"

namespace ui {

namespace {

constexpr double K_SECONDS_PER_DAY = 86400.0;

// What an orbit on this band and lane would be: stable free fall, an unstable
// circular geodesic held by station-keeping thrust (between the marginally
// bound radius and the ISCO), or no bound orbit at all.
const char *orbitLabel(const game::BandView &band, game::OrbitLane lane) {
  const bool retrograde = lane == game::OrbitLane::Retrograde;
  const bool admits = retrograde ? band.admitsRetrogradeOrbit : band.admitsOrbit;
  const bool stable = retrograde ? band.stableRetrogradeOrbit : band.stableOrbit;
  if (!admits) {
    return "orbit: none bound here (hover only)";
  }
  return stable ? "orbit: stable" : "orbit: unstable (station-keeping)";
}

double days(double seconds) { return seconds / K_SECONDS_PER_DAY; }

/** @brief A span of seconds in the largest unit that keeps it readable. */
std::string formatSpan(double seconds) {
  constexpr double kMinute = 60.0;
  constexpr double kHour = 3600.0;
  constexpr double kYear = 365.25 * K_SECONDS_PER_DAY;
  const double magnitude = std::fabs(seconds);
  if (magnitude < kMinute) {
    return std::format("{:.2f} s", seconds);
  }
  if (magnitude < kHour) {
    return std::format("{:.2f} min", seconds / kMinute);
  }
  if (magnitude < K_SECONDS_PER_DAY) {
    return std::format("{:.2f} h", seconds / kHour);
  }
  if (magnitude < kYear) {
    return std::format("{:.2f} d", seconds / K_SECONDS_PER_DAY);
  }
  return std::format("{:.2f} y", seconds / kYear);
}

const char *nodeName(game::NodeId node) {
  if (node == game::K_NO_NODE) {
    return "fleets"; // replies from fleets, which are not stations
  }
  return node == game::K_AUTHORITY_NODE ? "host" : "colony";
}

/** @brief Advances one turn and feeds both stations' inboxes; true when an
 *         arrival this turn at the focused station is in a pause category. */
bool stepTurn(game::CampaignSession &session, CampaignUiState &uiState) {
  session.state().advanceTurn();
  const bool colonyPause = uiState.inbox.sync(session.state().arrivals());
  const bool hostPause = uiState.hostInbox.sync(session.state().arrivals());
  return uiState.focusNode == game::K_AUTHORITY_NODE ? hostPause : colonyPause;
}

const game::NodeView *findNode(const game::CampaignViewSnapshot &view, game::NodeId id) {
  const auto found = std::ranges::find(view.nodes, id, &game::NodeView::id);
  return found == view.nodes.end() ? nullptr : &*found;
}

/** @brief True when the player stands at a colony: the host's present state
 *         is then out of reach, and only what the host last sent is shown. */
bool atColony(const game::CampaignViewSnapshot &view, const CampaignUiState &uiState) {
  const game::NodeView *focus = findNode(view, uiState.focusNode);
  return focus != nullptr && focus->isColony;
}

/** @brief Wrapped text in the disabled color: long readouts fold to the
 *         window width instead of running off its edge. */
void textDisabledWrapped(const std::string &text) {
  ImGui::PushStyleColor(ImGuiCol_Text, ImGui::GetStyleColorVec4(ImGuiCol_TextDisabled));
  ImGui::TextWrapped("%s", text.c_str());
  ImGui::PopStyleColor();
}

/** @brief A remote station as its latest arrival stamped it: clock, what it
 *         reports (the host's bank, a colony's tech), emission turn and age. */
std::string remoteAsLastHeard(const game::CampaignViewSnapshot &view, const game::NodeView &node,
                              double viewerRate) {
  if (!node.heard) {
    return std::format("{}: nothing received yet -- its present is unknown here",
                       nodeName(node.id));
  }
  const double ageSec = static_cast<double>(view.turn - node.asOfTurn) * view.secondsPerTurn;
  const std::string reported =
      node.isColony ? std::format("tech tier {} ({} points)", node.techTier, node.techPoints)
                    : std::format("energy banked {:.1f}", view.energyUnits);
  return std::format("{} as last heard: {}, its clock {} (sent t{}; signal age {} outside / {} "
                     "local)",
                     nodeName(node.id), reported,
                     formatSpan(node.properTimeSec), node.asOfTurn, formatSpan(ageSec),
                     formatSpan(ageSec * viewerRate));
}

std::string arrivalText(const game::CampaignViewSnapshot &view, const game::ArrivalRecord &arrival) {
  if (arrival.sender == game::K_NO_NODE) {
    return std::format("fleet {}: redeployment order fizzled (not enough fuel when it arrived)",
                       arrival.fleet);
  }
  if (arrival.kind == game::EmitKind::TechPacket) {
    return std::format("tech packet #{} (+{} points)", arrival.payloadIndex + 1,
                       arrival.techPoints);
  }
  const auto text = std::ranges::find(view.eventTexts, arrival.payloadIndex,
                                      &game::EventTextView::id);
  if (text == view.eventTexts.end()) {
    return "notice";
  }
  return text->text.empty() ? text->name : text->text;
}

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

void renderTimeLedger(const game::CampaignViewSnapshot &view, const CampaignUiState &uiState) {
  // Two short lines rather than one wrapped one, so no number splits.
  ImGui::Text("turn %lld  |  t_coordinate %.1f d", static_cast<long long>(view.turn),
              days(view.coordinateTimeSec));
  ImGui::Text("authority dtau/dt %.4f  |  spin a* %.2f", view.authorityProperTimeRate,
              view.spinDimensionless);
  if (atColony(view, uiState)) {
    // The host's ledger -- its intel, its bank, its objective -- is host-local
    // truth; at the colony it exists only as the host's last transmission,
    // which the clock readout below shows.
    return;
  }
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
    if (fleet.positionKnown) {
      ImGui::Text("%d", fleet.bandIndex);
    } else {
      ImGui::TextDisabled("?");
    }
    if (!fleet.telemetryKnown) {
      // The fleet reports to the host: nothing of its state reaches here.
      for (int column = 0; column < 5; ++column) {
        ImGui::TableNextColumn();
        ImGui::TextDisabled("--");
      }
    } else {
      ImGui::TableNextColumn();
      ImGui::Text("%.4g", fleet.properTimeRate);
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
    }
    ImGui::TableNextColumn();
    if (!fleet.positionKnown) {
      ImGui::TextDisabled("?");
    } else if (fleet.observer == game::Observer::Hovering) {
      ImGui::TextUnformatted("hover");
    } else {
      ImGui::Text("%s%s", game::laneName(fleet.lane), fleet.unstableOrbit ? " (unstable)" : "");
    }
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
  // Orders leave from where the player stands; the delay runs from its radius.
  // Standing at the colony, only the colony can send.
  const game::NodeView *focus = findNode(view, uiState.focusNode);
  uiState.commandOrigin = focus != nullptr ? focus->id : game::K_AUTHORITY_NODE;
  if (view.nodes.size() > 1) {
    ImGui::SameLine();
    ImGui::TextDisabled("(orders leave from the %s)", nodeName(uiState.commandOrigin));
  }

  char bandPreview[64];
  static_cast<void>(std::snprintf(bandPreview, sizeof(bandPreview), "band %d", uiState.composerTargetBand));
  if (ImGui::BeginCombo("target band", bandPreview)) {
    for (const game::BandView &band : view.bands) {
      std::string bandLabel;
      if (band.validStation) {
        // The clock of the lane and station keeping selected below; 0 marks a
        // band where that orbit is not bound.
        bandLabel = std::format(
            "band {}  (dtau/dt {:.4g}, delay {:.1f} d)", band.index,
            game::bandRateFor(band, uiState.composerLane, uiState.composerStation),
            band.delayToAuthoritySec / K_SECONDS_PER_DAY);
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
  for (const game::BandView &band : view.bands) {
    if (band.index == uiState.composerTargetBand && band.validStation) {
      ImGui::SameLine();
      if (uiState.composerStation == game::StationKeeping::Hover) {
        ImGui::Text("hover: dtau/dt %.4f", band.hoverProperTimeRate);
      } else {
        ImGui::Text("%s, dtau/dt %.4f", orbitLabel(band, uiState.composerLane),
                    game::bandRateFor(band, uiState.composerLane, uiState.composerStation));
      }
    }
  }
  if (ImGui::Button("Redeploy fleet")) {
    uiState.lastCommandAccepted = session.issuePlaceFleet(
        uiState.selectedFleet, uiState.composerTargetBand, uiState.composerLane,
        uiState.composerStation, uiState.commandOrigin);
    uiState.lastCommandValid = true;
  }

  ImGui::SliderFloat("task cost (proper hours)", &uiState.composerCostHours, 1.0f, 500.0f,
                     "%.0f h", ImGuiSliderFlags_Logarithmic);
  ImGui::SameLine();
  if (ImGui::Button("Assign task")) {
    uiState.lastCommandAccepted =
        session.issueAssignTask(uiState.selectedFleet,
                                static_cast<double>(uiState.composerCostHours),
                                uiState.commandOrigin);
    uiState.lastCommandValid = true;
  }

  if (uiState.lastCommandValid && !uiState.lastCommandAccepted) {
    // One message for every refusal: the reason can depend on state the
    // sender has no way to know yet.
    ImGui::TextColored(ImVec4(1.0f, 0.4f, 0.4f, 1.0f), "order refused");
  }
}

void renderIntelWindow(const game::CampaignViewSnapshot &view, const CampaignUiState &uiState) {
  ImGui::SetNextWindowPos(ImVec2(980.0f, 40.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(420.0f, 300.0f), ImGuiCond_FirstUseEver);
  if (!ImGui::Begin("Campaign Intel", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::End();
    return;
  }
  if (atColony(view, uiState)) {
    ImGui::TextDisabled("the intel log is kept at the host; the colony sees only its inbox");
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

void startColonyStory(CampaignUiState &uiState, int colonyBand) {
  const game::EventLoadResult loaded =
      game::loadEventSetFile(platform::resourcePath("assets/events/host_goes_dark.json"));
  if (!loaded.ok()) {
    uiState.storyError = loaded.error;
    return;
  }
  uiState.storyError.clear();
  uiState.storySession = std::make_unique<game::CampaignSession>(1, loaded.story, colonyBand);
  // Fresh inboxes for the new session, keeping the player's pause choices.
  game::Inbox colonyInbox(game::K_FIRST_COLONY_NODE);
  game::Inbox hostInbox(game::K_AUTHORITY_NODE);
  for (int index = 0; index < game::K_EVENT_CATEGORY_COUNT; ++index) {
    const auto category = static_cast<game::EventCategory>(index);
    colonyInbox.setPauseOn(category, uiState.inbox.pausesOn(category));
    hostInbox.setPauseOn(category, uiState.inbox.pausesOn(category));
  }
  uiState.inbox = colonyInbox;
  uiState.hostInbox = hostInbox;
  uiState.focusNode = game::K_FIRST_COLONY_NODE;
  uiState.commandOrigin = game::K_FIRST_COLONY_NODE;
  uiState.realtime = false;
  // A fresh driver: backlog owed to the old session is not owed to this one.
  game::RealtimeDriverConfig config;
  config.secondsPerTurn = uiState.storySession->state().config().secondsPerTurn;
  config.localSecondsPerWallSecond = static_cast<double>(uiState.localSecondsPerWallSecond);
  uiState.driver = game::RealtimeDriver(config);
}

/** @brief Real-time controls: start the story, run the clock at the focused
 *         station's rate, pause categories, and the lagging indicator. */
void renderRealtimeControls(const game::CampaignViewSnapshot &view, CampaignUiState &uiState) {
  ImGui::SeparatorText("Real time");
  if (!uiState.storySession) {
    // The host-goes-dark story from either orbit. Deep, the colony hears
    // decades of the host's stream per local day but ships little before the
    // host falls silent; shallow, it ships its whole charter home but its
    // mission ends while the stream has barely begun.
    ImGui::TextUnformatted("host story -- choose where the colony lives:");
    int chosenBand = -1;
    if (ImGui::Button("Miller's planet (deep: 1 local hour = 7 outside years)")) {
      chosenBand = game::K_MILLER_BAND;
    }
    ImGui::SameLine();
    if (ImGui::Button("100M survey orbit (shallow)")) {
      chosenBand = game::K_SURVEY_BAND;
    }
    if (chosenBand >= 0) {
      startColonyStory(uiState, chosenBand);
      return; // this frame's view is the old session's
    }
  }
  if (!uiState.storyError.empty()) {
    ImGui::TextColored(ImVec4(1.0f, 0.4f, 0.4f, 1.0f), "story: %s", uiState.storyError.c_str());
  }
  const game::NodeView *focus = findNode(view, uiState.focusNode);
  if (focus == nullptr) {
    uiState.focusNode = game::K_AUTHORITY_NODE;
    focus = findNode(view, uiState.focusNode);
  }
  if (view.nodes.size() > 1) {
    int focusChoice = static_cast<int>(uiState.focusNode);
    for (const game::NodeView &node : view.nodes) {
      ImGui::SameLine();
      ImGui::RadioButton(std::format("{} focus##focus{}", nodeName(node.id), node.id).c_str(),
                         &focusChoice, static_cast<int>(node.id));
    }
    uiState.focusNode = static_cast<game::NodeId>(focusChoice);
    focus = findNode(view, uiState.focusNode);
  }
  ImGui::Checkbox("run in real time", &uiState.realtime);
  ImGui::SameLine();
  bool paused = uiState.driver.paused();
  if (ImGui::Checkbox("paused", &paused)) {
    uiState.driver.setPaused(paused);
  }
  if (ImGui::SliderFloat("local s per wall s", &uiState.localSecondsPerWallSecond, 1.0f, 3600.0f,
                         "%.0f", ImGuiSliderFlags_Logarithmic)) {
    game::RealtimeDriverConfig config;
    config.secondsPerTurn = view.secondsPerTurn;
    config.localSecondsPerWallSecond = static_cast<double>(uiState.localSecondsPerWallSecond);
    const bool wasPaused = uiState.driver.paused();
    uiState.driver = game::RealtimeDriver(config);
    uiState.driver.setPaused(wasPaused);
  }
  if (focus != nullptr && focus->properTimeRate > 0.0) {
    uiState.driver.setFocusRate(focus->properTimeRate);
    ImGui::TextDisabled("outside: %.4g turns per wall second at %s focus",
                        uiState.driver.turnsPerWallSecond(), nodeName(focus->id));
  }
  if (uiState.lagging) {
    ImGui::TextColored(ImVec4(1.0f, 0.7f, 0.3f, 1.0f),
                       "LAGGING: the outside world runs slower than the focus clock asks");
  }
  ImGui::TextUnformatted("pause on:");
  for (int index = 0; index < game::K_EVENT_CATEGORY_COUNT; ++index) {
    const auto category = static_cast<game::EventCategory>(index);
    bool pauseOn = uiState.inbox.pausesOn(category);
    ImGui::SameLine();
    if (ImGui::Checkbox(game::eventCategoryName(category), &pauseOn)) {
      uiState.inbox.setPauseOn(category, pauseOn);
      uiState.hostInbox.setPauseOn(category, pauseOn);
    }
  }
}

/** @brief Local proper time at the focused station against outside
 *         coordinate time, and each remote node as last heard. */
void renderClocks(const game::CampaignViewSnapshot &view, const CampaignUiState &uiState) {
  const game::NodeView *focus = findNode(view, uiState.focusNode);
  if (focus == nullptr) {
    return;
  }
  ImGui::TextWrapped("local tau (%s) %s   |   outside t %s (turn %lld)", nodeName(focus->id),
                     formatSpan(focus->properTimeSec).c_str(),
                     formatSpan(view.coordinateTimeSec).c_str(), static_cast<long long>(view.turn));
  for (const game::NodeView &node : view.nodes) {
    if (node.id != focus->id) {
      textDisabledWrapped(remoteAsLastHeard(view, node, focus->properTimeRate));
    }
  }
}

void renderInboxWindow(const game::CampaignViewSnapshot &view, CampaignUiState &uiState) {
  ImGui::SetNextWindowPos(ImVec2(980.0f, 360.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(620.0f, 320.0f), ImGuiCond_FirstUseEver);
  // The inbox of the station the player stands at, labeled by that station.
  game::Inbox &inbox =
      uiState.focusNode == game::K_AUTHORITY_NODE ? uiState.hostInbox : uiState.inbox;
  const std::string title = std::format("{} inbox ({} unread)###CampaignInbox",
                                        nodeName(inbox.owner()), inbox.unreadCount());
  if (!ImGui::Begin(title.c_str(), &uiState.inboxOpen, ImGuiWindowFlags_NoCollapse)) {
    ImGui::End();
    return;
  }
  const std::vector<game::InboxGroup> groups = inbox.groups();
  if (groups.empty()) {
    ImGui::TextDisabled("nothing has arrived");
  }
  for (const game::InboxGroup &group : groups) {
    const std::string header = std::format("from {} ({} unread, {} total)###sender{}",
                                           nodeName(group.sender), group.unread,
                                           group.entries.size(), group.sender);
    if (!ImGui::CollapsingHeader(header.c_str(), ImGuiTreeNodeFlags_DefaultOpen)) {
      continue;
    }
    if (ImGui::SmallButton(std::format("mark all read##all{}", group.sender).c_str())) {
      inbox.markAllRead(group.sender);
    }
    for (const std::size_t index : group.entries) {
      const game::InboxEntry &entry = inbox.entries().at(index);
      const game::ArrivalRecord &arrival = entry.arrival;
      ImVec4 color(1.0f, 1.0f, 1.0f, 1.0f);
      if (entry.read) {
        color = ImVec4(0.6f, 0.6f, 0.6f, 1.0f);
      } else if (inbox.pausesOn(arrival.category)) {
        color = ImVec4(1.0f, 0.75f, 0.4f, 1.0f);
      }
      ImGui::PushStyleColor(ImGuiCol_Text, color);
      const std::string line = std::format(
          "t{} [{}] {}  (sent t{} at sender tau {})##entry{}", arrival.arrivalTurn,
          game::eventCategoryName(arrival.category), arrivalText(view, arrival), arrival.emitTurn,
          formatSpan(static_cast<double>(arrival.senderProperSecAtEmit)), index);
      if (ImGui::Selectable(line.c_str(), false)) {
        inbox.markRead(index);
      }
      ImGui::PopStyleColor();
    }
  }
  ImGui::End();
}

void renderTechWindow(const game::CampaignViewSnapshot &view, const CampaignUiState &uiState) {
  if (view.techTiers.empty()) {
    return;
  }
  ImGui::SetNextWindowPos(ImVec2(980.0f, 700.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(460.0f, 300.0f), ImGuiCond_FirstUseEver);
  if (!ImGui::Begin("Technology", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::End();
    return;
  }
  const std::int64_t points = std::accumulate(
      view.nodes.begin(), view.nodes.end(), std::int64_t{0},
      [](std::int64_t best, const game::NodeView &node) {
        return node.isColony ? std::max(best, node.techPoints) : best;
      });
  // The colony's tier is present truth only at the colony; at the host it is
  // what the colony last reported, with the report's age.
  if (atColony(view, uiState)) {
    ImGui::Text("colony tier %lld (%lld points)", static_cast<long long>(view.colonyTechTier),
                static_cast<long long>(points));
  } else {
    ImGui::Text("energy banked at host %.1f", view.energyUnits);
  }
  const game::NodeView *focus = findNode(view, uiState.focusNode);
  for (const game::NodeView &node : view.nodes) {
    if (focus != nullptr && node.id != focus->id) {
      textDisabledWrapped(remoteAsLastHeard(view, node, focus->properTimeRate));
    }
  }
  for (const game::TechLevelView &level : view.techTiers) {
    const bool unlocked = points >= level.points;
    ImGui::TextColored(unlocked ? ImVec4(0.5f, 1.0f, 0.6f, 1.0f) : ImVec4(0.6f, 0.6f, 0.6f, 1.0f),
                       "%s %s  (%lld points)", unlocked ? "[x]" : "[ ]", level.name.c_str(),
                       static_cast<long long>(level.points));
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
  // Desktop captures open the story without synthetic input: the same calls
  // the panel's buttons and controls make.
  if (const char *storyEnv = std::getenv("BLACKHOLE_CAMPAIGN_STORY")) {
    if (std::strcmp(storyEnv, "deep") == 0) {
      startColonyStory(uiState, game::K_MILLER_BAND);
    } else if (std::strcmp(storyEnv, "shallow") == 0) {
      startColonyStory(uiState, game::K_SURVEY_BAND);
    }
  }
  if (const char *focusEnv = std::getenv("BLACKHOLE_CAMPAIGN_FOCUS")) {
    uiState.focusNode =
        std::strcmp(focusEnv, "host") == 0 ? game::K_AUTHORITY_NODE : game::K_FIRST_COLONY_NODE;
  }
  bool alerted = false;
  if (const char *advanceEnv = std::getenv("BLACKHOLE_CAMPAIGN_ADVANCE");
      advanceEnv != nullptr && uiState.storySession) {
    // As the Advance buttons: turn by turn, stopping on a flagged arrival.
    const long long turns = std::strtoll(advanceEnv, nullptr, 10);
    for (long long step = 0; step < std::min(turns, 100000LL) && !alerted; ++step) {
      alerted = stepTurn(*uiState.storySession, uiState);
    }
  }
  if (const char *realtimeEnv = std::getenv("BLACKHOLE_CAMPAIGN_REALTIME")) {
    const double scale = std::strtod(realtimeEnv, nullptr);
    if (std::isfinite(scale) && scale >= 1.0 && scale <= 3600.0) {
      uiState.localSecondsPerWallSecond = static_cast<float>(scale);
      game::RealtimeDriverConfig config;
      config.secondsPerTurn = uiState.storySession
                                  ? uiState.storySession->state().config().secondsPerTurn
                                  : config.secondsPerTurn;
      config.localSecondsPerWallSecond = scale;
      uiState.driver = game::RealtimeDriver(config);
      uiState.realtime = true;
    }
  }
  if (alerted) {
    uiState.driver.setPaused(true); // the preset's batch stopped on an alert
  }
}

void renderCampaignWindows(game::CampaignSession &defaultSession, CampaignUiState &uiState,
                           const CampaignBackdrop *backdrops, int backdropCount) {
  ImGui::SetNextWindowPos(ImVec2(420.0f, 40.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(540.0f, 420.0f), ImGuiCond_FirstUseEver);
  if (ImGui::Begin("Campaign", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::Checkbox("Singularity: GOROROBA", &uiState.windowsOpen);
    if (uiState.windowsOpen) {
      // The story session, once started, is the one every window plays.
      game::CampaignSession &session =
          uiState.storySession ? *uiState.storySession : defaultSession;
      const game::CampaignViewSnapshot view = session.state().perceivedSnapshot(uiState.focusNode);
      renderTimeLedger(view, uiState);
      renderClocks(view, uiState);
      for (const int count : {1, 5, 25}) {
        if (count > 1) {
          ImGui::SameLine();
        }
        const std::string label =
            count == 1 ? std::string("Advance turn") : std::format("Advance {}", count);
        if (ImGui::Button(label.c_str())) {
          // A flagged arrival stops a batch on its own turn, as in real time.
          for (int step = 0; step < count; ++step) {
            if (stepTurn(session, uiState)) {
              // The batch consumed the alert; the real-time pump later this
              // frame must not run past it.
              uiState.driver.setPaused(true);
              uiState.inboxOpen = true;
              break;
            }
          }
        }
      }
      renderRealtimeControls(view, uiState);
      renderBackdropPicker(backdrops, backdropCount, uiState);
      // The controls above may have changed the focus (or an Advance button
      // the state): the roster and composer draw a view rebuilt for the focus
      // now selected, so no frame shows one station's knowledge at another.
      const game::CampaignViewSnapshot focusedView =
          session.state().perceivedSnapshot(uiState.focusNode);
      ImGui::SeparatorText("Fleet roster");
      renderFleetRoster(focusedView, uiState);
      renderOrderComposer(session, focusedView, uiState);
    } else {
      ImGui::TextDisabled("enable to command fleets around Gororoba, the singularity");
    }
  }
  ImGui::End();

  // The story button above may have swapped sessions this frame.
  game::CampaignSession &session =
      uiState.storySession ? *uiState.storySession : defaultSession;
  if (uiState.windowsOpen && uiState.realtime) {
    // Wall time enters here and nowhere in the campaign: the driver turns it
    // into whole turns at the focused station's rate, stopping on a flagged
    // arrival's own turn. It runs after the controls, so a focus change made
    // this frame already sets this frame's rate.
    const std::vector<game::StationNode> &nodes = session.state().nodes();
    if (uiState.focusNode < nodes.size()) {
      uiState.driver.setFocusRate(nodes.at(uiState.focusNode).clock.rate());
    }
    const game::RealtimePumpResult pumped = uiState.driver.pump(
        static_cast<double>(ImGui::GetIO().DeltaTime),
        [&session, &uiState]() { return stepTurn(session, uiState); });
    uiState.lagging = pumped.lagging;
    if (pumped.pausedByArrival) {
      uiState.inboxOpen = true;
    }
  }

  if (uiState.windowsOpen) {
    // A fresh snapshot after any button above mutated the campaign this frame.
    const game::CampaignViewSnapshot view = session.state().perceivedSnapshot(uiState.focusNode);
    unsigned int backdropTextureId = 0;
    const char *backdropCredit = nullptr;
    if (backdrops != nullptr && backdropCount > 0) {
      const CampaignBackdrop &chosen =
          backdrops[std::clamp(uiState.selectedBackdrop, 0, backdropCount - 1)];
      backdropTextureId = chosen.textureId;
      backdropCredit = chosen.credit;
    }
    renderStrategicMap(view, uiState, backdropTextureId, backdropCredit);
    renderIntelWindow(view, uiState);
    if (uiState.inboxOpen) {
      renderInboxWindow(view, uiState);
    }
    renderTechWindow(view, uiState);
  }
}

} // namespace ui
