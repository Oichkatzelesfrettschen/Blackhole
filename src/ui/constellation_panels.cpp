#include "ui/constellation_panels.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <ios>
#include <iterator>
#include <memory>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

#include <imgui.h>

#include "game/campaign_view.h"
#include "game/constellation.h"
#include "game/constellation_types.h"
#include "game/constellation_view.h"
#include "game/desktop_game.h"
#include "game/first_play_briefing.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "render/render_state.h"
#include "render/renderer_contract.h"

namespace ui {
namespace {

// Turns between automatic checkpoint saves.
constexpr std::int64_t K_CHECKPOINT_TURNS = 25;
// Longest single "Advance to next report" run, so one click never skips a
// quiet stretch longer than this without returning control to the player.
constexpr std::int64_t K_MAX_TURNS_PER_ADVANCE = 250;

const char *rejectionName(game::OrderRejection reason) {
  switch (reason) {
  case game::OrderRejection::None:
    return "Ready";
  case game::OrderRejection::InvalidSession:
    return "Scenario unavailable";
  case game::OrderRejection::OutcomeKnown:
    return "Campaign decided";
  case game::OrderRejection::UnknownFleet:
    return "Fleet unavailable";
  case game::OrderRejection::FleetInTransit:
    return "Fleet travelling";
  case game::OrderRejection::InvalidTarget:
    return "Target band unavailable";
  case game::OrderRejection::InvalidPlacement:
    return "Orbit unavailable at target";
  case game::OrderRejection::NoLink:
    return "No route between systems";
  case game::OrderRejection::InsufficientFuel:
    return "Fuel insufficient";
  case game::OrderRejection::DuplicateOrder:
    return "Fleet already assigned there";
  case game::OrderRejection::NoSignalPath:
    return "Command signal cannot arrive";
  }
  return "Order unavailable";
}

const char *controllerName(game::FactionId controller, game::FactionId player) {
  if (controller == game::K_INVALID_FACTION_ID) {
    return "unconfirmed";
  }
  return controller == player ? "your control" : "rival control";
}

const char *outcomeName(game::CampaignStatus status) {
  if (status == game::CampaignStatus::Ongoing) {
    return "Outcome pending at your authority";
  }
  return status == game::CampaignStatus::Won ? "Victory confirmed" : "Defeat confirmed";
}

const char *eventName(game::GameEventKind kind) {
  switch (kind) {
  case game::GameEventKind::OrderIssued:
    return "Order sent";
  case game::GameEventKind::FleetReport:
    return "Fleet report received";
  case game::GameEventKind::ArrivalReport:
    return "Arrival report received";
  case game::GameEventKind::ControlObservation:
    return "Control observed";
  case game::GameEventKind::ContestedOrUnknown:
    return "Control unconfirmed";
  case game::GameEventKind::EnergyReport:
    return "Energy credited";
  case game::GameEventKind::StabilizationReport:
    return "Stabilization reported";
  case game::GameEventKind::ControlReport:
    return "Control score reported";
  case game::GameEventKind::OutcomeNotice:
    return "Outcome notice received";
  }
  return "Report received";
}

std::filesystem::path savePath() {
  return "propertime.save";
}

bool writeSave(const game::DesktopGame &session) {
  const std::filesystem::path temporary = "propertime.save.tmp";
  const std::vector<std::uint8_t> bytes = session.save();
  std::ofstream output(temporary, std::ios::binary | std::ios::trunc);
  output.write(reinterpret_cast<const char *>(bytes.data()),
               static_cast<std::streamsize>(bytes.size()));
  output.close();
  if (!output) {
    return false;
  }
  std::error_code error;
  std::filesystem::rename(temporary, savePath(), error);
  return !error;
}

void drawStrategicMap(ConstellationUiState &uiState,
                      const game::ConstellationViewSnapshot &snapshot) {
  if (ImGui::Begin("System/Strategic Map")) {
    ImGui::Text("Turn %lld", static_cast<long long>(snapshot.turn));
    ImGui::TextWrapped("The viewport renders the selected system; the camera does not advance "
                       "campaign time.");
    for (const game::SystemStanding &system : snapshot.systems) {
      const std::string label = "System " + std::to_string(system.id);
      if (ImGui::Selectable(label.c_str(), uiState.selectedSystem == system.id)) {
        static_cast<void>(selectConstellationSystem(uiState, snapshot, system.id));
      }
      for (std::size_t band = 0; band < system.bandController.size(); ++band) {
        const game::FactionId controller = system.bandController.at(band);
        ImGui::BulletText("Band %zu: %s", band, controllerName(controller, snapshot.playerFaction));
      }
    }
    for (const game::InterSystemLink &link : snapshot.links) {
      ImGui::Text("Route %u - %u", link.a, link.b);
    }
    for (const game::ConstellationFleetView &fleet : snapshot.fleets) {
      if (fleet.inTransit) {
        ImGui::Text("Fleet %u travelling: %u to %u, reported arrival %lld", fleet.id, fleet.system,
                    fleet.transitDestSystem, static_cast<long long>(fleet.transitArrivalTurn));
      } else {
        ImGui::Text("Fleet %u: system %u band %d", fleet.id, fleet.system, fleet.bandIndex);
      }
    }
    ImGui::Text("Selected target: System %u", uiState.selectedSystem);
  }
  ImGui::End();
}

void drawOperations(ConstellationUiState &uiState,
                    const game::ConstellationViewSnapshot &snapshot) {
  if (ImGui::Begin("Operations")) {
    ImGui::TextUnformatted("Orders travel at light speed. Fleets move after the signal arrives.");
    for (const game::ConstellationFleetView &fleet : snapshot.fleets) {
      const std::string label = "Fleet " + std::to_string(fleet.id) + " - system " +
                                std::to_string(fleet.system) + " band " +
                                std::to_string(fleet.bandIndex);
      if (ImGui::Selectable(label.c_str(), uiState.selectedFleet == fleet.id)) {
        uiState.selectedFleet = fleet.id;
        uiState.targetSystem = static_cast<int>(fleet.system);
        uiState.targetBand = fleet.bandIndex;
      }
      ImGui::SameLine();
      ImGui::TextDisabled("report from turn %lld", static_cast<long long>(fleet.reportedTurn));
    }
    ImGui::SeparatorText("Order route");
    ImGui::InputInt("Target system", &uiState.targetSystem);
    ImGui::InputInt("Target band", &uiState.targetBand);
    bool retrograde = uiState.lane == game::OrbitLane::Retrograde;
    if (ImGui::Checkbox("Retrograde orbit", &retrograde)) {
      uiState.lane = retrograde ? game::OrbitLane::Retrograde : game::OrbitLane::Prograde;
    }
    bool hover = uiState.station == game::StationKeeping::Hover;
    if (ImGui::Checkbox("Hold position with thrust", &hover)) {
      uiState.station = hover ? game::StationKeeping::Hover : game::StationKeeping::Orbit;
    }
    const game::ConstellationCommand command{
        .fleet = uiState.selectedFleet,
        .targetSystem = uiState.targetSystem < 0
                            ? game::K_INVALID_SYSTEM_ID
                            : static_cast<game::SystemId>(uiState.targetSystem),
        .targetBand = uiState.targetBand,
        .lane = uiState.lane,
        .station = uiState.station};
    const game::OrderPreview preview = uiState.session->preview(command);
    ImGui::Text("System %u, band %d: %s", preview.targetSystem, preview.targetBand,
                rejectionName(preview.rejection));
    if (preview.rejection == game::OrderRejection::None) {
      ImGui::Text("Fuel cost %.1f; reported fuel remaining %.1f", preview.fuelCost,
                  preview.remainingFuel);
      ImGui::Text("Signal %lld turns; effect turn %lld",
                  static_cast<long long>(preview.signalTurns),
                  static_cast<long long>(preview.effectTurn));
      ImGui::Text("Travel %lld turns; expected arrival turn %lld",
                  static_cast<long long>(preview.travelTurns),
                  static_cast<long long>(preview.arrivalTurn));
      ImGui::TextUnformatted(preview.riskKnown ? "Known controller at target"
                                               : "Target risks unavailable until reports arrive");
    }
    ImGui::BeginDisabled(preview.rejection != game::OrderRejection::None);
    if (ImGui::Button("Send order")) {
      uiState.lastRejection = uiState.session->issue(command);
    }
    ImGui::EndDisabled();
    if (uiState.lastRejection != game::OrderRejection::None) {
      ImGui::Text("Order refused: %s", rejectionName(uiState.lastRejection));
    }
    const std::int64_t turnBefore = uiState.session->state().turn();
    if (ImGui::Button("Advance one turn")) {
      uiState.session->advanceTurn();
    }
    ImGui::SameLine();
    if (ImGui::Button("Advance to next report")) {
      uiState.advancedTurns = uiState.session->advanceToNextNotice(K_MAX_TURNS_PER_ADVANCE);
    }
    if (uiState.advancedTurns > 0) {
      ImGui::TextDisabled("Last advance: %lld turns",
                          static_cast<long long>(uiState.advancedTurns));
    }
    // A checkpoint lands whenever play crosses a K_CHECKPOINT_TURNS boundary,
    // whether by one step or by a batched advance.
    if (uiState.session->state().turn() / K_CHECKPOINT_TURNS != turnBefore / K_CHECKPOINT_TURNS) {
      uiState.saveMessage = writeSave(*uiState.session) ? "Checkpoint saved" : "Checkpoint failed";
    }
  }
  ImGui::End();
}

void drawIntelligence(const game::ConstellationViewSnapshot &snapshot) {
  if (ImGui::Begin("Intelligence")) {
    ImGui::TextUnformatted("Control marks show reports received by your authority.");
    ImGui::TextUnformatted("Unconfirmed bands may be empty, contested, or beyond your reports.");
    for (const game::SystemStanding &system : snapshot.systems) {
      for (std::size_t band = 0; band < system.bandController.size(); ++band) {
        const std::int64_t sourceTurn = system.observationSourceTurn.at(band);
        if (sourceTurn >= 0) {
          ImGui::Text("System %u band %zu: band observation from turn %lld; age %lld; arrived %lld",
                      system.id, band, static_cast<long long>(sourceTurn),
                      static_cast<long long>(snapshot.turn - sourceTurn),
                      static_cast<long long>(system.observationArrivalTurn.at(band)));
        }
      }
    }
    for (const game::ConstellationFleetView &fleet : snapshot.fleets) {
      ImGui::Text("Fleet %u: system %u, report age %lld turns", fleet.id, fleet.system,
                  static_cast<long long>(snapshot.turn - fleet.reportedTurn));
      if (fleet.inTransit) {
        ImGui::Text("Travel report: destination %u, arrival turn %lld", fleet.transitDestSystem,
                    static_cast<long long>(fleet.transitArrivalTurn));
      }
    }
    ImGui::TextUnformatted("Rival orders and fleet positions remain unavailable.");
  }
  ImGui::End();
}

void drawObjectives(ConstellationUiState &uiState,
                    const game::ConstellationViewSnapshot &snapshot) {
  if (ImGui::Begin("Objectives")) {
    ImGui::Checkbox("Hide briefing", &uiState.hideBriefing);
    ImGui::Text("Energy %.1f / %.1f", snapshot.player.energyUnits, snapshot.victoryEnergyUnits);
    ImGui::Text("Stabilization %.1f / %.1f", snapshot.player.stabilizationUnits,
                snapshot.victoryStabilizationUnits);
    ImGui::Text("Control %.1f / %.1f", snapshot.player.controlScore, snapshot.victoryControlScore);
    ImGui::Text("Deadline: turn %lld", static_cast<long long>(snapshot.deadlineTurn));
    std::uint32_t observedRivalBands = 0;
    for (const game::SystemStanding &system : snapshot.systems) {
      observedRivalBands += static_cast<std::uint32_t>(
          std::ranges::count_if(system.bandController, [&](game::FactionId controller) {
            return controller != game::K_INVALID_FACTION_ID && controller != snapshot.playerFaction;
          }));
    }
    ImGui::Text("Rival control observed: %u bands", observedRivalBands);
    ImGui::TextUnformatted(outcomeName(snapshot.overallStatus));
    ImGui::TextUnformatted("Rival totals arrive through delayed observations.");
  }
  ImGui::End();
}

void drawBriefing(ConstellationUiState &uiState) {
  if (uiState.hideBriefing) {
    return;
  }
  const game::Briefing briefing = game::evaluateBriefing(*uiState.session);
  if (ImGui::Begin("Briefing")) {
    for (std::size_t index = 0; index < briefing.steps.size(); ++index) {
      const game::BriefingStep &step = briefing.steps.at(index);
      if (step.complete) {
        ImGui::Text("[x] %.*s", static_cast<int>(step.title.size()), step.title.data());
      } else if (index == briefing.currentIndex) {
        ImGui::SeparatorText(step.title.data());
        ImGui::TextWrapped("%s", step.body.c_str());
      } else {
        ImGui::TextDisabled("[ ] %.*s", static_cast<int>(step.title.size()), step.title.data());
      }
    }
    if (briefing.currentIndex == briefing.steps.size()) {
      ImGui::TextUnformatted("Briefing complete.");
    }
  }
  ImGui::End();
}

void drawEventLog(ConstellationUiState &uiState, const game::ConstellationViewSnapshot &snapshot,
                  const std::vector<game::GameEvent> &events) {
  if (ImGui::Begin("Event Log")) {
    for (const game::PlayerOrderView &order : snapshot.orders) {
      const char *status = "Awaiting fleet report";
      if (order.status == game::PlayerOrderStatus::ConfirmedByFleetReport) {
        status = "Delivery confirmed by fleet report";
      } else if (order.status == game::PlayerOrderStatus::UndeliveredNotice) {
        status = "Non-delivery notice received";
      }
      ImGui::Text("Fleet %u order, effect turn %lld: %s", order.fleet,
                  static_cast<long long>(order.effectTurn), status);
    }
    const std::size_t first = events.size() > 100 ? events.size() - 100 : 0;
    for (std::size_t index = first; index < events.size(); ++index) {
      const game::GameEvent &event = events.at(index);
      ImGui::Text("Turn %lld: %s", static_cast<long long>(event.receivedTurn),
                  eventName(event.kind));
      if (event.fleet != game::K_INVALID_FLEET_ID) {
        ImGui::SameLine();
        ImGui::Text("fleet %u", event.fleet);
      }
      if (event.system != game::K_INVALID_SYSTEM_ID) {
        ImGui::SameLine();
        ImGui::Text("system %u band %d", event.system, event.band);
      }
    }
    if (ImGui::Button("Save campaign")) {
      uiState.saveMessage = writeSave(*uiState.session) ? "Campaign saved" : "Save failed";
    }
    ImGui::SameLine();
    if (ImGui::Button("Load campaign")) {
      std::ifstream input(savePath(), std::ios::binary);
      if (input) {
        const std::vector<std::uint8_t> bytes{std::istreambuf_iterator<char>(input),
                                              std::istreambuf_iterator<char>()};
        game::SaveError error = game::SaveError::None;
        std::unique_ptr<game::DesktopGame> loaded = game::DesktopGame::load(bytes, error);
        if (loaded) {
          uiState.session = std::move(loaded);
          uiState.saveMessage = "Campaign verified and loaded";
        } else {
          uiState.saveMessage =
              "Save verification failed (code " + std::to_string(static_cast<int>(error)) + ")";
        }
      } else {
        uiState.saveMessage = "Save unavailable";
      }
    }
    ImGui::TextUnformatted(uiState.saveMessage.c_str());
  }
  ImGui::End();
}

} // namespace

void renderConstellationPanels(ConstellationUiState &uiState, blackhole::RenderState &renderState) {
  const game::ConstellationViewSnapshot snapshot = uiState.session->snapshot();
  const std::vector<game::GameEvent> events = uiState.session->events();
  drawStrategicMap(uiState, snapshot);
  drawOperations(uiState, snapshot);
  drawIntelligence(snapshot);
  drawObjectives(uiState, snapshot);
  drawBriefing(uiState);
  // A fresh layout leaves each dock node on whichever tab it docked last;
  // focusing opens the map and the order composer, Operations last so it holds
  // keyboard focus.
  if (renderState.overlays.sceneWindowFocusPending) {
    ImGui::SetWindowFocus("System/Strategic Map");
    ImGui::SetWindowFocus("Operations");
    renderState.overlays.sceneWindowFocusPending = false;
  }
  drawEventLog(uiState, snapshot, events);
  if (uiState.selectedSystem < snapshot.systems.size()) {
    renderState.physicsCore.kerrSpin =
        static_cast<float>(snapshot.systems.at(uiState.selectedSystem).spinDimensionless);
    renderState.physicsCore.blackHoleMass = uiState.selectedSystem == 0 ? 6.5f : 4.1f;
    renderState.dispatch.contract.geodesic = blackhole::GeodesicModel::KerrReference;
  }
}

} // namespace ui
