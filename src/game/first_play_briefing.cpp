#include "game/first_play_briefing.h"

#include <algorithm>
#include <cstdint>
#include <string>
#include <utility>

#include "game/constellation_view.h"
#include "game/desktop_game.h"

namespace game {
namespace {

const ConstellationFleetView *receivedPlayerReport(const DesktopGame &session,
                                                   const ConstellationViewSnapshot &snapshot) {
  if (session.orders().empty()) {
    return nullptr;
  }
  const std::int64_t firstIssueTurn = session.orders().front().issueTurn;
  for (const GameEvent &event : session.events()) {
    if (event.receivedTurn <= firstIssueTurn ||
        (event.kind != GameEventKind::FleetReport && event.kind != GameEventKind::ArrivalReport)) {
      continue;
    }
    const auto fleet = std::ranges::find(snapshot.fleets, event.fleet, &ConstellationFleetView::id);
    if (fleet != snapshot.fleets.end() && fleet->faction == snapshot.playerFaction) {
      return &*fleet;
    }
  }
  return nullptr;
}

bool receivedControlObservation(const DesktopGame &session) {
  return std::ranges::any_of(session.events(), [](const GameEvent &event) {
    return event.kind == GameEventKind::ControlObservation ||
           event.kind == GameEventKind::ContestedOrUnknown;
  });
}

} // namespace

Briefing evaluateBriefing(const DesktopGame &session) {
  const ConstellationViewSnapshot snapshot = session.snapshot();
  const bool orderIssued = !session.orders().empty();
  const bool signalArrived = orderIssued && !snapshot.orders.empty() &&
                             snapshot.turn >= snapshot.orders.front().effectTurn;
  const ConstellationFleetView *reportedFleet = receivedPlayerReport(session, snapshot);

  std::string reportBody = "A fleet report shows where the fleet was when it sent the news. "
                           "Compare its report turn with the current turn to see the age.";
  if (reportedFleet != nullptr) {
    reportBody = "A fleet report shows where the fleet was when it sent the news. "
                 "Report turn " +
                 std::to_string(reportedFleet->reportedTurn) + "; current turn " +
                 std::to_string(snapshot.turn) + "; age " +
                 std::to_string(snapshot.turn - reportedFleet->reportedTurn) + " turns.";
  }

  Briefing briefing{
      .steps = {
          BriefingStep{.title = "Send an order",
                       .body = "Orders travel at light speed. Select a fleet in Operations and "
                               "check the effect turn in the order preview before sending it.",
                       .complete = orderIssued},
          BriefingStep{.title = "Wait for the signal",
                       .body = "The fleet has not moved yet. Advance turns: the order takes "
                               "effect only when its signal arrives at the effect turn.",
                       .complete = signalArrived},
          BriefingStep{.title = "Read the report",
                       .body = std::move(reportBody),
                       .complete = reportedFleet != nullptr},
          BriefingStep{.title = "Stale intelligence",
                       .body = "Rival control news arrives after light has traveled from the "
                               "observed band. The rival also plans from old reports about you.",
                       .complete = receivedControlObservation(session)},
          BriefingStep{.title = "Choose a line",
                       .body = "Outer bands gather energy with faster clocks; deep ergoregion "
                               "bands stabilize instability with slower clocks. Holding the "
                               "rival's bands builds control, but the same fleets and time can "
                               "serve only one goal at once.",
                       .complete = session.orders().size() >= 3 || snapshot.turn > 100},
      }};
  while (briefing.currentIndex < briefing.steps.size() &&
         briefing.steps.at(briefing.currentIndex).complete) {
    ++briefing.currentIndex;
  }
  return briefing;
}

} // namespace game
