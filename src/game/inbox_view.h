#ifndef BLACKHOLE_GAME_INBOX_VIEW_H
#define BLACKHOLE_GAME_INBOX_VIEW_H

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <format>
#include <string>
#include <vector>

#include "game/inbox.h"

namespace game {

struct InboxRow {
  std::vector<std::size_t> entries;
  std::int64_t firstTurn = 0;
  std::int64_t lastTurn = 0;
};

inline bool routineInboxCategory(EventCategory category) {
  return category == EventCategory::Info || category == EventCategory::Tech;
}

inline std::vector<InboxRow> inboxRows(const Inbox &inbox, const InboxGroup &group) {
  std::vector<InboxRow> rows;
  for (std::size_t index : group.entries) {
    const ArrivalRecord &arrival = inbox.entries().at(index).arrival;
    if (!rows.empty() && routineInboxCategory(arrival.category) &&
        routineInboxCategory(inbox.entries().at(rows.back().entries.back()).arrival.category) &&
        inbox.entries().at(rows.back().entries.back()).arrival.sender == arrival.sender) {
      rows.back().entries.push_back(index);
      rows.back().firstTurn = std::min(rows.back().firstTurn, arrival.arrivalTurn);
      rows.back().lastTurn = std::max(rows.back().lastTurn, arrival.arrivalTurn);
    } else {
      rows.push_back(
          {.entries = {index}, .firstTurn = arrival.arrivalTurn, .lastTurn = arrival.arrivalTurn});
    }
  }
  return rows;
}

inline std::string inboxDetailText(const ArrivalRecord &arrival, double secondsPerTurn,
                                   const std::string &senderName, const std::string &message) {
  const double ageSeconds =
      static_cast<double>(arrival.arrivalTurn - arrival.emitTurn) * secondsPerTurn;
  const std::string change = arrival.kind == EmitKind::TechPacket
                                 ? std::format("Tech points: +{}", arrival.techPoints)
                                 : "Tech points: none recorded";
  return std::format(
      "Sender: {} (node {})\nDestination: node {}\nCategory: {}\n"
      "Kind: {}\nMessage: {}\nPayload index: {}\nFleet: {}\n"
      "Sender energy at emission: {}\nSender tech points at emission: {}\n"
      "Emitted: turn {}\nArrived: "
      "turn {}\nSender proper time at emission: {} s\nSignal age: {} turns "
      "({} s)\n{}\nFlags: none recorded\nSchedules: none recorded",
      senderName, arrival.sender, arrival.destination, eventCategoryName(arrival.category),
      arrival.kind == EmitKind::TechPacket ? "tech packet" : "notice", message,
      arrival.payloadIndex, arrival.fleet, arrival.senderEnergyUnitsAtEmit,
      arrival.senderTechPointsAtEmit, arrival.emitTurn, arrival.arrivalTurn,
      arrival.senderProperSecAtEmit, arrival.arrivalTurn - arrival.emitTurn, ageSeconds, change);
}

} // namespace game

#endif // BLACKHOLE_GAME_INBOX_VIEW_H
