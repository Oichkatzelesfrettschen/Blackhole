/**
 * @file inbox.cpp
 * @brief Player inbox implementation.
 */

#include "game/inbox.h"

#include <algorithm>
#include <cstddef>
#include <map>
#include <utility>
#include <vector>

#include "game/event.h"
#include "game/station_node.h"

namespace game {

namespace {

std::size_t categoryIndex(EventCategory category) { return static_cast<std::size_t>(category); }

} // namespace

Inbox::Inbox(NodeId owner) : owner_(owner) {
  for (const EventCategory category : {EventCategory::War, EventCategory::Treaty,
                                       EventCategory::Collapse, EventCategory::Silence}) {
    pauseOn_.at(categoryIndex(category)) = true;
  }
}

void Inbox::setPauseOn(EventCategory category, bool pause) {
  pauseOn_.at(categoryIndex(category)) = pause;
}

bool Inbox::pausesOn(EventCategory category) const { return pauseOn_.at(categoryIndex(category)); }

bool Inbox::sync(const std::vector<ArrivalRecord> &arrivals) {
  bool pause = false;
  for (; cursor_ < arrivals.size(); ++cursor_) {
    const ArrivalRecord &arrival = arrivals.at(cursor_);
    if (arrival.destination != owner_) {
      continue;
    }
    entries_.push_back({.arrival = arrival, .read = false});
    if (pausesOn(arrival.category)) {
      pause = true;
      lastPauseEntry_ = entries_.size() - 1;
    }
  }
  return pause;
}

std::vector<InboxGroup> Inbox::groups() const {
  std::map<NodeId, InboxGroup> bySender;
  for (std::size_t index = entries_.size(); index-- > 0;) {
    const InboxEntry &entry = entries_.at(index);
    InboxGroup &group = bySender[entry.arrival.sender];
    group.sender = entry.arrival.sender;
    group.entries.push_back(index);
    if (!entry.read) {
      ++group.unread;
    }
  }
  std::vector<InboxGroup> ordered;
  ordered.reserve(bySender.size());
  for (auto &[sender, group] : bySender) {
    static_cast<void>(sender);
    ordered.push_back(std::move(group));
  }
  return ordered;
}

std::size_t Inbox::unreadCount() const {
  return static_cast<std::size_t>(
      std::ranges::count_if(entries_, [](const InboxEntry &entry) { return !entry.read; }));
}

void Inbox::markRead(std::size_t entryIndex) {
  if (entryIndex < entries_.size()) {
    entries_.at(entryIndex).read = true;
  }
}

void Inbox::markAllRead(NodeId sender) {
  for (InboxEntry &entry : entries_) {
    if (entry.arrival.sender == sender) {
      entry.read = true;
    }
  }
}

} // namespace game
