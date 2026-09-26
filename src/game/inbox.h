/**
 * @file inbox.h
 * @brief The player's inbox at one node: arrivals grouped by sender, read
 *        marks, and auto-pause on flagged categories.
 *
 * The inbox is player-side state and lives outside CampaignState: what has
 * arrived is the campaign's (CampaignState::arrivals(), in the digest); which
 * entries the player has read and which categories stop the clock are not.
 * sync() ingests only the arrivals past its cursor, so called after every
 * turn it sees each arrival on its own arrival turn, and its return value is
 * the pause request the real-time driver acts on before the next turn runs.
 */

#ifndef BLACKHOLE_GAME_INBOX_H
#define BLACKHOLE_GAME_INBOX_H

#include <array>
#include <cstddef>
#include <cstdint>
#include <optional>
#include <vector>

#include "game/event.h"
#include "game/station_node.h"

namespace game {

struct InboxEntry {
  ArrivalRecord arrival{};
  bool read = false;
};

/** @brief One sender's entries, newest first. */
struct InboxGroup {
  NodeId sender = K_NO_NODE;
  std::vector<std::size_t> entries; ///< Indices into Inbox::entries().
  std::size_t unread = 0;
};

class Inbox {
public:
  /** @brief An inbox for arrivals addressed to `owner`. War, treaty,
   *         collapse, and silence pause by default; info and tech do not. */
  explicit Inbox(NodeId owner = K_FIRST_COLONY_NODE);

  [[nodiscard]] NodeId owner() const { return owner_; }

  void setPauseOn(EventCategory category, bool pause);
  [[nodiscard]] bool pausesOn(EventCategory category) const;

  /** @brief Ingests arrivals[cursor, end) addressed to the owner; returns
   *         true when any of them is in a pause category. The arrival vector
   *         only grows, so the cursor stays valid across calls. */
  bool sync(const std::vector<ArrivalRecord> &arrivals);

  [[nodiscard]] const std::vector<InboxEntry> &entries() const { return entries_; }
  /** @brief Groups by sender, ascending sender id; each group newest first. */
  [[nodiscard]] std::vector<InboxGroup> groups() const;
  [[nodiscard]] std::size_t unreadCount() const;
  /** @brief The entry whose arrival requested the latest pause, if any. */
  [[nodiscard]] std::optional<std::size_t> lastPauseEntry() const { return lastPauseEntry_; }

  void markRead(std::size_t entryIndex);
  void markAllRead(NodeId sender);

private:
  NodeId owner_;
  std::array<bool, K_EVENT_CATEGORY_COUNT> pauseOn_{};
  std::size_t cursor_ = 0;
  std::vector<InboxEntry> entries_;
  std::optional<std::size_t> lastPauseEntry_;
};

} // namespace game

#endif // BLACKHOLE_GAME_INBOX_H
