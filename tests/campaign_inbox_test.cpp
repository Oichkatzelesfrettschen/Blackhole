/**
 * @file campaign_inbox_test.cpp
 * @brief Falsification gates for the player inbox and the received clocks:
 *        grouping by sender, read marks, pause categories, one-shot
 *        ingestion, and the remote clock as last heard.
 */

#include <gtest/gtest.h>

#include <cstddef>
#include <cstdint>
#include <vector>

#include "campaign_test_field.h"
#include "game/campaign.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/inbox.h"
#include "game/received_clock.h"
#include "game/station_node.h"

namespace {

game::ArrivalRecord arrival(game::NodeId sender, game::NodeId destination,
                            game::EventCategory category, std::int64_t turn) {
  game::ArrivalRecord record;
  record.sender = sender;
  record.destination = destination;
  record.category = category;
  record.emitTurn = turn - 3;
  record.arrivalTurn = turn;
  record.senderProperSecAtEmit = 100 * (turn - 3);
  return record;
}

} // namespace

// Falsifier: an entry filed under the wrong sender, a group not newest first,
// unread counts off after read marks, or another node's arrival ingested.
TEST(Inbox, GroupsBySenderNewestFirstWithReadMarks) {
  const game::NodeId colony = game::K_FIRST_COLONY_NODE;
  game::Inbox inbox(colony);
  const std::vector<game::ArrivalRecord> arrivals = {
      arrival(game::K_AUTHORITY_NODE, colony, game::EventCategory::Tech, 5),
      arrival(colony, colony, game::EventCategory::Info, 6),
      arrival(game::K_AUTHORITY_NODE, colony, game::EventCategory::Tech, 9),
      arrival(colony, game::K_AUTHORITY_NODE, game::EventCategory::Info, 9), // not ours
  };
  EXPECT_FALSE(inbox.sync(arrivals));
  ASSERT_EQ(inbox.entries().size(), 3U);
  const std::vector<game::InboxGroup> groups = inbox.groups();
  ASSERT_EQ(groups.size(), 2U);
  EXPECT_EQ(groups.at(0).sender, game::K_AUTHORITY_NODE);
  EXPECT_EQ(groups.at(0).entries, (std::vector<std::size_t>{2, 0}));
  EXPECT_EQ(groups.at(1).sender, colony);
  EXPECT_EQ(inbox.unreadCount(), 3U);
  inbox.markRead(2);
  EXPECT_EQ(inbox.groups().at(0).unread, 1U);
  inbox.markAllRead(game::K_AUTHORITY_NODE);
  EXPECT_EQ(inbox.unreadCount(), 1U);
}

// Falsifier: a pause requested for an unflagged category, missing for a
// flagged one, repeated for an already ingested arrival, or ignoring the
// player's category toggles.
TEST(Inbox, PausesOnFlaggedCategoriesOnceEach) {
  game::Inbox inbox(game::K_FIRST_COLONY_NODE);
  EXPECT_TRUE(inbox.pausesOn(game::EventCategory::Silence));
  EXPECT_TRUE(inbox.pausesOn(game::EventCategory::War));
  EXPECT_FALSE(inbox.pausesOn(game::EventCategory::Tech));
  std::vector<game::ArrivalRecord> arrivals = {
      arrival(game::K_AUTHORITY_NODE, 1, game::EventCategory::Tech, 4)};
  EXPECT_FALSE(inbox.sync(arrivals));
  arrivals.push_back(arrival(game::K_AUTHORITY_NODE, 1, game::EventCategory::Silence, 7));
  EXPECT_TRUE(inbox.sync(arrivals));
  EXPECT_EQ(inbox.lastPauseEntry(), std::size_t{1});
  EXPECT_FALSE(inbox.sync(arrivals)); // already ingested
  inbox.setPauseOn(game::EventCategory::Tech, true);
  inbox.setPauseOn(game::EventCategory::Treaty, false);
  arrivals.push_back(arrival(game::K_AUTHORITY_NODE, 1, game::EventCategory::Treaty, 8));
  EXPECT_FALSE(inbox.sync(arrivals));
  arrivals.push_back(arrival(game::K_AUTHORITY_NODE, 1, game::EventCategory::Tech, 9));
  EXPECT_TRUE(inbox.sync(arrivals));
}

// Falsifier: received tau reporting anything but the sender's clock at the
// latest emission, or signal age not (now - emitTurn) turns, scaled by the
// receiver's rate for the local reading. The fake host runs at rate 1 on
// one-second turns, so its clock at turn T reads T seconds.
TEST(ReceivedClock, RemoteClockIsTheLatestEmissionStamp) {
  const game::EventLoadResult loaded = game::parseEventSet(R"({"events": [
      {"id": 1, "triggers": [{"turn_at_least": 3}], "effects": [{"emit": {"kind": "notice", "to": "colony"}}]},
      {"id": 2, "triggers": [{"turn_at_least": 11}], "effects": [{"emit": {"kind": "tech_packet", "to": "colony"}}]}]})");
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config = campaign_test::fakeConfig();
  game::ColonyConfig colony;
  colony.bandIndex = 0; // radius 960: rate 0.1, 40 turns from the host
  colony.localTickSec = 1;
  config.colonies = {colony};
  config.story = loaded.story;
  game::CampaignState state(config, field);
  ASSERT_TRUE(state.valid());
  state.advanceTurns(60);
  const std::vector<game::ReceivedClock> clocks =
      game::latestReceivedClocks(state.arrivals(), game::K_FIRST_COLONY_NODE, 2);
  const game::ReceivedClock &host = clocks.at(game::K_AUTHORITY_NODE);
  ASSERT_TRUE(host.heard);
  EXPECT_EQ(host.emitTurn, 11);
  EXPECT_EQ(host.arrivalTurn, 51);
  EXPECT_EQ(host.senderProperSec, 11);
  EXPECT_FALSE(clocks.at(game::K_FIRST_COLONY_NODE).heard);
  EXPECT_DOUBLE_EQ(game::signalAgeCoordinateSec(host, state.turn(), 1.0), 49.0);
  EXPECT_DOUBLE_EQ(game::signalAgeLocalSec(host, state.turn(), 1.0, 0.1), 4.9);
}
