/**
 * @file event_loader_test.cpp
 * @brief Falsification gates for the story loader and the event vocabulary:
 *        unknown keys rejected at every depth, structural errors rejected,
 *        output independent of file order, and each predicate and effect
 *        firing on exactly the turn its definition implies.
 */

#include <gtest/gtest.h>

#include <algorithm>
#include <bit>
#include <cstdint>
#include <limits>
#include <memory>
#include <ranges>
#include <set>
#include <string>
#include <vector>

#include "campaign_test_field.h"
#include "game/campaign.h"
#include "game/event.h"
#include "game/event_loader.h"
#include "game/station_node.h"

namespace {

/** @brief The fake field (authority 1000; bands 960 and 995, 40 and 5 turns
 *         away at one-second turns) with one colony on band 995. */
struct StoryRun {
  campaign_test::FakeTimeField field;
  std::unique_ptr<game::CampaignState> state;
};

std::unique_ptr<StoryRun> runStory(const std::string &json, std::int64_t turns,
                                   std::uint64_t seed = 11) {
  const game::EventLoadResult loaded = game::parseEventSet(json);
  EXPECT_TRUE(loaded.ok()) << loaded.error;
  auto run = std::make_unique<StoryRun>();
  game::CampaignConfig config = campaign_test::fakeConfig();
  config.seed = seed;
  game::ColonyConfig colony;
  colony.bandIndex = 1;
  colony.localTickSec = 1;
  config.colonies = {colony};
  config.story = loaded.story;
  run->state = std::make_unique<game::CampaignState>(config, run->field);
  EXPECT_TRUE(run->state->valid());
  run->state->advanceTurns(turns);
  return run;
}

/** @brief Arrival turns of notices from `event` at `destination`. */
std::vector<std::int64_t> noticeTurns(const game::CampaignState &state, std::uint32_t event,
                                      game::NodeId destination) {
  return state.arrivals() | std::views::filter([&](const game::ArrivalRecord &arrival) {
           return arrival.kind == game::EmitKind::Notice && arrival.payloadIndex == event &&
                  arrival.destination == destination;
         }) |
         std::views::transform(&game::ArrivalRecord::arrivalTurn) |
         std::ranges::to<std::vector<std::int64_t>>();
}

std::string errorOf(const std::string &json) { return game::parseEventSet(json).error; }

} // namespace

// Falsifier: the shipped story failing to load, or its flags, parameters,
// tiers, and events out of the documented order.
TEST(EventLoader, ShippedStoryLoadsInCanonicalOrder) {
  const game::EventLoadResult loaded =
      game::loadEventSetFile(std::string(BLACKHOLE_SOURCE_DIR) + "/assets/events/host_goes_dark.json");
  ASSERT_TRUE(loaded.ok()) << loaded.error;
  const game::EventSet &story = loaded.story;
  ASSERT_FALSE(story.flags.empty());
  EXPECT_EQ(story.flags.front(), game::K_DARK_FLAG_NAME);
  EXPECT_TRUE(std::is_sorted(story.flags.begin() + 1, story.flags.end()));
  EXPECT_TRUE(std::ranges::is_sorted(story.params, {}, &game::EventParam::name));
  EXPECT_TRUE(std::ranges::is_sorted(story.events, {}, &game::EventDef::id));
  EXPECT_TRUE(std::ranges::is_sorted(story.techTiers, {}, &game::TechLevel::points));
  EXPECT_EQ(story.events.front().name, "host_dark");
}

// Falsifier: any unknown key accepted, at the root, in a parameter, a tier,
// an event, a predicate body, an effect body, or an integer reference.
TEST(EventLoader, UnknownKeysRejectedAtEveryDepth) {
  EXPECT_NE(errorOf(R"({"eventz": []})").find("unknown key"), std::string::npos);
  EXPECT_NE(errorOf(R"({"params": {"k": {"min": 1, "max": 2, "mean": 1}}})").find("unknown key"),
            std::string::npos);
  EXPECT_NE(errorOf(R"({"tech_tiers": [{"points": 1, "label": "x"}]})").find("unknown key"),
            std::string::npos);
  EXPECT_NE(errorOf(R"({"events": [{"id": 1, "priority": 2}]})").find("unknown key"),
            std::string::npos);
  EXPECT_NE(
      errorOf(R"({"events": [{"id": 1, "triggers": [{"compare": {"var": "tech_points", "op": ">=", "value": 1, "x": 0}}]}]})")
          .find("unknown key"),
      std::string::npos);
  EXPECT_NE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"emit": {"kind": "notice", "to": "host", "delay": 3}}]}]})")
          .find("unknown key"),
      std::string::npos);
  EXPECT_NE(
      errorOf(R"({"params": {"k": 3}, "events": [{"id": 1, "triggers": [{"turn_at_least": {"param": "k", "scale": 2}}]}]})")
          .find("unknown key"),
      std::string::npos);
  // The error names where the key was.
  EXPECT_NE(errorOf(R"({"events": [{"id": 1}, {"id": 2, "when": 0}]})").find("$.events[1]"),
            std::string::npos);
}

// Falsifier: a structurally broken story loading.
TEST(EventLoader, StructuralErrorsRejected) {
  EXPECT_FALSE(errorOf(R"({"events": [{"id": 1}, {"id": 1}]})").empty());          // duplicate id
  EXPECT_FALSE(errorOf(R"({"events": [{"name": "no id"}]})").empty());             // missing id
  EXPECT_FALSE(errorOf(R"({"events": [{"id": 1, "triggers": [{"sometimes": 1}]}]})").empty());
  EXPECT_FALSE(errorOf(R"({"events": [{"id": 1, "effects": [{"explode": 1}]}]})").empty());
  EXPECT_FALSE(
      errorOf(R"({"events": [{"id": 1, "triggers": [{"turn_at_least": 1, "flag_set": "x"}]}]})")
          .empty()); // a predicate is exactly one key
  EXPECT_FALSE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"schedule": {"event": 9, "delay_turns": 1}}]}]})")
          .empty()); // unknown target
  EXPECT_FALSE(
      errorOf(R"({"events": [{"id": 1, "mode": "scheduled", "effects": [{"schedule": {"event": 1, "delay_turns": 0}}]}]})")
          .empty()); // same-turn cascade
  EXPECT_FALSE(
      errorOf(R"({"params": {"k": {"min": 0, "max": 5}}, "events": [{"id": 1, "mode": "scheduled", "effects": [{"schedule": {"event": 1, "delay_turns": "k"}}]}]})")
          .empty()); // a seeded delay that can draw zero
  EXPECT_FALSE(errorOf(R"({"events": [{"id": 1, "triggers": [{"turn_at_least": "nope"}]}]})").empty());
  EXPECT_FALSE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"emit": {"kind": "notice", "to": "host", "points": 2}}]}]})")
          .empty()); // only packets carry points
  EXPECT_FALSE(errorOf(R"({"events": [{"id": 1, "source": "moon"}]})").empty());
  EXPECT_FALSE(errorOf(R"({"events": [{"id": 1, "category": "gossip"}]})").empty());
  EXPECT_FALSE(errorOf(R"({"params": {"k": {"min": 5, "max": 1}}})").empty());
  EXPECT_FALSE(errorOf(R"({"events": [)").empty()); // malformed JSON
}

// Falsifier: two files differing only in the order of events, parameters,
// tiers, and first flag use producing different stories (compared through
// the campaign's byte serialization, which carries the whole event set).
TEST(EventLoader, OutputIndependentOfFileOrder) {
  const std::string first = R"({
    "params": {"b": 2, "a": {"min": 1, "max": 9}},
    "tech_tiers": [{"points": 5, "name": "late"}, {"points": 1, "name": "early"}],
    "events": [
      {"id": 7, "source": "colony", "mode": "scheduled", "triggers": [{"flag_set": "zeta"}], "effects": [{"set_flag": "alpha"}]},
      {"id": 3, "triggers": [{"turn_at_least": "a"}], "effects": [{"set_flag": "zeta"}, {"schedule": {"event": 7, "delay_turns": "b"}}]}
    ]})";
  const std::string second = R"({
    "events": [
      {"id": 3, "effects": [{"set_flag": "zeta"}, {"schedule": {"event": 7, "delay_turns": "b"}}], "triggers": [{"turn_at_least": "a"}]},
      {"id": 7, "mode": "scheduled", "source": "colony", "effects": [{"set_flag": "alpha"}], "triggers": [{"flag_set": "zeta"}]}
    ],
    "tech_tiers": [{"points": 1, "name": "early"}, {"points": 5, "name": "late"}],
    "params": {"a": {"min": 1, "max": 9}, "b": 2}})";
  const std::unique_ptr<StoryRun> runFirst = runStory(first, 0);
  const std::unique_ptr<StoryRun> runSecond = runStory(second, 0);
  EXPECT_EQ(runFirst->state->serializeState(), runSecond->state->serializeState());
  const game::EventSet story = game::parseEventSet(first).story;
  const std::vector<std::string> expectedFlags = {"dark", "alpha", "zeta"};
  EXPECT_EQ(story.flags, expectedFlags);
}

// Falsifier: turn_at_least firing on any turn but the named one, or a
// zero-delay notice to the event's own node arriving on a later turn.
TEST(EventPredicates, TurnAtLeastFiresOnItsTurnAndOnlyOnce) {
  const std::unique_ptr<StoryRun> run = runStory(R"({"events": [
      {"id": 1, "triggers": [{"turn_at_least": 5}], "effects": [{"emit": {"kind": "notice", "to": "host"}}]}]})",
                                                 20);
  EXPECT_EQ(noticeTurns(*run->state, 1, game::K_AUTHORITY_NODE), std::vector<std::int64_t>{5});
}

// Falsifier: packets landing off emit + 5 turns, a scheduled event missing a
// cadence step, or a compare predicate firing before the points arrive.
TEST(EventPredicates, ScheduledPacketsAndCompare) {
  const std::unique_ptr<StoryRun> run = runStory(R"({"events": [
      {"id": 1, "triggers": [{"turn_at_least": 1}],
       "effects": [{"emit": {"kind": "tech_packet", "to": "colony", "points": 2}},
                   {"schedule": {"event": 2, "delay_turns": 3}}]},
      {"id": 2, "mode": "scheduled",
       "effects": [{"emit": {"kind": "tech_packet", "to": "colony", "points": 2}},
                   {"schedule": {"event": 2, "delay_turns": 3}}]},
      {"id": 5, "source": "colony",
       "triggers": [{"compare": {"var": "tech_points", "op": ">=", "value": 6}}],
       "effects": [{"emit": {"kind": "notice", "to": "colony"}}]}]})",
                                                 20);
  std::vector<std::int64_t> packetArrivals;
  for (const game::ArrivalRecord &arrival : run->state->arrivals()) {
    if (arrival.kind == game::EmitKind::TechPacket) {
      EXPECT_EQ(arrival.arrivalTurn, arrival.emitTurn + 5);
      EXPECT_EQ(arrival.emitTurn % 3, 1);
      packetArrivals.push_back(arrival.arrivalTurn);
    }
  }
  const std::vector<std::int64_t> expected = {6, 9, 12, 15, 18};
  EXPECT_EQ(packetArrivals, expected);
  // Points reach 6 with the third packet, at turn 12.
  EXPECT_EQ(noticeTurns(*run->state, 5, 1), std::vector<std::int64_t>{12});
}

// Falsifier: a flag set by a lower-id event invisible to a higher-id event in
// the same turn, or flag_clear still true after the flag is set.
TEST(EventPredicates, FlagsAreVisibleInIdOrderWithinATurn) {
  const std::unique_ptr<StoryRun> run = runStory(R"({"events": [
      {"id": 1, "triggers": [{"turn_at_least": 1}], "effects": [{"emit": {"kind": "tech_packet", "to": "colony"}}]},
      {"id": 6, "source": "colony",
       "triggers": [{"flag_clear": "seen"}, {"received": {"kind": "tech_packet", "from": "host"}}],
       "effects": [{"set_flag": "seen"}, {"emit": {"kind": "notice", "to": "colony"}}]},
      {"id": 7, "source": "colony", "triggers": [{"flag_set": "seen"}],
       "effects": [{"emit": {"kind": "notice", "to": "colony"}}]}]})",
                                                 20);
  EXPECT_EQ(noticeTurns(*run->state, 6, 1), std::vector<std::int64_t>{6});
  EXPECT_EQ(noticeTurns(*run->state, 7, 1), std::vector<std::int64_t>{6});
}

// Falsifier: a silence test firing before the latest arrival is old enough,
// or firing with no arrival ever.
TEST(EventPredicates, ReceivedSilenceCountsFromTheLatestArrival) {
  const std::unique_ptr<StoryRun> run = runStory(R"({"events": [
      {"id": 1, "triggers": [{"turn_at_least": 1}], "effects": [{"emit": {"kind": "tech_packet", "to": "colony"}}]},
      {"id": 2, "triggers": [{"turn_at_least": 4}], "effects": [{"emit": {"kind": "tech_packet", "to": "colony"}}]},
      {"id": 8, "source": "colony",
       "triggers": [{"received": {"kind": "tech_packet", "from": "host", "silent_turns_at_least": 10}}],
       "effects": [{"emit": {"kind": "notice", "to": "colony"}}]},
      {"id": 9, "source": "colony",
       "triggers": [{"received": {"kind": "notice", "from": "host"}}],
       "effects": [{"emit": {"kind": "notice", "to": "colony"}}]}]})",
                                                 40);
  // Latest packet lands at 4 + 5 = 9; ten silent turns later is 19.
  EXPECT_EQ(noticeTurns(*run->state, 8, 1), std::vector<std::int64_t>{19});
  EXPECT_TRUE(noticeTurns(*run->state, 9, 1).empty());
}

// Falsifier: a dark node emitting, firing events, or receiving; the dark event
// (lower id) taking effect after a same-turn emission.
TEST(EventPredicates, DarkNodeEmitsAndReceivesNothing) {
  const std::unique_ptr<StoryRun> run = runStory(R"({"events": [
      {"id": 1, "triggers": [{"turn_at_least": 3}], "effects": [{"set_flag": "dark"}]},
      {"id": 2, "triggers": [{"turn_at_least": 1}],
       "effects": [{"emit": {"kind": "tech_packet", "to": "colony"}}, {"schedule": {"event": 3, "delay_turns": 1}}]},
      {"id": 3, "mode": "scheduled",
       "effects": [{"emit": {"kind": "tech_packet", "to": "colony"}}, {"schedule": {"event": 3, "delay_turns": 1}}]},
      {"id": 4, "source": "colony", "triggers": [{"turn_at_least": 1}],
       "effects": [{"emit": {"kind": "notice", "to": "host"}}]}]})",
                                                 30);
  std::set<std::int64_t> emitTurns;
  for (const game::ArrivalRecord &arrival : run->state->arrivals()) {
    if (arrival.kind == game::EmitKind::TechPacket) {
      emitTurns.insert(arrival.emitTurn);
    }
  }
  const std::set<std::int64_t> expected = {1, 2};
  EXPECT_EQ(emitTurns, expected);
  // The colony's notice leaves at 1 and would land at 6: the host is dark.
  EXPECT_TRUE(noticeTurns(*run->state, 4, game::K_AUTHORITY_NODE).empty());
  EXPECT_TRUE(run->state->nodes().front().dark());
}

// Falsifier: a seeded parameter outside its range, differing between two
// campaigns with one seed, or identical across every seed tried.
TEST(EventPredicates, SeededParameterIsDeterministicPerSeed) {
  const std::string json = R"({"params": {"dark_turn": {"min": 100, "max": 200}}})";
  std::set<std::int64_t> draws;
  for (std::uint64_t seed = 1; seed <= 16; ++seed) {
    const std::int64_t value = runStory(json, 0, seed)->state->storyParam("dark_turn").value_or(-1);
    EXPECT_GE(value, 100);
    EXPECT_LE(value, 200);
    EXPECT_EQ(value, runStory(json, 0, seed)->state->storyParam("dark_turn").value_or(-2));
    draws.insert(value);
  }
  EXPECT_GT(draws.size(), 8U);
  EXPECT_FALSE(runStory(json, 0)->state->storyParam("missing").has_value());
}

namespace {

/** @brief A campaign built directly from a hand-made story, bypassing the
 *         loader, so the core's own validation is what stands. */
bool storyBuildsValid(const game::EventSet &story) {
  const campaign_test::FakeTimeField field;
  game::CampaignConfig config = campaign_test::fakeConfig();
  game::ColonyConfig colony;
  colony.bandIndex = 1;
  colony.localTickSec = 1;
  config.colonies = {colony};
  config.story = story;
  const game::CampaignState state(config, field);
  return state.valid();
}

game::EventSet scheduleStory(const game::IntRef &delay) {
  game::EventSet story;
  story.flags = {game::K_DARK_FLAG_NAME};
  game::EventDef event;
  event.id = 1;
  event.mode = game::EventMode::Scheduled;
  game::EventEffect schedule;
  schedule.kind = game::EffectKind::Schedule;
  schedule.event = 1;
  schedule.delayTurns = delay;
  event.effects = {schedule};
  story.events = {event};
  return story;
}

} // namespace

// Falsifier: an integer the documented story range excludes loading -- the
// full int64 parameter range (whose span overflows), an unsigned literal above
// INT64_MAX, a multiplier past 2^20, a literal past 2^40 -- or a negative
// tier or silence threshold, or a schedule target past uint32.
TEST(EventLoader, StoryIntegersOutsideTheDocumentedRangeRejected) {
  EXPECT_FALSE(
      errorOf(R"({"params": {"k": {"min": -9223372036854775808, "max": 9223372036854775807}}})")
          .empty());
  EXPECT_FALSE(errorOf(R"({"params": {"k": 9223372036854775808}})").empty());
  EXPECT_FALSE(errorOf(R"({"params": {"k": 1099511627777}})").empty());
  EXPECT_TRUE(errorOf(R"({"params": {"k": 1099511627776}})").empty());
  EXPECT_FALSE(
      errorOf(R"({"params": {"k": 3}, "events": [{"id": 1, "triggers": [{"turn_at_least": {"param": "k", "times": 4611686018427387904}}]}]})")
          .empty());
  EXPECT_FALSE(
      errorOf(R"({"params": {"k": 3}, "events": [{"id": 1, "triggers": [{"turn_at_least": {"param": "k", "times": 1048577}}]}]})")
          .empty());
  EXPECT_FALSE(errorOf(R"({"tech_tiers": [{"points": -1}]})").empty());
  EXPECT_FALSE(
      errorOf(R"({"events": [{"id": 1, "triggers": [{"received": {"kind": "notice", "from": "host", "silent_turns_at_least": -5}}]}]})")
          .empty());
  EXPECT_FALSE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"schedule": {"event": 4294967297, "delay_turns": 1}}]}]})")
          .empty());
  EXPECT_FALSE(errorOf(R"({"events": [{"id": 4294967296}]})").empty());
}

// Falsifier: a duplicated key at any depth accepted (the parser would keep
// only the last value, silently).
TEST(EventLoader, DuplicateJsonKeysRejected) {
  EXPECT_NE(errorOf(R"({"params": {"k": 1, "k": 2}})").find("duplicate key"), std::string::npos);
  EXPECT_NE(errorOf(R"({"events": [{"id": 1, "id": 2}]})").find("duplicate key"),
            std::string::npos);
  EXPECT_NE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"emit": {"kind": "notice", "to": "host", "to": "colony"}}]}]})")
          .find("duplicate key"),
      std::string::npos);
  // The same key in sibling objects is not a duplicate.
  EXPECT_TRUE(errorOf(R"({"events": [{"id": 1}, {"id": 2}]})").empty());
}

// Falsifier: a hand-built story the loader would refuse building a valid
// campaign -- or crashing it -- through overflow in a seeded span or a
// times * param + plus, duplicate or unsorted ids, unsorted parameters, or a
// negative tier.
TEST(EventPredicates, CoreRejectsStoriesOutsideTheDocumentedRange) {
  game::EventSet fullRange;
  fullRange.params = {{.name = "k",
                       .min = std::numeric_limits<std::int64_t>::min(),
                       .max = std::numeric_limits<std::int64_t>::max()}};
  EXPECT_FALSE(storyBuildsValid(fullRange));

  game::EventSet wideSpan;
  wideSpan.params = {{.name = "k", .min = -game::K_STORY_INT_LIMIT, .max = game::K_STORY_INT_LIMIT}};
  EXPECT_TRUE(storyBuildsValid(wideSpan));

  game::EventSet overflowing = scheduleStory(
      {.plus = 1, .times = std::numeric_limits<std::int64_t>::max(), .param = 0});
  overflowing.params = {{.name = "k", .min = 3, .max = 3}};
  EXPECT_FALSE(storyBuildsValid(overflowing));
  EXPECT_FALSE(storyBuildsValid(scheduleStory({.plus = std::numeric_limits<std::int64_t>::max()})));
  EXPECT_TRUE(storyBuildsValid(scheduleStory({.plus = 2})));

  game::EventSet duplicateIds = scheduleStory({.plus = 1});
  duplicateIds.events.push_back(duplicateIds.events.front());
  EXPECT_FALSE(storyBuildsValid(duplicateIds));

  game::EventSet unsortedParams;
  unsortedParams.params = {{.name = "b", .min = 1, .max = 1}, {.name = "a", .min = 1, .max = 1}};
  EXPECT_FALSE(storyBuildsValid(unsortedParams));

  game::EventSet negativeTier;
  negativeTier.techTiers = {{.points = -3, .name = "x"}};
  EXPECT_FALSE(storyBuildsValid(negativeTier));
}

// Falsifier: two schedule entries naming one event for one turn collapsing
// into a single occurrence -- each entry must run the event once.
TEST(EventPredicates, EachScheduledOccurrenceRuns) {
  const std::unique_ptr<StoryRun> run = runStory(R"({"events": [
      {"id": 1, "triggers": [{"turn_at_least": 1}],
       "effects": [{"schedule": {"event": 2, "delay_turns": 3}},
                   {"schedule": {"event": 2, "delay_turns": 3}}]},
      {"id": 2, "mode": "scheduled", "effects": [{"emit": {"kind": "notice", "to": "host"}}]}]})",
                                                 10);
  EXPECT_EQ(noticeTurns(*run->state, 2, game::K_AUTHORITY_NODE), (std::vector<std::int64_t>{4, 4}));
}

// Falsifier: a schedule effect naming a once-only event loading (the core
// runs once-only events from their triggers alone, so the schedule would be
// silently ignored), or a duplicated empty key slipping past the duplicate
// check because the empty string doubled as "no duplicate yet".
TEST(EventLoader, ScheduleTargetsAndEmptyDuplicateKeysChecked) {
  EXPECT_NE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"schedule": {"event": 2, "delay_turns": 1}}]},
                             {"id": 2}]})")
          .find("not a scheduled event"),
      std::string::npos);
  EXPECT_NE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"schedule": {"event": 2, "delay_turns": 1}}]},
                             {"id": 2, "mode": "once"}]})")
          .find("not a scheduled event"),
      std::string::npos);
  EXPECT_TRUE(
      errorOf(R"({"events": [{"id": 1, "effects": [{"schedule": {"event": 2, "delay_turns": 1}}]},
                             {"id": 2, "mode": "scheduled"}]})")
          .empty());
  EXPECT_NE(errorOf(R"({"params": {"": 1, "": 2}})").find("duplicate key"), std::string::npos);

  // The core refuses a hand-built story that schedules a once-only event.
  game::EventSet onceTarget = scheduleStory({.plus = 1});
  onceTarget.events.front().mode = game::EventMode::Once;
  EXPECT_FALSE(storyBuildsValid(onceTarget));
}

// An enum holding an arbitrary value of its fixed underlying type, as a
// hand-built story could; every uint8 value is a valid object of these enums.
template <typename Enum> Enum rawEnum(std::uint8_t value) { return std::bit_cast<Enum>(value); }

// Falsifier: a hand-built story with an out-of-range enum discriminant --
// which the loader can never produce -- building a valid campaign; a Received
// predicate with such a kind would index past lastArrivalTurn at run time.
TEST(EventPredicates, CoreRejectsOutOfRangeEnums) {
  const auto withTrigger = [](game::EventPredicate predicate) {
    game::EventSet story;
    story.flags = {game::K_DARK_FLAG_NAME};
    game::EventDef event;
    event.id = 1;
    event.triggers = {predicate};
    story.events = {event};
    return story;
  };
  game::EventPredicate received;
  received.kind = game::PredicateKind::Received;
  EXPECT_TRUE(storyBuildsValid(withTrigger(received)));
  received.receivedKind = rawEnum<game::EmitKind>(7);
  EXPECT_FALSE(storyBuildsValid(withTrigger(received)));

  game::EventPredicate kind;
  kind.kind = rawEnum<game::PredicateKind>(9);
  EXPECT_FALSE(storyBuildsValid(withTrigger(kind)));
  game::EventPredicate compare;
  compare.kind = game::PredicateKind::Compare;
  compare.op = rawEnum<game::CompareOp>(40);
  EXPECT_FALSE(storyBuildsValid(withTrigger(compare)));
  compare.op = game::CompareOp::Less;
  compare.var = rawEnum<game::CompareVar>(40);
  EXPECT_FALSE(storyBuildsValid(withTrigger(compare)));

  game::EventSet badEvent = withTrigger(received);
  badEvent.events.front().triggers.clear();
  badEvent.events.front().mode = rawEnum<game::EventMode>(5);
  EXPECT_FALSE(storyBuildsValid(badEvent));
  badEvent.events.front().mode = game::EventMode::Once;
  badEvent.events.front().category = rawEnum<game::EventCategory>(99);
  EXPECT_FALSE(storyBuildsValid(badEvent));
  badEvent.events.front().category = game::EventCategory::Info;
  game::EventEffect emit;
  emit.kind = game::EffectKind::Emit;
  emit.emitKind = rawEnum<game::EmitKind>(3);
  badEvent.events.front().effects = {emit};
  EXPECT_FALSE(storyBuildsValid(badEvent));
}

// Falsifier: a story whose scheduled events re-schedule into their own cycle
// more than once per pass loading -- its pending occurrences double every
// cycle and exhaust memory within a few dozen turns -- while a simple
// repeating cycle (the shipped packet stream) still loads.
TEST(EventLoader, BranchingScheduleCyclesRejected) {
  EXPECT_NE(
      errorOf(R"({"events": [
        {"id": 1, "triggers": [{"turn_at_least": 1}], "effects": [{"schedule": {"event": 2, "delay_turns": 1}}]},
        {"id": 2, "mode": "scheduled", "effects": [{"schedule": {"event": 2, "delay_turns": 1}},
                                                   {"schedule": {"event": 2, "delay_turns": 1}}]}]})")
          .find("branching schedule cycle"),
      std::string::npos);
  EXPECT_NE(
      errorOf(R"({"events": [
        {"id": 2, "mode": "scheduled", "effects": [{"schedule": {"event": 3, "delay_turns": 1}}]},
        {"id": 3, "mode": "scheduled", "effects": [{"schedule": {"event": 2, "delay_turns": 1}},
                                                   {"schedule": {"event": 3, "delay_turns": 2}}]}]})")
          .find("branching schedule cycle"),
      std::string::npos);
  // A simple cycle, and a once-only event fanning out into it, are bounded.
  EXPECT_TRUE(
      errorOf(R"({"events": [
        {"id": 1, "triggers": [{"turn_at_least": 1}], "effects": [{"schedule": {"event": 2, "delay_turns": 1}},
                                                                  {"schedule": {"event": 2, "delay_turns": 2}}]},
        {"id": 2, "mode": "scheduled", "effects": [{"schedule": {"event": 3, "delay_turns": 1}}]},
        {"id": 3, "mode": "scheduled", "effects": [{"schedule": {"event": 2, "delay_turns": 1}}]}]})")
          .empty());
  game::EventSet branching = scheduleStory({.plus = 1});
  branching.events.front().effects.push_back(branching.events.front().effects.front());
  EXPECT_FALSE(storyBuildsValid(branching));
}

// Falsifier: a hand-built story the loader could never produce building a
// valid campaign: a flag table without the reserved dark flag first (bit 0
// is dark at run time whatever the table says), with unsorted or repeated
// names, or a Received silence threshold below zero (it would fire with no
// silent interval at all).
TEST(EventPredicates, CoreRequiresLoaderShapedFlagsAndThresholds) {
  game::EventSet flags;
  flags.flags = {"dark", "alpha", "zeta"};
  EXPECT_TRUE(storyBuildsValid(flags));
  flags.flags = {"peace", "dark"};
  EXPECT_FALSE(storyBuildsValid(flags));
  flags.flags = {"dark", "zeta", "alpha"};
  EXPECT_FALSE(storyBuildsValid(flags));
  flags.flags = {"dark", "alpha", "alpha"};
  EXPECT_FALSE(storyBuildsValid(flags));
  flags.flags = {"dark", "dark"};
  EXPECT_FALSE(storyBuildsValid(flags));

  game::EventSet silence;
  silence.flags = {game::K_DARK_FLAG_NAME};
  game::EventDef event;
  event.id = 1;
  game::EventPredicate received;
  received.kind = game::PredicateKind::Received;
  received.silentFor = true;
  received.value = {.plus = 0};
  event.triggers = {received};
  silence.events = {event};
  EXPECT_TRUE(storyBuildsValid(silence));
  silence.events.front().triggers.front().value = {.plus = -5};
  EXPECT_FALSE(storyBuildsValid(silence));
}

// Falsifier: the schedule-cycle check needing storage quadratic in the event
// count (200,000 events would need 40 GB as a reachability matrix) or
// recursion deep enough to overflow the stack on a 200,000-long cycle, or
// misjudging that cycle: simple as built, branching with one extra edge.
TEST(EventLoader, ScheduleCycleCheckScalesLinearly) {
  constexpr std::uint32_t kEvents = 200000;
  game::EventSet story;
  story.events.resize(kEvents);
  for (std::uint32_t index = 0; index < kEvents; ++index) {
    game::EventDef &event = story.events.at(index);
    event.id = index + 1;
    event.mode = game::EventMode::Scheduled;
    game::EventEffect schedule;
    schedule.kind = game::EffectKind::Schedule;
    schedule.event = index + 1 == kEvents ? 1U : index + 2;
    schedule.delayTurns = {.plus = 1};
    event.effects = {schedule};
  }
  EXPECT_EQ(game::scheduleGrowth(story), game::ScheduleGrowth::Bounded);
  story.events.at(kEvents / 2).effects.push_back(story.events.at(kEvents / 2).effects.front());
  EXPECT_EQ(game::scheduleGrowth(story), game::ScheduleGrowth::BranchingCycle);
}

namespace {

/** @brief A once-only seed (id 1) and a chain of `length` scheduled events,
 *         each scheduling the next `fanOut` times. */
std::string fanOutChainJson(int length, int fanOut) {
  std::string json = R"({"events": [{"id": 1, "triggers": [{"turn_at_least": 1}],
      "effects": [{"schedule": {"event": 2, "delay_turns": 1}}]})";
  for (int index = 0; index < length; ++index) {
    const int id = index + 2;
    json += R"(, {"id": )" + std::to_string(id) + R"(, "mode": "scheduled", "effects": [)";
    for (int copy = 0; index + 1 < length && copy < fanOut; ++copy) {
      json += (copy > 0 ? ", " : "") + std::string(R"({"schedule": {"event": )") +
              std::to_string(id + 1) + R"(, "delay_turns": 1}})";
    }
    json += "]}";
  }
  return json + "]}";
}

} // namespace

// Falsifier: an acyclic schedule fan-out loading when one pass would run an
// event more than K_MAX_SCHEDULE_FANOUT times (a doubling chain of 12 levels
// runs its last event 2048 times per seed firing and grows exponentially with
// depth), or a cycle feeding another cycle loading (each pass of the first
// adds a permanent stream to the second, so its occurrences per turn grow
// without bound); while a 10-level doubling chain (512) and the shipped
// story still load.
TEST(EventLoader, UnboundedScheduleGrowthRejected) {
  EXPECT_TRUE(errorOf(fanOutChainJson(10, 2)).empty());
  EXPECT_NE(errorOf(fanOutChainJson(12, 2)).find("fan-out"), std::string::npos);
  EXPECT_NE(
      errorOf(R"({"events": [
        {"id": 1, "triggers": [{"turn_at_least": 1}], "effects": [{"schedule": {"event": 2, "delay_turns": 1}}]},
        {"id": 2, "mode": "scheduled", "effects": [{"schedule": {"event": 2, "delay_turns": 1}},
                                                   {"schedule": {"event": 3, "delay_turns": 1}}]},
        {"id": 3, "mode": "scheduled", "effects": [{"schedule": {"event": 3, "delay_turns": 1}}]}]})")
          .find("cycle feeds another cycle"),
      std::string::npos);
  const game::EventLoadResult shipped = game::loadEventSetFile(
      std::string(BLACKHOLE_SOURCE_DIR) + "/assets/events/host_goes_dark.json");
  EXPECT_TRUE(shipped.ok()) << shipped.error;
  EXPECT_EQ(game::scheduleGrowth(shipped.story), game::ScheduleGrowth::Bounded);

  // The core applies the same bound to a hand-built story: triple every
  // fan-out of the loadable 10-level chain (3^9 = 19683 runs).
  game::EventSet tripled = game::parseEventSet(fanOutChainJson(10, 2)).story;
  EXPECT_TRUE(storyBuildsValid(tripled));
  for (game::EventDef &event : tripled.events) {
    if (event.mode == game::EventMode::Scheduled && !event.effects.empty()) {
      event.effects.push_back(event.effects.front());
    }
  }
  EXPECT_EQ(game::scheduleGrowth(tripled), game::ScheduleGrowth::FanOut);
  EXPECT_FALSE(storyBuildsValid(tripled));
}
