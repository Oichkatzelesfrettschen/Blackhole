/**
 * @file event.h
 * @brief Story events: node identities, delivery categories, and the
 *        whitelisted trigger/effect vocabulary a story file is built from.
 *
 * An event belongs to one source node (the host civilization at the authority
 * station, or a colony) and is evaluated there, in ascending id order, once per
 * coordinate turn. Its triggers read only that node's own state -- its flags,
 * its counters, and the deliveries that have physically reached it -- so a
 * colony infers the host's fate from what arrives, never from the host's
 * flags. Effects set a flag on the source node, emit a delivery that rides the
 * causal queue (arrival quantized once at emission with ceil), or schedule an
 * event some whole number of turns ahead.
 *
 * Integer fields may name a story parameter (value = times * param + plus); a
 * parameter with min < max is drawn once from the campaign seed, so a story's
 * dark turn is fixed by the seed and replays identically.
 */

#ifndef BLACKHOLE_GAME_EVENT_H
#define BLACKHOLE_GAME_EVENT_H

#include <cstdint>
#include <limits>
#include <optional>
#include <string>
#include <vector>

namespace game {

/** @brief A communicating station: the authority (host) or a colony. */
using NodeId = std::uint32_t;
inline constexpr NodeId K_AUTHORITY_NODE = 0;
inline constexpr NodeId K_FIRST_COLONY_NODE = 1;
/** @brief Sender of a delivery that no node emitted (a fleet's report). */
inline constexpr NodeId K_NO_NODE = 0xFFFFFFFFU;

/** @brief What an arrival is about; the inbox pauses on flagged categories.
 *         Values are serialized. */
enum class EventCategory : std::uint8_t {
  Info = 0,
  Tech = 1,
  War = 2,
  Treaty = 3,
  Collapse = 4,
  Silence = 5,
};
inline constexpr int K_EVENT_CATEGORY_COUNT = 6;

[[nodiscard]] constexpr const char *eventCategoryName(EventCategory category) {
  switch (category) {
  case EventCategory::Info:
    return "info";
  case EventCategory::Tech:
    return "tech";
  case EventCategory::War:
    return "war";
  case EventCategory::Treaty:
    return "treaty";
  case EventCategory::Collapse:
    return "collapse";
  case EventCategory::Silence:
    return "silence";
  }
  return "unknown";
}

/** @brief Flag index 0 is reserved: a node whose "dark" flag is set emits
 *         nothing further, fires no events, and drops whatever reaches it. */
inline constexpr std::uint32_t K_DARK_FLAG = 0;
inline constexpr const char *K_DARK_FLAG_NAME = "dark";
inline constexpr std::uint32_t K_MAX_STORY_FLAGS = 64;
inline constexpr std::uint32_t K_NO_PARAM = 0xFFFFFFFFU;

/**
 * @brief Documented range of story integers. Parameter bounds, literals, and
 *        "plus" lie in [-2^40, 2^40] (2^40 one-day turns is three billion
 *        years); "times" lies in [-2^20, 2^20]. Then |times * param + plus| is
 *        below 2^61, so no evaluation of a story integer can overflow int64,
 *        and a seeded span max - min + 1 is below 2^42. The loader rejects
 *        anything outside these ranges; CampaignState rejects a hand-built
 *        story that strays outside them.
 */
inline constexpr std::int64_t K_STORY_INT_LIMIT = std::int64_t{1} << 40;
inline constexpr std::int64_t K_STORY_TIMES_LIMIT = std::int64_t{1} << 20;

[[nodiscard]] constexpr bool withinStoryLimit(std::int64_t value, std::int64_t limit) {
  return value >= -limit && value <= limit;
}

/** @brief times * value + plus, or nullopt when it overflows int64. */
[[nodiscard]] inline std::optional<std::int64_t> checkedLinear(std::int64_t times,
                                                               std::int64_t value,
                                                               std::int64_t plus) {
  std::int64_t product = 0;
  std::int64_t sum = 0;
  if (__builtin_mul_overflow(times, value, &product) || __builtin_add_overflow(product, plus, &sum)) {
    return std::nullopt;
  }
  return sum;
}

/** @brief lhs + rhs clamped to the int64 range. A colony's tech points
 *         accumulate one packet (at most 2^40 points) per arrival for up to
 *         K_SAVE_MAX_TURN turns, which can exceed int64; they saturate instead
 *         of overflowing, so tiers stay monotone and the digest defined. */
[[nodiscard]] inline std::int64_t saturatingAdd(std::int64_t lhs, std::int64_t rhs) {
  std::int64_t sum = 0;
  if (!__builtin_add_overflow(lhs, rhs, &sum)) {
    return sum;
  }
  return rhs > 0 ? std::numeric_limits<std::int64_t>::max()
                 : std::numeric_limits<std::int64_t>::min();
}

/** @brief An integer that is a literal (param == K_NO_PARAM) or
 *         times * param + plus. */
struct IntRef {
  std::int64_t plus = 0;
  std::int64_t times = 1;
  std::uint32_t param = K_NO_PARAM;
};

/** @brief A story parameter: fixed when min == max, else drawn from the seed
 *         uniformly in [min, max]. */
struct EventParam {
  std::string name;
  std::int64_t min = 0;
  std::int64_t max = 0;
};

enum class PredicateKind : std::uint8_t {
  TurnAtLeast = 0, ///< Coordinate turn >= value.
  FlagSet = 1,     ///< Source-node flag set.
  FlagClear = 2,   ///< Source-node flag clear.
  Compare = 3,     ///< Source-node counter compared with value.
  Received = 4,    ///< A delivery of receivedKind from receivedFrom has arrived here.
};

enum class CompareVar : std::uint8_t {
  TechPoints = 0,
  TechTier = 1,
  PacketsReceived = 2,
  NoticesReceived = 3,
};

enum class CompareOp : std::uint8_t {
  Less = 0,
  LessEqual = 1,
  Equal = 2,
  NotEqual = 3,
  GreaterEqual = 4,
  Greater = 5,
};

/** @brief Node-to-node payloads a story emits. Values are serialized. */
enum class EmitKind : std::uint8_t {
  TechPacket = 0, ///< Technology data: adds points at the destination.
  Notice = 1,     ///< A message in the event's category.
};

struct EventPredicate {
  PredicateKind kind = PredicateKind::TurnAtLeast;
  IntRef value{};             ///< TurnAtLeast / Compare operand; Received silence threshold.
  std::uint32_t flag = 0;     ///< FlagSet / FlagClear.
  CompareVar var = CompareVar::TechPoints;
  CompareOp op = CompareOp::GreaterEqual;
  EmitKind receivedKind = EmitKind::TechPacket;
  NodeId receivedFrom = K_AUTHORITY_NODE;
  /// Received: also require the latest such arrival to be at least `value`
  /// turns old (a silence test); false means any arrival ever satisfies it.
  bool silentFor = false;
};

enum class EffectKind : std::uint8_t {
  SetFlag = 0,
  Emit = 1,
  Schedule = 2,
};

struct EventEffect {
  EffectKind kind = EffectKind::SetFlag;
  std::uint32_t flag = 0;              ///< SetFlag.
  EmitKind emitKind = EmitKind::Notice;
  NodeId to = K_AUTHORITY_NODE;        ///< Emit destination node.
  std::int64_t techPoints = 0;         ///< Emit TechPacket: points carried.
  std::uint32_t event = 0;             ///< Schedule: target event id.
  IntRef delayTurns{};                 ///< Schedule: whole turns ahead, >= 1.
};

/** @brief Once: evaluated every turn until it fires, then never again.
 *         Scheduled: evaluated only on turns a schedule effect named it, and
 *         may fire each time. */
enum class EventMode : std::uint8_t {
  Once = 0,
  Scheduled = 1,
};

struct EventDef {
  std::uint32_t id = 0;
  std::string name;
  std::string text; ///< Inbox text for notices this event emits.
  NodeId source = K_AUTHORITY_NODE;
  EventMode mode = EventMode::Once;
  EventCategory category = EventCategory::Info;
  std::vector<EventPredicate> triggers; ///< All must hold.
  std::vector<EventEffect> effects;     ///< Applied in order.
};

/** @brief A technology tier reached when a colony's points meet `points`. */
struct TechLevel {
  std::int64_t points = 0;
  std::string name;
};

/** @brief A loaded story: parameters and flags sorted by name (the reserved
 *         dark flag first), events sorted by id, tech tiers by points. */
struct EventSet {
  std::vector<EventParam> params;
  std::vector<std::string> flags;
  std::vector<TechLevel> techTiers;
  std::vector<EventDef> events;

  [[nodiscard]] bool empty() const { return events.empty() && techTiers.empty(); }
};

/** @brief Field-by-field little-endian bytes of a story: the bytes the
 *         campaign serialization carries for its configured story. */
void appendEventSet(std::vector<std::uint8_t> &out, const EventSet &story);

/** @brief FNV-1a 64 over appendEventSet's bytes: identifies a story in a save. */
[[nodiscard]] std::uint64_t eventSetDigest(const EventSet &story);

/// Most occurrences one event may run from a single seed firing (or, inside a
/// repeating cycle, per pass round the cycle): the fan-out bound a story's
/// schedule graph must respect.
inline constexpr std::uint64_t K_MAX_SCHEDULE_FANOUT = 1024;

/** @brief Whether a story's schedules can multiply occurrences without bound,
 *         and how. Values name the first violation found. */
enum class ScheduleGrowth : std::uint8_t {
  Bounded = 0,
  BranchingCycle = 1, ///< An event on a cycle schedules into that cycle twice or more.
  ChainedCycles = 2,  ///< A repeating cycle feeds another cycle, adding a stream every pass.
  FanOut = 3,         ///< Some event runs more than K_MAX_SCHEDULE_FANOUT times per seed.
};

/**
 * @brief Classifies a story's schedule graph. Each schedule entry is one
 *        occurrence, so occurrences multiply along schedule edges. Growth is
 *        bounded exactly when every repeating cycle is simple (each event on it
 *        schedules one successor on it), no cycle is downstream of another, and
 *        the occurrence count reaching each event -- the saturating sum over
 *        schedule paths from once-only seeds (and from cycles, per pass) of the
 *        products of edge multiplicities -- stays within K_MAX_SCHEDULE_FANOUT.
 *        Checked statically (triggers run only at run time) by an iterative
 *        Tarjan SCC pass and a dynamic program over the condensation, in time
 *        and space linear in events plus schedule effects. Events must be
 *        sorted by id; schedules to missing events are ignored.
 */
[[nodiscard]] ScheduleGrowth scheduleGrowth(const EventSet &story);

} // namespace game

#endif // BLACKHOLE_GAME_EVENT_H
