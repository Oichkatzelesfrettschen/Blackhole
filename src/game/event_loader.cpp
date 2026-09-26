/**
 * @file event_loader.cpp
 * @brief Strict JSON story loader (nlohmann_json).
 */

#include "game/event_loader.h"

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <fstream>
#include <ios>
#include <initializer_list>
#include <map>
#include <optional>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <vector>

#include <nlohmann/json.hpp>
#include <nlohmann/json_fwd.hpp>

#include "game/event.h"

namespace game {

namespace {

using Json = nlohmann::json;

class LoadError : public std::runtime_error {
public:
  using std::runtime_error::runtime_error;
};

[[noreturn]] void fail(const std::string &path, const std::string &message) {
  throw LoadError(path + ": " + message);
}

void requireObject(const Json &value, const std::string &path) {
  if (!value.is_object()) {
    fail(path, "expected an object");
  }
}

void rejectUnknownKeys(const Json &object, const std::string &path,
                       std::initializer_list<std::string_view> allowed) {
  requireObject(object, path);
  for (const auto &[key, value] : object.items()) {
    static_cast<void>(value);
    if (std::ranges::find(allowed, std::string_view(key)) == allowed.end()) {
      fail(path, "unknown key \"" + key + "\"");
    }
  }
}

/** @brief An integer in [-limit, limit]. An unsigned literal above INT64_MAX
 *         is refused before any conversion could wrap it. */
std::int64_t requireInteger(const Json &value, const std::string &path,
                            std::int64_t limit = K_STORY_INT_LIMIT) {
  if (!value.is_number_integer()) {
    fail(path, "expected an integer");
  }
  if (value.is_number_unsigned() &&
      value.get<std::uint64_t>() > static_cast<std::uint64_t>(limit)) {
    fail(path, "integer outside [-" + std::to_string(limit) + ", " + std::to_string(limit) + "]");
  }
  const auto integer = value.get<std::int64_t>();
  if (!withinStoryLimit(integer, limit)) {
    fail(path, "integer outside [-" + std::to_string(limit) + ", " + std::to_string(limit) + "]");
  }
  return integer;
}

/** @brief An id: an integer in [0, 2^32 - 1]. */
std::uint32_t requireId(const Json &value, const std::string &path) {
  constexpr std::int64_t kMaxId = 0xFFFFFFFFLL;
  if (!value.is_number_integer() ||
      (value.is_number_unsigned() && value.get<std::uint64_t>() > static_cast<std::uint64_t>(kMaxId))) {
    fail(path, "expected an id in [0, 4294967295]");
  }
  const auto id = value.get<std::int64_t>();
  if (id < 0 || id > kMaxId) {
    fail(path, "expected an id in [0, 4294967295]");
  }
  return static_cast<std::uint32_t>(id);
}

std::string requireString(const Json &value, const std::string &path) {
  if (!value.is_string()) {
    fail(path, "expected a string");
  }
  return value.get<std::string>();
}

/** @brief The single key of a one-key object (a predicate or an effect). */
std::pair<std::string, const Json *> singleEntry(const Json &object, const std::string &path) {
  requireObject(object, path);
  if (object.size() != 1) {
    fail(path, "expected exactly one key");
  }
  const auto entry = object.begin();
  return {entry.key(), &entry.value()};
}

template <typename Enum>
Enum lookup(const std::string &text, const std::vector<std::pair<std::string_view, Enum>> &table,
            const std::string &path) {
  for (const auto &[name, value] : table) {
    if (name == text) {
      return value;
    }
  }
  fail(path, "unknown value \"" + text + "\"");
}

class Loader {
public:
  EventSet load(const Json &root) {
    rejectUnknownKeys(root, "$", {"params", "tech_tiers", "events"});
    if (root.contains("params")) {
      loadParams(root.at("params"));
    }
    if (root.contains("tech_tiers")) {
      loadTiers(root.at("tech_tiers"));
    }
    if (root.contains("events")) {
      loadEvents(root.at("events"));
    }
    finishFlags();
    checkSchedules();
    return std::move(story_);
  }

private:
  void loadParams(const Json &params) {
    requireObject(params, "$.params");
    // nlohmann objects iterate in key order, so parameter indices follow names.
    for (const auto &[name, value] : params.items()) {
      const std::string path = "$.params." + name;
      EventParam param;
      param.name = name;
      if (value.is_object()) {
        rejectUnknownKeys(value, path, {"min", "max"});
        if (!value.contains("min") || !value.contains("max")) {
          fail(path, "a seeded parameter needs min and max");
        }
        param.min = requireInteger(value.at("min"), path + ".min");
        param.max = requireInteger(value.at("max"), path + ".max");
        if (param.max < param.min) {
          fail(path, "max below min");
        }
      } else {
        param.min = requireInteger(value, path);
        param.max = param.min;
      }
      story_.params.push_back(param);
    }
  }

  void loadTiers(const Json &tiers) {
    if (!tiers.is_array()) {
      fail("$.tech_tiers", "expected an array");
    }
    for (std::size_t index = 0; index < tiers.size(); ++index) {
      const std::string path = "$.tech_tiers[" + std::to_string(index) + "]";
      const Json &tier = tiers.at(index);
      rejectUnknownKeys(tier, path, {"points", "name"});
      TechLevel level;
      if (!tier.contains("points")) {
        fail(path, "missing points");
      }
      level.points = requireInteger(tier.at("points"), path + ".points");
      if (level.points < 0) {
        fail(path + ".points", "tech points must be non-negative");
      }
      if (tier.contains("name")) {
        level.name = requireString(tier.at("name"), path + ".name");
      }
      story_.techTiers.push_back(level);
    }
    std::ranges::sort(story_.techTiers, [](const TechLevel &lhs, const TechLevel &rhs) {
      return lhs.points != rhs.points ? lhs.points < rhs.points : lhs.name < rhs.name;
    });
  }

  [[nodiscard]] std::uint32_t paramIndex(const std::string &name, const std::string &path) const {
    const auto found = std::ranges::find(story_.params, name, &EventParam::name);
    if (found == story_.params.end()) {
      fail(path, "unknown parameter \"" + name + "\"");
    }
    return static_cast<std::uint32_t>(found - story_.params.begin());
  }

  [[nodiscard]] IntRef loadInt(const Json &value, const std::string &path) const {
    IntRef ref;
    if (value.is_string()) {
      ref.param = paramIndex(value.get<std::string>(), path);
      ref.plus = 0;
      return ref;
    }
    if (value.is_object()) {
      rejectUnknownKeys(value, path, {"param", "times", "plus"});
      if (!value.contains("param")) {
        fail(path, "missing param");
      }
      ref.param = paramIndex(requireString(value.at("param"), path + ".param"), path + ".param");
      if (value.contains("times")) {
        ref.times = requireInteger(value.at("times"), path + ".times", K_STORY_TIMES_LIMIT);
      }
      if (value.contains("plus")) {
        ref.plus = requireInteger(value.at("plus"), path + ".plus");
      }
      return ref;
    }
    ref.plus = requireInteger(value, path);
    return ref;
  }

  /** @brief Smallest value an IntRef can take over its parameter's range. */
  [[nodiscard]] std::int64_t minimumOf(const IntRef &ref) const {
    if (ref.param == K_NO_PARAM) {
      return ref.plus;
    }
    // Within the documented ranges neither end can overflow; checkedLinear
    // makes that a checked fact rather than an assumption.
    const EventParam &param = story_.params.at(ref.param);
    const std::optional<std::int64_t> atMin = checkedLinear(ref.times, param.min, ref.plus);
    const std::optional<std::int64_t> atMax = checkedLinear(ref.times, param.max, ref.plus);
    if (!atMin.has_value() || !atMax.has_value()) {
      fail("$", "integer reference overflows");
    }
    return std::min(atMin.value(), atMax.value());
  }

  static NodeId loadNode(const Json &value, const std::string &path) {
    return lookup<NodeId>(requireString(value, path),
                          {{"host", K_AUTHORITY_NODE}, {"colony", K_FIRST_COLONY_NODE}}, path);
  }

  static EmitKind loadEmitKind(const Json &value, const std::string &path) {
    return lookup<EmitKind>(requireString(value, path),
                            {{"tech_packet", EmitKind::TechPacket}, {"notice", EmitKind::Notice}},
                            path);
  }

  std::uint32_t internFlag(const Json &value, const std::string &path) {
    const std::string name = requireString(value, path);
    if (name.empty()) {
      fail(path, "empty flag name");
    }
    const auto [entry, inserted] =
        provisionalFlags_.emplace(name, static_cast<std::uint32_t>(provisionalFlags_.size()));
    static_cast<void>(inserted);
    return entry->second;
  }

  EventPredicate loadPredicate(const Json &object, const std::string &path) {
    const auto [key, value] = singleEntry(object, path);
    const std::string valuePath = path + "." + key;
    EventPredicate predicate;
    if (key == "turn_at_least") {
      predicate.kind = PredicateKind::TurnAtLeast;
      predicate.value = loadInt(*value, valuePath);
    } else if (key == "flag_set" || key == "flag_clear") {
      predicate.kind = key == "flag_set" ? PredicateKind::FlagSet : PredicateKind::FlagClear;
      predicate.flag = internFlag(*value, valuePath);
    } else if (key == "compare") {
      rejectUnknownKeys(*value, valuePath, {"var", "op", "value"});
      if (!value->contains("var") || !value->contains("op") || !value->contains("value")) {
        fail(valuePath, "compare needs var, op, and value");
      }
      predicate.kind = PredicateKind::Compare;
      predicate.var = lookup<CompareVar>(requireString(value->at("var"), valuePath + ".var"),
                                         {{"tech_points", CompareVar::TechPoints},
                                          {"tech_tier", CompareVar::TechTier},
                                          {"packets_received", CompareVar::PacketsReceived},
                                          {"notices_received", CompareVar::NoticesReceived}},
                                         valuePath + ".var");
      predicate.op = lookup<CompareOp>(requireString(value->at("op"), valuePath + ".op"),
                                       {{"<", CompareOp::Less},
                                        {"<=", CompareOp::LessEqual},
                                        {"==", CompareOp::Equal},
                                        {"!=", CompareOp::NotEqual},
                                        {">=", CompareOp::GreaterEqual},
                                        {">", CompareOp::Greater}},
                                       valuePath + ".op");
      predicate.value = loadInt(value->at("value"), valuePath + ".value");
    } else if (key == "received") {
      rejectUnknownKeys(*value, valuePath, {"kind", "from", "silent_turns_at_least"});
      if (!value->contains("kind") || !value->contains("from")) {
        fail(valuePath, "received needs kind and from");
      }
      predicate.kind = PredicateKind::Received;
      predicate.receivedKind = loadEmitKind(value->at("kind"), valuePath + ".kind");
      predicate.receivedFrom = loadNode(value->at("from"), valuePath + ".from");
      if (value->contains("silent_turns_at_least")) {
        predicate.silentFor = true;
        predicate.value =
            loadInt(value->at("silent_turns_at_least"), valuePath + ".silent_turns_at_least");
        if (minimumOf(predicate.value) < 0) {
          fail(valuePath + ".silent_turns_at_least", "a silence threshold must be non-negative");
        }
      }
    } else {
      fail(path, "unknown predicate \"" + key + "\"");
    }
    return predicate;
  }

  EventEffect loadEffect(const Json &object, const std::string &path) {
    const auto [key, value] = singleEntry(object, path);
    const std::string valuePath = path + "." + key;
    EventEffect effect;
    if (key == "set_flag") {
      effect.kind = EffectKind::SetFlag;
      effect.flag = internFlag(*value, valuePath);
    } else if (key == "emit") {
      rejectUnknownKeys(*value, valuePath, {"kind", "to", "points"});
      if (!value->contains("kind") || !value->contains("to")) {
        fail(valuePath, "emit needs kind and to");
      }
      effect.kind = EffectKind::Emit;
      effect.emitKind = loadEmitKind(value->at("kind"), valuePath + ".kind");
      effect.to = loadNode(value->at("to"), valuePath + ".to");
      if (value->contains("points")) {
        if (effect.emitKind != EmitKind::TechPacket) {
          fail(valuePath + ".points", "only a tech_packet carries points");
        }
        effect.techPoints = requireInteger(value->at("points"), valuePath + ".points");
      }
    } else if (key == "schedule") {
      rejectUnknownKeys(*value, valuePath, {"event", "delay_turns"});
      if (!value->contains("event") || !value->contains("delay_turns")) {
        fail(valuePath, "schedule needs event and delay_turns");
      }
      effect.kind = EffectKind::Schedule;
      effect.event = requireId(value->at("event"), valuePath + ".event");
      effect.delayTurns = loadInt(value->at("delay_turns"), valuePath + ".delay_turns");
      if (minimumOf(effect.delayTurns) < 1) {
        fail(valuePath + ".delay_turns", "a schedule delay must be at least one turn");
      }
    } else {
      fail(path, "unknown effect \"" + key + "\"");
    }
    return effect;
  }

  void loadEvents(const Json &events) {
    if (!events.is_array()) {
      fail("$.events", "expected an array");
    }
    for (std::size_t index = 0; index < events.size(); ++index) {
      const std::string path = "$.events[" + std::to_string(index) + "]";
      const Json &object = events.at(index);
      rejectUnknownKeys(object, path,
                        {"id", "name", "text", "source", "mode", "category", "triggers", "effects"});
      if (!object.contains("id")) {
        fail(path, "missing id");
      }
      EventDef event;
      event.id = requireId(object.at("id"), path + ".id");
      if (object.contains("name")) {
        event.name = requireString(object.at("name"), path + ".name");
      }
      if (object.contains("text")) {
        event.text = requireString(object.at("text"), path + ".text");
      }
      if (object.contains("source")) {
        event.source = loadNode(object.at("source"), path + ".source");
      }
      if (object.contains("mode")) {
        event.mode = lookup<EventMode>(requireString(object.at("mode"), path + ".mode"),
                                       {{"once", EventMode::Once}, {"scheduled", EventMode::Scheduled}},
                                       path + ".mode");
      }
      if (object.contains("category")) {
        event.category =
            lookup<EventCategory>(requireString(object.at("category"), path + ".category"),
                                  {{"info", EventCategory::Info},
                                   {"tech", EventCategory::Tech},
                                   {"war", EventCategory::War},
                                   {"treaty", EventCategory::Treaty},
                                   {"collapse", EventCategory::Collapse},
                                   {"silence", EventCategory::Silence}},
                                  path + ".category");
      }
      loadList(object, "triggers", path, [&](const Json &item, const std::string &itemPath) {
        event.triggers.push_back(loadPredicate(item, itemPath));
      });
      loadList(object, "effects", path, [&](const Json &item, const std::string &itemPath) {
        event.effects.push_back(loadEffect(item, itemPath));
      });
      story_.events.push_back(std::move(event));
    }
    std::ranges::sort(story_.events, {}, &EventDef::id);
    const auto duplicate = std::ranges::adjacent_find(
        story_.events, [](const EventDef &lhs, const EventDef &rhs) { return lhs.id == rhs.id; });
    if (duplicate != story_.events.end()) {
      fail("$.events", "duplicate event id " + std::to_string(duplicate->id));
    }
  }

  template <typename Visit>
  static void loadList(const Json &object, const char *key, const std::string &path,
                       const Visit &visit) {
    if (!object.contains(key)) {
      return;
    }
    const Json &list = object.at(key);
    const std::string listPath = path + "." + key;
    if (!list.is_array()) {
      fail(listPath, "expected an array");
    }
    for (std::size_t index = 0; index < list.size(); ++index) {
      visit(list.at(index), listPath + "[" + std::to_string(index) + "]");
    }
  }

  /** @brief Replaces provisional (first-seen) flag indices with the final
   *         order: the reserved dark flag, then the rest by name. */
  void finishFlags() {
    std::vector<std::string> names = {K_DARK_FLAG_NAME};
    for (const auto &[name, provisional] : provisionalFlags_) {
      static_cast<void>(provisional);
      if (name != K_DARK_FLAG_NAME) {
        names.push_back(name); // std::map iterates by name
      }
    }
    if (names.size() > K_MAX_STORY_FLAGS) {
      fail("$", "more than 64 distinct flags");
    }
    std::map<std::uint32_t, std::uint32_t> remap;
    for (const auto &[name, provisional] : provisionalFlags_) {
      remap[provisional] =
          static_cast<std::uint32_t>(std::ranges::find(names, name) - names.begin());
    }
    for (EventDef &event : story_.events) {
      for (EventPredicate &predicate : event.triggers) {
        if (predicate.kind == PredicateKind::FlagSet || predicate.kind == PredicateKind::FlagClear) {
          predicate.flag = remap.at(predicate.flag);
        }
      }
      for (EventEffect &effect : event.effects) {
        if (effect.kind == EffectKind::SetFlag) {
          effect.flag = remap.at(effect.flag);
        }
      }
    }
    story_.flags = std::move(names);
  }

  /** @brief Every schedule names an existing event whose mode is
   *         "scheduled": a once-only event runs from its triggers alone, so a
   *         schedule naming it would be silently ignored. */
  void checkSchedules() const {
    for (const EventDef &event : story_.events) {
      for (const EventEffect &effect : event.effects) {
        if (effect.kind != EffectKind::Schedule) {
          continue;
        }
        const auto target = std::ranges::find(story_.events, effect.event, &EventDef::id);
        if (target == story_.events.end()) {
          fail("$.events", "event " + std::to_string(event.id) + " schedules unknown event " +
                               std::to_string(effect.event));
        }
        if (target->mode != EventMode::Scheduled) {
          fail("$.events", "event " + std::to_string(event.id) + " schedules event " +
                               std::to_string(effect.event) + ", which is not a scheduled event");
        }
      }
    }
  }

  EventSet story_;
  std::map<std::string, std::uint32_t> provisionalFlags_;
};

} // namespace

EventLoadResult parseEventSet(std::string_view jsonText) {
  EventLoadResult result;
  try {
    // JSON keeps only the last of duplicated keys; a story that says the same
    // thing twice is ambiguous, so the parse tracks each open object's keys
    // and the load refuses a repeat anywhere.
    std::vector<std::set<std::string>> openObjects;
    // Optional, not an empty-string sentinel: "" is a legal (and duplicable) key.
    std::optional<std::string> duplicate;
    const Json::parser_callback_t trackKeys = [&openObjects, &duplicate](
                                                  int /*depth*/, Json::parse_event_t event,
                                                  Json &parsed) {
      if (event == Json::parse_event_t::object_start) {
        openObjects.emplace_back();
      } else if (event == Json::parse_event_t::object_end && !openObjects.empty()) {
        openObjects.pop_back();
      } else if (event == Json::parse_event_t::key && !openObjects.empty() &&
                 !openObjects.back().insert(parsed.get<std::string>()).second &&
                 !duplicate.has_value()) {
        duplicate = parsed.get<std::string>();
      }
      return true;
    };
    const Json root = Json::parse(jsonText.begin(), jsonText.end(), trackKeys);
    if (duplicate.has_value()) {
      throw LoadError("$: duplicate key \"" + duplicate.value() + "\"");
    }
    Loader loader;
    result.story = loader.load(root);
  } catch (const LoadError &error) {
    result.error = error.what();
  } catch (const Json::exception &error) {
    result.error = std::string("json: ") + error.what();
  }
  return result;
}

EventLoadResult loadEventSetFile(const std::string &path) {
  const std::ifstream file(path, std::ios::binary);
  if (!file) {
    EventLoadResult result;
    result.error = "cannot open " + path;
    return result;
  }
  std::ostringstream text;
  text << file.rdbuf();
  return parseEventSet(text.str());
}

} // namespace game
