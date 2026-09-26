/**
 * @file event_loader.h
 * @brief Strict JSON loader for story event sets.
 *
 * The loader accepts exactly the whitelisted vocabulary of event.h and
 * rejects anything else -- an unknown key at any depth, a duplicate event id,
 * a reference to an undeclared event or parameter, a schedule delay that can
 * resolve below one turn -- with a message naming the offending path. Its
 * output is independent of file order: events sort by id, parameters and
 * flags by name (the reserved "dark" flag first), tech tiers by points.
 *
 * Schema (every key optional unless noted):
 *   { "params": { NAME: INT | {"min": INT, "max": INT} },
 *     "tech_tiers": [ {"points": INT, "name": STR} ],
 *     "events": [ { "id": INT (required), "name": STR, "text": STR,
 *                   "source": NODE, "mode": "once" | "scheduled",
 *                   "category": "info"|"tech"|"war"|"treaty"|"collapse"|"silence",
 *                   "triggers": [PREDICATE], "effects": [EFFECT] } ] }
 *   NODE      = "host" | "colony"
 *   INT       = integer | PARAM_NAME | {"param": NAME, "times": int, "plus": int}
 *   PREDICATE = {"turn_at_least": INT} | {"flag_set": NAME} | {"flag_clear": NAME}
 *             | {"compare": {"var": "tech_points"|"tech_tier"|"packets_received"
 *                                   |"notices_received",
 *                            "op": "<"|"<="|"=="|"!="|">="|">", "value": INT}}
 *             | {"received": {"kind": "tech_packet"|"notice", "from": NODE,
 *                             "silent_turns_at_least": INT}}
 *   EFFECT    = {"set_flag": NAME}
 *             | {"emit": {"kind": "tech_packet"|"notice", "to": NODE, "points": INT}}
 *             | {"schedule": {"event": INT, "delay_turns": INT}}
 */

#ifndef BLACKHOLE_GAME_EVENT_LOADER_H
#define BLACKHOLE_GAME_EVENT_LOADER_H

#include <string>
#include <string_view>

#include "game/event.h"

namespace game {

struct EventLoadResult {
  EventSet story;
  std::string error; ///< Empty on success.

  [[nodiscard]] bool ok() const { return error.empty(); }
};

/** @brief Parses a story from JSON text. */
[[nodiscard]] EventLoadResult parseEventSet(std::string_view jsonText);

/** @brief Reads and parses a story file. */
[[nodiscard]] EventLoadResult loadEventSetFile(const std::string &path);

} // namespace game

#endif // BLACKHOLE_GAME_EVENT_LOADER_H
