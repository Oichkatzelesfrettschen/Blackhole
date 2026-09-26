/**
 * @file save_format.h
 * @brief Versioned campaign save: the scenario, the seed, and the command log,
 *        replayed on load and checked against the saved digest.
 *
 * A save does not snapshot internal state. The campaign is a pure function of
 * its scenario, seed, story, and the ordered commands issued on each turn, so
 * a save records exactly those and the turn reached; load rebuilds the
 * session, replays every command on its issue turn, and accepts the result
 * only when its stateDigest equals the saved one. The digest check binds a
 * save to one build (the determinism scope); a story is identified by its
 * eventSetDigest and must be supplied again on load.
 *
 * Layout, all little-endian:
 *   magic "BHSV", u32 saveFormatVersion,
 *   then sections, each u32 tag + u32 byte length + body, in this order:
 *   'HEAD' u8 scenario, u64 seed, f64 spin (M87 scenario), i32 colonyBand,
 *          u64 story digest (0 without a story)
 *   'CMDS' u32 count, then per command: i64 issueTurn, u8 type, u32 fleet,
 *          i32 targetBand, u8 lane, u8 station, f64 properTimeCostSec,
 *          u32 originNode
 *   'TURN' i64 turn reached
 *   'DGST' u64 stateDigest at that turn
 * Load rejects an unknown version, a wrong tag, a section length that
 * disagrees with its body, truncation, trailing bytes, a header field the
 * rebuilt session does not reproduce (spin, colony band, story digest), a
 * saved turn beyond the scenario's replay budget, a command log out of turn
 * order or past the saved turn, a command the replay refuses, and a digest
 * mismatch. The budget and command checks run before any turn is replayed,
 * so a corrupted turn field costs no replay work.
 *
 * Replay rebuilds only what the scenario constructor and the command log
 * produce. A session changed any other way -- a fleet added with addFleet
 * after construction, or a GargantuaColony session built without its story
 * (no colony, band -1) -- saves but is refused on load, by the digest check
 * or the story check respectively.
 */

#ifndef BLACKHOLE_GAME_SAVE_FORMAT_H
#define BLACKHOLE_GAME_SAVE_FORMAT_H

#include <cstdint>
#include <memory>
#include <string>
#include <vector>

#include "game/campaign_session.h"
#include "game/event.h"

namespace game {

inline constexpr std::uint32_t K_SAVE_FORMAT_VERSION = 1;

/// Wall time of play a save may represent: four hours at the scenario's
/// fastest advance rate (saveReplayTurnBudget).
inline constexpr double K_SAVE_SESSION_WALL_SEC = 4.0 * 3600.0;
/// Manual batches per wall second credited to a player clicking the largest
/// Advance button as fast as the controls allow.
inline constexpr double K_SAVE_MANUAL_BATCHES_PER_WALL_SEC = 10.0;

/**
 * @brief Largest saved turn load replays for this scenario: the turns
 *        K_SAVE_SESSION_WALL_SEC of play reach at the scenario's fastest
 *        advance rate, the larger of
 *  - real time at the slowest station clock and the fastest scale:
 *    K_MAX_LOCAL_SECONDS_PER_WALL_SECOND / (min dtau/dt * secondsPerTurn),
 *    3600 / (1.6286e-5 * 86400) = 2558 turns per wall second on Miller's
 *    orbit, so 3.68e7 turns in four hours -- the deep colony's whole
 *    365-local-day charter is 2.24e7 turns (2.4 wall hours);
 *  - manual batches: K_MAX_MANUAL_BATCH_TURNS * K_SAVE_MANUAL_BATCHES_PER_WALL_SEC
 *    = 250 turns per wall second, so 3.6e6 turns in four hours, which binds
 *    for M87, Gargantua, and the survey colony, whose stations all run
 *    near dtau/dt = 1 (real time there is about 0.04 turns per wall second).
 * Replay cost scales with the budget, so a save's scenario, not a global
 * constant, sets how long the worst corrupted turn field can make a load run.
 */
[[nodiscard]] std::int64_t saveReplayTurnBudget(const CampaignState &state);

/** @brief Serializes a session's save: its scenario, seed, field spin,
 *         colony band, story digest, command log, turn, and digest. */
[[nodiscard]] std::vector<std::uint8_t> saveCampaign(const CampaignSession &session);

struct CampaignLoadResult {
  std::unique_ptr<CampaignSession> session;
  std::string error; ///< Empty on success.

  [[nodiscard]] bool ok() const { return error.empty() && session != nullptr; }
};

/** @brief Rebuilds and replays a save. `story` must be the story the save was
 *         made with (checked by digest) for a colony scenario; null otherwise. */
[[nodiscard]] CampaignLoadResult loadCampaign(const std::vector<std::uint8_t> &bytes,
                                              const EventSet *story);

} // namespace game

#endif // BLACKHOLE_GAME_SAVE_FORMAT_H
