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
 * disagrees with its body, truncation, trailing bytes, a story mismatch, a
 * command the replay refuses, and a digest mismatch.
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
