/**
 * @file save_format.cpp
 * @brief Versioned replay save implementation.
 */

#include "game/save_format.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <numeric>
#include <string>
#include <utility>
#include <vector>

#include "game/campaign.h"
#include "game/campaign_session.h"
#include "game/command.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/observer.h"
#include "game/realtime_driver.h"
#include "game/serialize_bytes.h"
#include "game/station_node.h"

namespace game {

namespace {

constexpr std::array<std::uint8_t, 4> K_MAGIC = {'B', 'H', 'S', 'V'};

constexpr std::uint32_t tag(char a, char b, char c, char d) {
  return static_cast<std::uint32_t>(static_cast<std::uint8_t>(a)) |
         (static_cast<std::uint32_t>(static_cast<std::uint8_t>(b)) << 8) |
         (static_cast<std::uint32_t>(static_cast<std::uint8_t>(c)) << 16) |
         (static_cast<std::uint32_t>(static_cast<std::uint8_t>(d)) << 24);
}

constexpr std::uint32_t K_TAG_HEAD = tag('H', 'E', 'A', 'D');
constexpr std::uint32_t K_TAG_CMDS = tag('C', 'M', 'D', 'S');
constexpr std::uint32_t K_TAG_TURN = tag('T', 'U', 'R', 'N');
constexpr std::uint32_t K_TAG_DGST = tag('D', 'G', 'S', 'T');

void appendSection(std::vector<std::uint8_t> &out, std::uint32_t sectionTag,
                   const std::vector<std::uint8_t> &body) {
  serial::appendU32(out, sectionTag);
  serial::appendU32(out, static_cast<std::uint32_t>(body.size()));
  out.insert(out.end(), body.begin(), body.end());
}

struct SaveHeader {
  CampaignScenario scenario = CampaignScenario::M87Default;
  std::uint64_t seed = 0;
  double spin = 0.0;
  std::int32_t colonyBand = -1;
  std::uint64_t storyDigest = 0;
};

struct SavedCommand {
  std::int64_t issueTurn = 0;
  Command command{};
};

/** @brief Reads one section's framing and returns a reader over its body. */
bool openSection(serial::ByteReader &reader, const std::vector<std::uint8_t> &bytes,
                 std::uint32_t expectedTag, serial::ByteReader &body, std::string &error) {
  std::uint32_t sectionTag = 0;
  std::uint32_t length = 0;
  if (!reader.readU32(sectionTag) || !reader.readU32(length)) {
    error = "truncated section header";
    return false;
  }
  if (sectionTag != expectedTag) {
    error = "unexpected section tag";
    return false;
  }
  if (length > reader.remaining()) {
    error = "section longer than the save";
    return false;
  }
  body = serial::ByteReader(bytes.data() + reader.offset(), length);
  return reader.skip(length);
}

bool closeSection(const serial::ByteReader &body, std::string &error) {
  if (!body.ok()) {
    error = "truncated section body";
    return false;
  }
  if (body.remaining() != 0) {
    error = "section length disagrees with its body";
    return false;
  }
  return true;
}

bool readHeader(serial::ByteReader &body, SaveHeader &header) {
  std::uint8_t scenario = 0;
  const bool ok = body.readU8(scenario) && body.readU64(header.seed) && body.readF64(header.spin) &&
                  body.readI32(header.colonyBand) && body.readU64(header.storyDigest);
  if (!ok || scenario > static_cast<std::uint8_t>(CampaignScenario::GargantuaColony)) {
    return false;
  }
  header.scenario = static_cast<CampaignScenario>(scenario);
  return true;
}

bool readCommand(serial::ByteReader &body, SavedCommand &saved) {
  std::uint8_t type = 0;
  std::uint8_t lane = 0;
  std::uint8_t station = 0;
  std::int32_t targetBand = 0;
  Command &command = saved.command;
  const bool ok = body.readI64(saved.issueTurn) && body.readU8(type) &&
                  body.readU32(command.fleet) && body.readI32(targetBand) && body.readU8(lane) &&
                  body.readU8(station) && body.readF64(command.properTimeCostSec) &&
                  body.readU32(command.originNode);
  if (!ok || type > static_cast<std::uint8_t>(CommandType::AssignTask) ||
      lane > static_cast<std::uint8_t>(OrbitLane::Retrograde) ||
      station > static_cast<std::uint8_t>(StationKeeping::Hover) || saved.issueTurn < 0) {
    return false;
  }
  command.type = static_cast<CommandType>(type);
  command.targetBand = targetBand;
  command.lane = static_cast<OrbitLane>(lane);
  command.station = static_cast<StationKeeping>(station);
  return true;
}

std::unique_ptr<CampaignSession> constructSession(const SaveHeader &header,
                                                  const EventSet *story, std::string &error) {
  switch (header.scenario) {
  case CampaignScenario::M87Default:
    return std::make_unique<CampaignSession>(header.seed, header.spin);
  case CampaignScenario::GargantuaCanon:
    return std::make_unique<CampaignSession>(header.seed, CampaignScenario::GargantuaCanon);
  case CampaignScenario::GargantuaColony:
    if (story == nullptr || eventSetDigest(*story) != header.storyDigest) {
      error = "the supplied story is not the one this save was made with";
      return nullptr;
    }
    return std::make_unique<CampaignSession>(header.seed, *story, header.colonyBand);
  }
  error = "unknown scenario";
  return nullptr;
}

/** @brief Builds the saved scenario and requires it to reproduce every header
 *         field, so a flipped header bit is refused rather than ignored. */
std::unique_ptr<CampaignSession> buildSession(const SaveHeader &header, const EventSet *story,
                                              std::string &error) {
  std::unique_ptr<CampaignSession> session = constructSession(header, story, error);
  if (!session) {
    return nullptr;
  }
  const std::uint64_t digest = session->scenario() == CampaignScenario::GargantuaColony
                                   ? eventSetDigest(session->state().config().story)
                                   : 0U;
  if (session->field().spinDimensionless() != header.spin ||
      session->colonyBand() != header.colonyBand || digest != header.storyDigest) {
    error = "the header does not match the scenario it names";
    return nullptr;
  }
  return session;
}

/** @brief Commands sorted by issue turn, each within [0, turn]: the replay
 *         then issues every one of them on its own turn. */
bool commandsWithinTurn(const std::vector<SavedCommand> &commands, std::int64_t turn) {
  std::int64_t previous = 0;
  return std::ranges::all_of(commands, [&previous, turn](const SavedCommand &saved) {
    const bool inOrder = saved.issueTurn >= previous && saved.issueTurn <= turn;
    previous = saved.issueTurn;
    return inOrder;
  });
}

} // namespace

std::int64_t saveReplayTurnBudget(const CampaignState &state) {
  const std::vector<StationNode> &nodes = state.nodes();
  const double slowestRate =
      std::accumulate(nodes.begin(), nodes.end(), 1.0, [](double slowest, const StationNode &node) {
        return std::min(slowest, node.clock.rate());
      });
  const double realtimeTurnsPerWallSec =
      K_MAX_LOCAL_SECONDS_PER_WALL_SECOND / (slowestRate * state.config().secondsPerTurn);
  const double manualTurnsPerWallSec =
      static_cast<double>(K_MAX_MANUAL_BATCH_TURNS) * K_SAVE_MANUAL_BATCHES_PER_WALL_SEC;
  return static_cast<std::int64_t>(std::ceil(
      K_SAVE_SESSION_WALL_SEC * std::max(realtimeTurnsPerWallSec, manualTurnsPerWallSec)));
}

std::vector<std::uint8_t> saveCampaign(const CampaignSession &session) {
  const CampaignState &state = session.state();
  std::vector<std::uint8_t> out(K_MAGIC.begin(), K_MAGIC.end());
  serial::appendU32(out, K_SAVE_FORMAT_VERSION);

  std::vector<std::uint8_t> head;
  serial::appendU8(head, static_cast<std::uint8_t>(session.scenario()));
  serial::appendU64(head, session.seed());
  serial::appendF64(head, session.field().spinDimensionless());
  serial::appendI32(head, session.colonyBand());
  serial::appendU64(head, session.scenario() == CampaignScenario::GargantuaColony
                              ? eventSetDigest(state.config().story)
                              : 0U);
  appendSection(out, K_TAG_HEAD, head);

  std::vector<std::uint8_t> commands;
  serial::appendU32(commands, static_cast<std::uint32_t>(state.commandLog().size()));
  for (const LoggedCommand &logged : state.commandLog()) {
    serial::appendI64(commands, logged.issueTurn);
    serial::appendU8(commands, static_cast<std::uint8_t>(logged.command.type));
    serial::appendU32(commands, logged.command.fleet);
    serial::appendI32(commands, logged.command.targetBand);
    serial::appendU8(commands, static_cast<std::uint8_t>(logged.command.lane));
    serial::appendU8(commands, static_cast<std::uint8_t>(logged.command.station));
    serial::appendF64(commands, logged.command.properTimeCostSec);
    serial::appendU32(commands, logged.command.originNode);
  }
  appendSection(out, K_TAG_CMDS, commands);

  std::vector<std::uint8_t> turn;
  serial::appendI64(turn, state.turn());
  appendSection(out, K_TAG_TURN, turn);

  std::vector<std::uint8_t> digest;
  serial::appendU64(digest, state.stateDigest());
  appendSection(out, K_TAG_DGST, digest);
  return out;
}

CampaignLoadResult loadCampaign(const std::vector<std::uint8_t> &bytes, const EventSet *story) {
  CampaignLoadResult result;
  serial::ByteReader reader(bytes.data(), bytes.size());
  std::array<std::uint8_t, 4> magic{};
  for (std::uint8_t &byte : magic) {
    static_cast<void>(reader.readU8(byte));
  }
  std::uint32_t version = 0;
  if (!reader.readU32(version) || magic != K_MAGIC) {
    result.error = "not a campaign save";
    return result;
  }
  if (version != K_SAVE_FORMAT_VERSION) {
    result.error = "unknown save format version " + std::to_string(version);
    return result;
  }

  serial::ByteReader body(nullptr, 0);
  SaveHeader header;
  if (!openSection(reader, bytes, K_TAG_HEAD, body, result.error)) {
    return result;
  }
  if (!readHeader(body, header)) {
    result.error = "malformed header";
    return result;
  }
  if (!closeSection(body, result.error)) {
    return result;
  }

  std::vector<SavedCommand> commands;
  if (!openSection(reader, bytes, K_TAG_CMDS, body, result.error)) {
    return result;
  }
  std::uint32_t commandCount = 0;
  static_cast<void>(body.readU32(commandCount));
  for (std::uint32_t index = 0; index < commandCount && body.ok(); ++index) {
    SavedCommand saved;
    if (!readCommand(body, saved)) {
      result.error = "malformed command";
      return result;
    }
    commands.push_back(saved);
  }
  if (!closeSection(body, result.error)) {
    return result;
  }

  std::int64_t turn = 0;
  if (!openSection(reader, bytes, K_TAG_TURN, body, result.error)) {
    return result;
  }
  static_cast<void>(body.readI64(turn));
  if (!closeSection(body, result.error)) {
    return result;
  }
  std::uint64_t savedDigest = 0;
  if (!openSection(reader, bytes, K_TAG_DGST, body, result.error)) {
    return result;
  }
  static_cast<void>(body.readU64(savedDigest));
  if (!closeSection(body, result.error)) {
    return result;
  }
  if (!reader.ok() || reader.remaining() != 0) {
    result.error = "trailing bytes after the last section";
    return result;
  }
  std::unique_ptr<CampaignSession> session = buildSession(header, story, result.error);
  if (!session) {
    return result;
  }
  CampaignState &state = session->state();
  if (!state.valid()) {
    result.error = "the saved scenario does not build a valid campaign";
    return result;
  }
  // Both refusals come before the first replayed turn, so a corrupted turn
  // field or command log costs no replay work.
  const std::int64_t budget = saveReplayTurnBudget(state);
  if (turn < 0 || turn > budget) {
    result.error =
        "saved turn outside [0, " + std::to_string(budget) + "], this scenario's replay budget";
    return result;
  }
  if (!commandsWithinTurn(commands, turn)) {
    result.error = "saved commands are out of turn order or beyond the saved turn";
    return result;
  }
  // Replay: every command on its issue turn, in log order, then the turn's
  // advance -- the same sequence the original session saw.
  std::size_t next = 0;
  for (std::int64_t current = 0; current <= turn; ++current) {
    for (; next < commands.size() && commands.at(next).issueTurn == current; ++next) {
      if (!state.issueCommand(commands.at(next).command)) {
        result.error = "the replay refused a saved command";
        return result;
      }
    }
    if (current < turn) {
      state.advanceTurn();
    }
  }
  if (state.stateDigest() != savedDigest) {
    result.error = "replay digest differs from the saved digest";
    return result;
  }
  result.session = std::move(session);
  return result;
}

} // namespace game
