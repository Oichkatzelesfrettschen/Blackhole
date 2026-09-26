/**
 * @file campaign_story.cpp
 * @brief Station nodes, their exact clocks, colony production, and the story
 *        events evaluated at each node.
 */

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <cstdint>
#include <numeric>
#include <optional>
#include <string>
#include <string_view>
#include <vector>

#include "game/campaign.h"
#include "game/event.h"
#include "game/observer.h"
#include "game/observer_clock.h"
#include "game/serialize_bytes.h"
#include "game/station_node.h"

namespace game {

using serial::appendF64;
using serial::appendI64;
using serial::appendString;
using serial::appendU32;
using serial::appendU64;
using serial::appendU8;

namespace {

/// Local tick of the host's clock; the host produces nothing, so the tick only
/// paces nothing and any positive value is equivalent.
constexpr std::int64_t K_HOST_TICK_SEC = 86400;

std::uint64_t splitMix64(std::uint64_t value) {
  value += 0x9E3779B97F4A7C15ULL;
  value = (value ^ (value >> 30)) * 0xBF58476D1CE4E5B9ULL;
  value = (value ^ (value >> 27)) * 0x94D049BB133111EBULL;
  return value ^ (value >> 31);
}

std::uint64_t hashName(std::string_view name) {
  std::uint64_t hash = 14695981039346656037ULL;
  for (const char character : name) {
    hash ^= static_cast<std::uint8_t>(character);
    hash *= 1099511628211ULL;
  }
  return hash;
}

bool compareHolds(std::int64_t lhs, CompareOp op, std::int64_t rhs) {
  switch (op) {
  case CompareOp::Less:
    return lhs < rhs;
  case CompareOp::LessEqual:
    return lhs <= rhs;
  case CompareOp::Equal:
    return lhs == rhs;
  case CompareOp::NotEqual:
    return lhs != rhs;
  case CompareOp::GreaterEqual:
    return lhs >= rhs;
  case CompareOp::Greater:
    return lhs > rhs;
  }
  return false;
}

std::uint64_t flagBit(std::uint32_t flag) { return std::uint64_t{1} << flag; }

std::size_t kindIndex(EmitKind kind) { return static_cast<std::size_t>(kind); }

void appendIntRef(std::vector<std::uint8_t> &out, const IntRef &ref) {
  appendI64(out, ref.plus);
  appendI64(out, ref.times);
  appendU32(out, ref.param);
}

/** @brief Index of event `id` in the id-sorted list, or nullopt. */
std::optional<std::size_t> eventIndexOf(const std::vector<EventDef> &events, std::uint32_t id) {
  const auto found = std::lower_bound(
      events.begin(), events.end(), id,
      [](const EventDef &event, std::uint32_t value) { return event.id < value; });
  if (found == events.end() || found->id != id) {
    return std::nullopt;
  }
  return static_cast<std::size_t>(found - events.begin());
}

} // namespace

void appendEventSet(std::vector<std::uint8_t> &out, const EventSet &story) {
  appendU32(out, static_cast<std::uint32_t>(story.params.size()));
  for (const EventParam &param : story.params) {
    appendString(out, param.name);
    appendI64(out, param.min);
    appendI64(out, param.max);
  }
  appendU32(out, static_cast<std::uint32_t>(story.flags.size()));
  for (const std::string &flag : story.flags) {
    appendString(out, flag);
  }
  appendU32(out, static_cast<std::uint32_t>(story.techTiers.size()));
  for (const TechLevel &level : story.techTiers) {
    appendI64(out, level.points);
    appendString(out, level.name);
  }
  appendU32(out, static_cast<std::uint32_t>(story.events.size()));
  for (const EventDef &event : story.events) {
    appendU32(out, event.id);
    appendString(out, event.name);
    appendString(out, event.text);
    appendU32(out, event.source);
    appendU8(out, static_cast<std::uint8_t>(event.mode));
    appendU8(out, static_cast<std::uint8_t>(event.category));
    appendU32(out, static_cast<std::uint32_t>(event.triggers.size()));
    for (const EventPredicate &predicate : event.triggers) {
      appendU8(out, static_cast<std::uint8_t>(predicate.kind));
      appendIntRef(out, predicate.value);
      appendU32(out, predicate.flag);
      appendU8(out, static_cast<std::uint8_t>(predicate.var));
      appendU8(out, static_cast<std::uint8_t>(predicate.op));
      appendU8(out, static_cast<std::uint8_t>(predicate.receivedKind));
      appendU32(out, predicate.receivedFrom);
      appendU8(out, predicate.silentFor ? 1U : 0U);
    }
    appendU32(out, static_cast<std::uint32_t>(event.effects.size()));
    for (const EventEffect &effect : event.effects) {
      appendU8(out, static_cast<std::uint8_t>(effect.kind));
      appendU32(out, effect.flag);
      appendU8(out, static_cast<std::uint8_t>(effect.emitKind));
      appendU32(out, effect.to);
      appendI64(out, effect.techPoints);
      appendU32(out, effect.event);
      appendIntRef(out, effect.delayTurns);
    }
  }
}

std::uint64_t eventSetDigest(const EventSet &story) {
  std::vector<std::uint8_t> bytes;
  appendEventSet(bytes, story);
  return serial::fnv1a64(bytes);
}

void CampaignState::buildNodes() {
  const auto secondsPerTurn = static_cast<std::uint64_t>(config_.secondsPerTurn);
  const auto makeNode = [&](NodeId id, double radiusCm, Observer observer,
                            std::int64_t tickSec) -> std::optional<StationNode> {
    const double rate = field_->properTimeRate(radiusCm, observer);
    if (rate <= 0.0 || rate > 1.0 || !std::isfinite(rate) || tickSec <= 0) {
      return std::nullopt;
    }
    // A rate below 2^-49 quantizes to a stopped clock; such a station is
    // refused rather than frozen.
    const std::uint64_t rateQ = quantizeClockRate(rate);
    if (rateQ == 0) {
      return std::nullopt;
    }
    StationNode node;
    node.id = id;
    node.radiusCm = radiusCm;
    node.observer = observer;
    node.clock = ObserverClock(rateQ, secondsPerTurn, tickSec);
    return node;
  };
  const std::optional<StationNode> host =
      makeNode(K_AUTHORITY_NODE, config_.authorityRadiusCm, config_.authorityObserver,
               K_HOST_TICK_SEC);
  if (!host) {
    valid_ = false;
    return;
  }
  nodes_.push_back(*host);
  for (std::size_t index = 0; index < config_.colonies.size(); ++index) {
    const ColonyConfig &colony = config_.colonies.at(index);
    if (colony.bandIndex < 0 ||
        static_cast<std::size_t>(colony.bandIndex) >= config_.bandRadiusCm.size() ||
        !field_->admitsObserver(bandRadiusCm(colony.bandIndex), colony.observer) ||
        colony.missionProperSec < 0) {
      valid_ = false;
      return;
    }
    std::optional<StationNode> node =
        makeNode(static_cast<NodeId>(K_FIRST_COLONY_NODE + index), bandRadiusCm(colony.bandIndex),
                 colony.observer, colony.localTickSec);
    if (!node) {
      valid_ = false;
      return;
    }
    node->isColony = true;
    node->colony = colony;
    nodes_.push_back(*node);
  }
  for (StationNode &node : nodes_) {
    node.received.resize(nodes_.size());
  }
}

bool CampaignState::storyWellFormed() const {
  const EventSet &story = config_.story;
  // Parameters sorted strictly by name, within the documented range.
  for (std::size_t index = 0; index < story.params.size(); ++index) {
    const EventParam &param = story.params.at(index);
    if (!withinStoryLimit(param.min, K_STORY_INT_LIMIT) ||
        !withinStoryLimit(param.max, K_STORY_INT_LIMIT) || param.max < param.min ||
        (index > 0 && !(story.params.at(index - 1).name < param.name))) {
      return false;
    }
  }
  // Events sorted strictly by id: ids are unique and lookups binary-search.
  for (std::size_t index = 1; index < story.events.size(); ++index) {
    if (!(story.events.at(index - 1).id < story.events.at(index).id)) {
      return false;
    }
  }
  // Tiers non-negative and non-decreasing; at most 64 flags.
  for (std::size_t index = 0; index < story.techTiers.size(); ++index) {
    if (story.techTiers.at(index).points < 0 ||
        (index > 0 && story.techTiers.at(index).points < story.techTiers.at(index - 1).points)) {
      return false;
    }
  }
  return story.flags.size() <= K_MAX_STORY_FLAGS;
}

bool CampaignState::intRefValid(const IntRef &ref) const {
  if (!withinStoryLimit(ref.plus, K_STORY_INT_LIMIT) ||
      !withinStoryLimit(ref.times, K_STORY_TIMES_LIMIT)) {
    return false;
  }
  if (ref.param == K_NO_PARAM) {
    return true;
  }
  return ref.param < storyParams_.size() &&
         checkedLinear(ref.times, storyParams_.at(ref.param), ref.plus).has_value();
}

void CampaignState::resolveStoryParams() {
  const EventSet &story = config_.story;
  storyParams_.clear();
  if (!storyWellFormed()) {
    valid_ = false;
    return;
  }
  for (const EventParam &param : story.params) {
    // Unsigned arithmetic: the span of any int64 range is representable
    // modulo 2^64; within the documented range it is below 2^42.
    const std::uint64_t span =
        (static_cast<std::uint64_t>(param.max) - static_cast<std::uint64_t>(param.min)) + 1U;
    const std::uint64_t draw =
        param.max == param.min ? 0U : splitMix64(config_.seed ^ hashName(param.name)) % span;
    storyParams_.push_back(
        static_cast<std::int64_t>(static_cast<std::uint64_t>(param.min) + draw));
  }
  eventFired_.assign(story.events.size(), 0);
  // Structural checks a hand-built story can fail; the loader enforces them
  // too. Nodes and flags must exist, every integer must evaluate without
  // overflow, schedule targets must exist, and every schedule delay must
  // resolve to at least one turn.
  const auto nodeOk = [this](NodeId node) { return node < nodes_.size(); };
  const auto flagOk = [&story](std::uint32_t flag) {
    return flag < K_MAX_STORY_FLAGS && flag < std::max<std::size_t>(story.flags.size(), 1);
  };
  for (const EventDef &event : story.events) {
    bool ok = nodeOk(event.source);
    for (const EventPredicate &predicate : event.triggers) {
      ok = ok && intRefValid(predicate.value) && nodeOk(predicate.receivedFrom) &&
           (predicate.kind != PredicateKind::FlagSet && predicate.kind != PredicateKind::FlagClear
                ? true
                : flagOk(predicate.flag));
    }
    for (const EventEffect &effect : event.effects) {
      ok = ok && intRefValid(effect.delayTurns);
      if (effect.kind == EffectKind::SetFlag) {
        ok = ok && flagOk(effect.flag);
      } else if (effect.kind == EffectKind::Emit) {
        ok = ok && nodeOk(effect.to) && withinStoryLimit(effect.techPoints, K_STORY_INT_LIMIT);
      } else {
        ok = ok && eventIndexOf(story.events, effect.event).has_value() &&
             resolve(effect.delayTurns) >= 1;
      }
    }
    if (!ok) {
      valid_ = false;
      return;
    }
  }
}

std::int64_t CampaignState::resolve(const IntRef &ref) const {
  if (ref.param == K_NO_PARAM) {
    return ref.plus;
  }
  // Construction verified every reference evaluates without overflow.
  return checkedLinear(ref.times, storyParams_.at(ref.param), ref.plus).value_or(0);
}

std::optional<std::int64_t> CampaignState::storyParam(std::string_view name) const {
  const std::vector<EventParam> &params = config_.story.params;
  for (std::size_t index = 0; index < params.size() && index < storyParams_.size(); ++index) {
    if (params.at(index).name == name) {
      return storyParams_.at(index);
    }
  }
  return std::nullopt;
}

std::int64_t CampaignState::techTier(NodeId node) const {
  if (node >= nodes_.size()) {
    return 0;
  }
  const std::int64_t points = nodes_.at(node).techPoints;
  return std::ranges::count_if(config_.story.techTiers,
                               [points](const TechLevel &level) { return level.points <= points; });
}

std::int64_t CampaignState::colonyTechTier() const {
  std::int64_t best = 0;
  for (const StationNode &node : nodes_) {
    if (node.isColony) {
      best = std::max(best, techTier(node.id));
    }
  }
  return best;
}

double CampaignState::nodeDelaySec(NodeId from, NodeId to) const {
  const double fromCm = nodes_.at(from).radiusCm;
  const double toCm = nodes_.at(to).radiusCm;
  // Story signals are light between stations: the geodesic delay, with none
  // of the fleet network's coordination overhead.
  return fromCm == toCm ? 0.0 : field_->signalDelaySec(fromCm, toCm);
}

std::int64_t CampaignState::nodeDelayTurns(NodeId from, NodeId to) const {
  return clock_.ceilTurns(nodeDelaySec(from, to));
}

void CampaignState::emitNodeDelivery(DeliveryKind kind, const StationNode &sender,
                                     NodeId destination, EventCategory category,
                                     std::uint32_t payloadIndex, std::int64_t techPoints,
                                     double yieldUnits) {
  Delivery delivery;
  delivery.kind = kind;
  delivery.emitTurn = clock_.turn();
  // Quantized once, here: ceil never lands a signal before light could.
  delivery.effectTurn = clock_.turn() + nodeDelayTurns(sender.id, destination);
  delivery.sequence = nextSequence_++;
  delivery.sender = sender.id;
  delivery.destination = destination;
  delivery.senderProperSecAtEmit = sender.clock.properSec();
  delivery.senderEnergyUnitsAtEmit = sender.id == K_AUTHORITY_NODE ? energyUnits_ : 0.0;
  delivery.senderTechPointsAtEmit = sender.techPoints;
  delivery.payloadIndex = payloadIndex;
  delivery.techPoints = techPoints;
  delivery.category = category;
  delivery.yieldUnits = yieldUnits;
  deliveryQueue_.push_back(delivery);
}

void CampaignState::advanceNodeClocks() {
  for (StationNode &node : nodes_) {
    const std::int64_t crossed = node.clock.advance();
    if (!node.isColony || node.dark()) {
      continue;
    }
    // Production runs on the colony's own clock: one shipment per local tick
    // inside the mission window, aggregated into one report per turn.
    std::int64_t productive = crossed;
    if (node.colony.missionProperSec > 0) {
      const std::int64_t missionTicks = node.colony.missionProperSec / node.clock.localTickSec();
      const std::int64_t after = node.clock.ticks();
      productive = std::max<std::int64_t>(
          0, std::min(after, missionTicks) - std::min(after - crossed, missionTicks));
    }
    if (productive > 0 && node.colony.energyPerTick > 0.0) {
      emitNodeDelivery(DeliveryKind::ColonyReport, node, K_AUTHORITY_NODE, EventCategory::Info,
                       0, 0, static_cast<double>(productive) * node.colony.energyPerTick);
    }
    if (node.colony.missionProperSec > 0 &&
        node.clock.properSec() >= node.colony.missionProperSec) {
      // The mission window closes on the colony's clock: it falls silent.
      node.flags |= flagBit(K_DARK_FLAG);
    }
  }
}

void CampaignState::receiveNodeDelivery(const Delivery &delivery) {
  StationNode &destination = nodes_.at(delivery.destination);
  if (destination.dark()) {
    return; // nobody is there to receive it
  }
  const EmitKind kind =
      delivery.kind == DeliveryKind::TechPacket ? EmitKind::TechPacket : EmitKind::Notice;
  ReceivedFromNode &received = destination.received.at(delivery.sender);
  received.lastArrivalTurn.at(kindIndex(kind)) = clock_.turn();
  ++received.count.at(kindIndex(kind));
  noteSenderStamp(delivery);
  if (kind == EmitKind::TechPacket) {
    destination.techPoints += delivery.techPoints;
  }
  ArrivalRecord record;
  record.kind = kind;
  record.category = delivery.category;
  record.sender = delivery.sender;
  record.destination = delivery.destination;
  record.emitTurn = delivery.emitTurn;
  record.arrivalTurn = clock_.turn();
  record.senderProperSecAtEmit = delivery.senderProperSecAtEmit;
  record.senderEnergyUnitsAtEmit = delivery.senderEnergyUnitsAtEmit;
  record.senderTechPointsAtEmit = delivery.senderTechPointsAtEmit;
  record.payloadIndex = delivery.payloadIndex;
  record.techPoints = delivery.techPoints;
  arrivals_.push_back(record);
}

void CampaignState::noteSenderStamp(const Delivery &delivery) {
  ReceivedFromNode &received = nodes_.at(delivery.destination).received.at(delivery.sender);
  if (delivery.emitTurn < received.lastEmitTurn) {
    return; // an older emission that took longer: it says nothing newer
  }
  received.lastEmitTurn = delivery.emitTurn;
  received.lastSenderProperSec = delivery.senderProperSecAtEmit;
  received.lastSenderTechPoints = delivery.senderTechPointsAtEmit;
  received.lastSenderEnergyUnits = delivery.senderEnergyUnitsAtEmit;
}

bool CampaignState::predicateHolds(const EventPredicate &predicate, const StationNode &node) const {
  switch (predicate.kind) {
  case PredicateKind::TurnAtLeast:
    return clock_.turn() >= resolve(predicate.value);
  case PredicateKind::FlagSet:
    return (node.flags & flagBit(predicate.flag)) != 0;
  case PredicateKind::FlagClear:
    return (node.flags & flagBit(predicate.flag)) == 0;
  case PredicateKind::Compare: {
    std::int64_t lhs = 0;
    switch (predicate.var) {
    case CompareVar::TechPoints:
      lhs = node.techPoints;
      break;
    case CompareVar::TechTier:
      lhs = techTier(node.id);
      break;
    case CompareVar::PacketsReceived:
    case CompareVar::NoticesReceived: {
      const EmitKind kind = predicate.var == CompareVar::PacketsReceived ? EmitKind::TechPacket
                                                                         : EmitKind::Notice;
      lhs = std::accumulate(node.received.begin(), node.received.end(), std::int64_t{0},
                            [kind](std::int64_t sum, const ReceivedFromNode &received) {
                              return sum + received.count.at(kindIndex(kind));
                            });
      break;
    }
    }
    return compareHolds(lhs, predicate.op, resolve(predicate.value));
  }
  case PredicateKind::Received: {
    const std::int64_t last =
        node.received.at(predicate.receivedFrom).lastArrivalTurn.at(kindIndex(predicate.receivedKind));
    if (last < 0) {
      return false;
    }
    return !predicate.silentFor || clock_.turn() - last >= resolve(predicate.value);
  }
  }
  return false;
}

void CampaignState::applyEffect(const EventEffect &effect, const EventDef &event,
                                StationNode &node) {
  switch (effect.kind) {
  case EffectKind::SetFlag:
    node.flags |= flagBit(effect.flag);
    break;
  case EffectKind::Emit:
    if (node.dark()) {
      break; // a node that has gone dark emits nothing further
    }
    if (effect.emitKind == EmitKind::TechPacket) {
      const auto ordinal = static_cast<std::uint32_t>(node.packetsEmitted++);
      emitNodeDelivery(DeliveryKind::TechPacket, node, effect.to, EventCategory::Tech, ordinal,
                       effect.techPoints, 0.0);
    } else {
      emitNodeDelivery(DeliveryKind::EventNotice, node, effect.to, event.category, event.id, 0,
                       0.0);
    }
    break;
  case EffectKind::Schedule: {
    // Construction verified every schedule target, so the lookup succeeds.
    const std::optional<std::size_t> target = eventIndexOf(config_.story.events, effect.event);
    if (!target.has_value()) {
      break;
    }
    scheduledEvents_.push_back({.turn = clock_.turn() + resolve(effect.delayTurns),
                                .eventIndex = static_cast<std::uint32_t>(target.value())});
    break;
  }
  }
}

void CampaignState::evaluateStory() {
  const std::vector<EventDef> &events = config_.story.events;
  if (events.empty()) {
    return;
  }
  const std::int64_t now = clock_.turn();
  // Each due schedule entry is one occurrence: an event scheduled twice for
  // this turn runs twice.
  std::vector<std::uint32_t> occurrences(events.size(), 0);
  for (const ScheduledEvent &scheduled : scheduledEvents_) {
    if (scheduled.turn <= now) {
      ++occurrences.at(scheduled.eventIndex);
    }
  }
  std::erase_if(scheduledEvents_,
                [now](const ScheduledEvent &scheduled) { return scheduled.turn <= now; });
  for (std::size_t index = 0; index < events.size(); ++index) {
    const EventDef &event = events.at(index);
    std::uint32_t runs = occurrences.at(index);
    if (event.mode == EventMode::Once) {
      runs = eventFired_.at(index) == 0 ? 1U : 0U;
    }
    for (std::uint32_t run = 0; run < runs; ++run) {
      fireIfTriggered(index);
    }
  }
}

void CampaignState::fireIfTriggered(std::size_t eventIndex) {
  const EventDef &event = config_.story.events.at(eventIndex);
  StationNode &node = nodes_.at(event.source);
  if (node.dark() || !std::ranges::all_of(event.triggers, [&](const EventPredicate &predicate) {
        return predicateHolds(predicate, node);
      })) {
    return;
  }
  if (event.mode == EventMode::Once) {
    eventFired_.at(eventIndex) = 1;
  }
  for (const EventEffect &effect : event.effects) {
    applyEffect(effect, event, node);
  }
}

void CampaignState::appendStoryState(std::vector<std::uint8_t> &out) const {
  appendI64(out, config_.victoryTechTier);
  appendU32(out, static_cast<std::uint32_t>(config_.colonies.size()));
  for (const ColonyConfig &colony : config_.colonies) {
    appendU32(out, static_cast<std::uint32_t>(colony.bandIndex));
    appendU8(out, static_cast<std::uint8_t>(colony.observer));
    appendI64(out, colony.localTickSec);
    appendF64(out, colony.energyPerTick);
    appendI64(out, colony.missionProperSec);
  }
  appendEventSet(out, config_.story);
  appendU32(out, static_cast<std::uint32_t>(storyParams_.size()));
  for (const std::int64_t value : storyParams_) {
    appendI64(out, value);
  }
  appendU32(out, static_cast<std::uint32_t>(nodes_.size()));
  for (const StationNode &node : nodes_) {
    appendU32(out, node.id);
    appendF64(out, node.radiusCm);
    appendU8(out, static_cast<std::uint8_t>(node.observer));
    appendU64(out, node.clock.rateQ());
    appendI64(out, node.clock.properSec());
    appendU64(out, node.clock.fractionQ());
    appendI64(out, node.clock.localTickSec());
    appendU64(out, node.flags);
    appendI64(out, node.techPoints);
    appendI64(out, node.packetsEmitted);
    for (const ReceivedFromNode &received : node.received) {
      for (std::size_t kind = 0; kind < received.count.size(); ++kind) {
        appendI64(out, received.lastArrivalTurn.at(kind));
        appendI64(out, received.count.at(kind));
      }
      appendI64(out, received.lastEmitTurn);
      appendI64(out, received.lastSenderProperSec);
      appendI64(out, received.lastSenderTechPoints);
      appendF64(out, received.lastSenderEnergyUnits);
    }
  }
  appendU32(out, static_cast<std::uint32_t>(eventFired_.size()));
  for (const std::uint8_t fired : eventFired_) {
    appendU8(out, fired);
  }
  appendU32(out, static_cast<std::uint32_t>(scheduledEvents_.size()));
  for (const ScheduledEvent &scheduled : scheduledEvents_) {
    appendI64(out, scheduled.turn);
    appendU32(out, scheduled.eventIndex);
  }
  appendU32(out, static_cast<std::uint32_t>(arrivals_.size()));
  for (const ArrivalRecord &arrival : arrivals_) {
    appendU8(out, static_cast<std::uint8_t>(arrival.kind));
    appendU8(out, static_cast<std::uint8_t>(arrival.category));
    appendU32(out, arrival.sender);
    appendU32(out, arrival.destination);
    appendI64(out, arrival.emitTurn);
    appendI64(out, arrival.arrivalTurn);
    appendI64(out, arrival.senderProperSecAtEmit);
    appendF64(out, arrival.senderEnergyUnitsAtEmit);
    appendI64(out, arrival.senderTechPointsAtEmit);
    appendU32(out, arrival.payloadIndex);
    appendI64(out, arrival.techPoints);
  }
  appendF64(out, energyLostToDarkness_);
}

} // namespace game
