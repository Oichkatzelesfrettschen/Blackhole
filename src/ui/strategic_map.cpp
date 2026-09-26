/**
 * @file strategic_map.cpp
 * @brief ImDrawList orbital map implementation.
 */

#include "ui/strategic_map.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
#include <numbers>
#include <numeric>
#include <string>
#include <vector>

#include <imgui.h>

#include "game/campaign_view.h"
#include "game/event.h"
#include "game/fleet.h"
#include "game/station_node.h"
#include "ui/campaign_panels.h"

namespace ui {

namespace {

constexpr double K_SECONDS_PER_DAY = 86400.0;
// Golden angle spreads fleet markers around their band ring without any
// stored azimuth: the angle is a pure function of the stable fleet id, so
// markers never jump between frames or runs.
constexpr float K_GOLDEN_ANGLE_RAD = 2.399963f;
constexpr float K_CORE_FRACTION = 0.10f; ///< Horizon core radius as a fraction of map radius.
constexpr float K_HIT_RADIUS_PX = 14.0f;

struct MapScale {
  ImVec2 center;
  float maxRadiusPx = 0.0f;
  double rMinCm = 1.0;
  double rMaxCm = 10.0;

  [[nodiscard]] float pixelRadius(double radiusCm) const {
    const double clamped = std::clamp(radiusCm, rMinCm, rMaxCm);
    const double normalized = std::log(clamped / rMinCm) / std::log(rMaxCm / rMinCm);
    return maxRadiusPx * (K_CORE_FRACTION + ((1.0f - K_CORE_FRACTION) * static_cast<float>(normalized)));
  }
};

ImVec2 ringPoint(const MapScale &scale, double radiusCm, float angleRad) {
  const float radiusPx = scale.pixelRadius(radiusCm);
  return {scale.center.x + (radiusPx * std::cos(angleRad)),
          scale.center.y + (radiusPx * std::sin(angleRad))};
}

float fleetAngleRad(game::FleetId fleetId) {
  return -1.5707963f + (static_cast<float>(fleetId) * K_GOLDEN_ANGLE_RAD);
}

ImU32 rateColor(double properTimeRate) {
  // Slow local clocks render hot (red), fast ones calm (green): the map IS
  // the time-dilation field.
  const float t = static_cast<float>(std::clamp(properTimeRate, 0.0, 1.0));
  return IM_COL32(static_cast<int>((230.0f * (1.0f - t)) + (60.0f * t)),
                  static_cast<int>((60.0f * (1.0f - t)) + (200.0f * t)), 70, 255);
}

float signalProgress(std::int64_t nowTurn, std::int64_t fromTurn, std::int64_t untilTurn) {
  if (untilTurn <= fromTurn) {
    return 1.0f;
  }
  const float fraction = static_cast<float>(nowTurn - fromTurn) /
                         static_cast<float>(untilTurn - fromTurn);
  return std::clamp(fraction, 0.0f, 1.0f);
}

ImVec2 lerp(const ImVec2 &a, const ImVec2 &b, float t) {
  return {a.x + ((b.x - a.x) * t), a.y + ((b.y - a.y) * t)};
}

// A deterministic starfield behind the map: star positions and brightness are
// pure functions of the star index (an integer hash), so the field is stable
// across frames and runs without storing anything. A couple of dim nebula
// washes tint the dark. This is procedural art -- no texture, no RAM cost.
void drawStarfield(ImDrawList *drawList, const ImVec2 &origin, const ImVec2 &size) {
  drawList->AddRectFilled(origin, {origin.x + size.x, origin.y + size.y},
                          IM_COL32(6, 8, 16, 255));
  // Two broad nebula washes (layered translucent fills approximate a glow).
  const ImVec2 nebulaA = {origin.x + (size.x * 0.30f), origin.y + (size.y * 0.28f)};
  const ImVec2 nebulaB = {origin.x + (size.x * 0.72f), origin.y + (size.y * 0.70f)};
  const float nebulaR = std::min(size.x, size.y) * 0.45f;
  for (int layer = 0; layer < 4; ++layer) {
    const float radius = nebulaR * (1.0f - (0.18f * static_cast<float>(layer)));
    drawList->AddCircleFilled(nebulaA, radius, IM_COL32(40, 30, 80, 10), 48);
    drawList->AddCircleFilled(nebulaB, radius, IM_COL32(20, 45, 70, 9), 48);
  }
  for (int star = 0; star < 170; ++star) {
    const std::uint32_t hx = (static_cast<std::uint32_t>(star) * 2654435761U) ^ 0x9E3779B9U;
    const std::uint32_t hy = (static_cast<std::uint32_t>(star) * 40503U) ^ 0x85EBCA6BU;
    const std::uint32_t hb = (static_cast<std::uint32_t>(star) * 2246822519U) ^ 0xC2B2AE35U;
    const float x = origin.x + ((static_cast<float>(hx % 1000U) / 1000.0f) * size.x);
    const float y = origin.y + ((static_cast<float>(hy % 1000U) / 1000.0f) * size.y);
    const int brightness = 90 + static_cast<int>(hb % 150U);
    const float radius = (hb % 17U) == 0U ? 1.6f : 0.8f; // a few brighter stars
    drawList->AddCircleFilled({x, y}, radius, IM_COL32(brightness, brightness, brightness + 20, 255),
                              6);
  }
}

// The map background: a vendored NASA nebula texture when present (darkened by
// a translucent overlay so rings and labels stay legible), the procedural
// starfield otherwise.
void drawMapBackdrop(ImDrawList *drawList, const ImVec2 &origin, const ImVec2 &size,
                     unsigned int backdropTextureId) {
  if (backdropTextureId == 0) {
    drawStarfield(drawList, origin, size);
    return;
  }
  const ImVec2 canvasEnd = {origin.x + size.x, origin.y + size.y};
  drawList->AddImage(static_cast<ImTextureID>(backdropTextureId), origin, canvasEnd);
  drawList->AddRectFilled(origin, canvasEnd, IM_COL32(4, 6, 12, 150));
}

// A soft additive halo: concentric translucent circles fading outward fake the
// bloom the vector map cannot get from the renderer's post pipeline.
void drawGlow(ImDrawList *drawList, const ImVec2 &center, float radiusPx, ImU32 color) {
  for (int ring = 0; ring < 3; ++ring) {
    const float radius = radiusPx + (2.0f * static_cast<float>(ring));
    const int alpha = 60 - (18 * ring);
    drawList->AddCircle(center, radius, (color & 0x00FFFFFFU) | (static_cast<ImU32>(alpha) << 24),
                        24, 2.0f);
  }
}

// Frame-dragging sense: a short counter-clockwise arc with a dot at its head,
// drawn near the core, showing which way inertial frames are swept (prograde).
void drawFrameDragArc(ImDrawList *drawList, const ImVec2 &center, float corePx) {
  const float arcPx = corePx * 1.5f;
  const int segments = 24;
  ImVec2 previous = {center.x + arcPx, center.y};
  for (int step = 1; step <= segments; ++step) {
    const float angle = -1.4f * (static_cast<float>(step) / static_cast<float>(segments));
    const ImVec2 point = {center.x + (arcPx * std::cos(angle)),
                          center.y + (arcPx * std::sin(angle))};
    drawList->AddLine(previous, point, IM_COL32(120, 200, 255, 200), 2.0f);
    previous = point;
  }
  drawList->AddCircleFilled(previous, 3.0f, IM_COL32(120, 200, 255, 255), 8);
}

// A small vector icon per capability, drawn at the marker instead of a letter:
// extraction a downward drill triangle, research a lens, fabrication a frame,
// relay a dish, verification a check. All ImDrawList primitives -- procedural,
// no sprite sheet.
void drawCapabilityIcon(ImDrawList *drawList, const ImVec2 &center, game::FleetCapability capability,
                        ImU32 color) {
  const float s = 4.5f;
  switch (capability) {
  case game::FleetCapability::Extraction:
    drawList->AddTriangleFilled({center.x - s, center.y - s}, {center.x + s, center.y - s},
                                {center.x, center.y + s}, color);
    break;
  case game::FleetCapability::Research:
    drawList->AddCircle({center.x - 1.0f, center.y - 1.0f}, s * 0.8f, color, 12, 1.5f);
    drawList->AddLine({center.x + (s * 0.3f), center.y + (s * 0.3f)}, {center.x + s, center.y + s},
                      color, 1.5f);
    break;
  case game::FleetCapability::Fabrication:
    drawList->AddRect({center.x - s, center.y - s}, {center.x + s, center.y + s}, color, 0.0f, 0,
                      1.5f);
    break;
  case game::FleetCapability::Relay:
    drawList->PathArcTo(center, s, 0.0f, std::numbers::pi_v<float>, 12);
    drawList->PathStroke(color, 0, 1.5f);
    drawList->AddCircleFilled(center, 1.3f, color, 6);
    break;
  case game::FleetCapability::Verification:
    drawList->AddLine({center.x - s, center.y}, {center.x - (s * 0.2f), center.y + s}, color, 1.5f);
    drawList->AddLine({center.x - (s * 0.2f), center.y + s}, {center.x + s, center.y - s}, color,
                      1.5f);
    break;
  }
}

// Orbital band rings coloured by proper-time rate with a soft glow; invalid
// bands draw as hazard without glow, ergoregion bands amber and prograde-only.
void drawOrbitalBands(ImDrawList *drawList, const MapScale &scale,
                      const game::CampaignViewSnapshot &view) {
  for (const game::BandView &band : view.bands) {
    std::string label;
    const float bandPx = scale.pixelRadius(band.radiusCm);
    ImU32 ringColor = IM_COL32(120, 30, 30, 180);
    float thickness = 1.0f;
    if (band.validStation && band.insideErgosphere) {
      ringColor = IM_COL32(210, 150, 60, 230);
      thickness = 2.0f;
      label = std::format("band {}  dtau/dt {:.4g}  omega {:.2e}  PROGRADE ONLY", band.index,
                          band.properTimeRate, band.frameDragRateRadPerSec);
    } else if (band.validStation) {
      ringColor = rateColor(band.properTimeRate);
      thickness = 1.5f;
      label = std::format("band {}  dtau/dt {:.4g}  delay {:.1f} d", band.index,
                          band.properTimeRate, band.delayToAuthoritySec / K_SECONDS_PER_DAY);
    } else {
      label = std::format("band {}  FORBIDDEN", band.index);
    }
    if (band.validStation) {
      drawGlow(drawList, scale.center, bandPx, ringColor);
    }
    drawList->AddCircle(scale.center, bandPx, ringColor, 96, thickness);
    drawList->AddText(
        {scale.center.x + (bandPx * 0.7071f) + 6.0f, scale.center.y - (bandPx * 0.7071f) - 6.0f},
        IM_COL32(200, 200, 210, 255), label.c_str());
  }
}

// A compact always-visible legend in the map's bottom-left corner: each
// capability icon beside its name, on a translucent panel.
void drawMapLegend(ImDrawList *drawList, const ImVec2 &canvasOrigin, const ImVec2 &canvasSize) {
  struct Entry {
    game::FleetCapability capability;
    const char *label;
  };
  const Entry entries[] = {
      {.capability = game::FleetCapability::Extraction, .label = "extraction"},
      {.capability = game::FleetCapability::Research, .label = "research"},
      {.capability = game::FleetCapability::Fabrication, .label = "fabrication"},
      {.capability = game::FleetCapability::Relay, .label = "relay"},
      {.capability = game::FleetCapability::Verification, .label = "verification"},
  };
  const float rowH = 15.0f;
  const float boxH = (rowH * 5.0f) + 8.0f;
  const ImVec2 boxMin = {canvasOrigin.x + 6.0f, canvasOrigin.y + canvasSize.y - boxH - 6.0f};
  const ImVec2 boxMax = {boxMin.x + 118.0f, boxMin.y + boxH};
  drawList->AddRectFilled(boxMin, boxMax, IM_COL32(6, 8, 16, 190), 3.0f);
  drawList->AddRect(boxMin, boxMax, IM_COL32(80, 90, 110, 180), 3.0f);
  float rowY = boxMin.y + 4.0f + (rowH * 0.5f);
  for (const Entry &entry : entries) {
    drawCapabilityIcon(drawList, {boxMin.x + 12.0f, rowY}, entry.capability,
                       IM_COL32(220, 220, 230, 255));
    drawList->AddText({boxMin.x + 24.0f, rowY - 7.0f}, IM_COL32(210, 210, 220, 255), entry.label);
    rowY += rowH;
  }
}

/** @brief A station marker's label: "(you)" for the viewer's own station;
 *         any other with the age of its latest arrival here. */
std::string remoteLabel(const game::CampaignViewSnapshot &view, const game::NodeView &node,
                        const char *name) {
  if (node.id == view.perceivedBy) {
    return std::format("{} (you)", name);
  }
  if (!node.heard) {
    return std::format("{} (never heard)", name);
  }
  const double ageDays =
      static_cast<double>(view.turn - node.asOfTurn) * view.secondsPerTurn / K_SECONDS_PER_DAY;
  return std::format("{} (last heard {:.0f} d ago)", name, ageDays);
}

/** @brief The authority marker's label: "authority" in its own view; from a
 *         colony, the host with the age of its latest arrival. */
std::string authorityLabel(const game::CampaignViewSnapshot &view) {
  if (view.perceivedBy == game::K_AUTHORITY_NODE) {
    return "authority";
  }
  const auto host = std::ranges::find(view.nodes, game::K_AUTHORITY_NODE, &game::NodeView::id);
  return host == view.nodes.end() ? std::string("host (never heard)")
                                  : remoteLabel(view, *host, "host");
}

/** @brief One order's line from its origin to the fleet, with a dot at its
 *         causal progress when the sender can estimate the arrival. */
void drawOrderInFlight(ImDrawList *drawList, const game::CampaignViewSnapshot &view,
                       const game::OrderInFlightView &order, ImVec2 from, ImVec2 to) {
  drawList->AddLine(from, to, IM_COL32(90, 200, 255, 120), 1.0f);
  if (!order.effectTurnKnown) {
    return; // the sender cannot estimate the arrival: no progress dot
  }
  const ImVec2 dot = lerp(from, to, signalProgress(view.turn, order.issueTurn, order.effectTurn));
  drawList->AddCircleFilled(dot, 3.0f, IM_COL32(90, 200, 255, 255), 12);
}

/** @brief A station's marker position on the map. */
struct StationPos {
  game::NodeId node = game::K_AUTHORITY_NODE;
  ImVec2 pos;
};

/** @brief Draws colonies at the bottom of their rings (the viewer's own
 *         marked) and returns every station's position, the host first. */
std::vector<StationPos> drawColonies(ImDrawList *drawList, const MapScale &scale,
                                     const game::CampaignViewSnapshot &view, ImVec2 authorityPos) {
  std::vector<StationPos> stations = {{.node = game::K_AUTHORITY_NODE, .pos = authorityPos}};
  for (const game::NodeView &node : view.nodes) {
    if (!node.isColony) {
      continue;
    }
    const ImVec2 pos = ringPoint(scale, node.radiusCm, 1.5707963f);
    stations.push_back({.node = node.id, .pos = pos});
    drawGlow(drawList, pos, 7.0f, IM_COL32(120, 230, 150, 255));
    drawList->AddCircleFilled(pos, 5.5f, IM_COL32(120, 230, 150, 255), 24);
    drawList->AddText({pos.x + 8.0f, pos.y - 8.0f}, IM_COL32(150, 240, 170, 255),
                      remoteLabel(view, node, "colony").c_str());
  }
  return stations;
}

/** @brief Story signals between stations (packets, notices) the view knows
 *         of, dot at the causal progress fraction. */
template <typename NodePos>
void drawStationSignals(ImDrawList *drawList, const game::CampaignViewSnapshot &view,
                        const NodePos &nodePos) {
  for (const game::ArrivalRecord &signal : view.nodeSignalsInFlight) {
    const ImVec2 from = nodePos(signal.sender);
    const ImVec2 to = nodePos(signal.destination);
    drawList->AddLine(from, to, IM_COL32(150, 240, 170, 90), 1.0f);
    const ImVec2 dot =
        lerp(from, to, signalProgress(view.turn, signal.emitTurn, signal.arrivalTurn));
    drawList->AddCircleFilled(dot, 3.0f, IM_COL32(150, 240, 170, 255), 12);
  }
}


} // namespace

void renderStrategicMap(const game::CampaignViewSnapshot &view, CampaignUiState &uiState,
                        unsigned int backdropTextureId, const char *backdropCredit) {
  ImGui::SetNextWindowPos(ImVec2(420.0f, 470.0f), ImGuiCond_FirstUseEver);
  ImGui::SetNextWindowSize(ImVec2(520.0f, 420.0f), ImGuiCond_FirstUseEver);
  if (!ImGui::Begin("Strategic Map", nullptr, ImGuiWindowFlags_NoCollapse)) {
    ImGui::End();
    return;
  }

  const ImVec2 canvasOrigin = ImGui::GetCursorScreenPos();
  ImVec2 canvasSize = ImGui::GetContentRegionAvail();
  canvasSize.x = std::max(canvasSize.x, 120.0f);
  canvasSize.y = std::max(canvasSize.y, 120.0f);
  // The invisible button owns every click on the canvas: ImGui captures the
  // mouse, so a map click can never rotate the scene camera.
  static_cast<void>(ImGui::InvisibleButton("strategic_map_canvas", canvasSize));
  const bool canvasClicked = ImGui::IsItemClicked(ImGuiMouseButton_Left);

  ImDrawList *drawList = ImGui::GetWindowDrawList();
  drawMapBackdrop(drawList, canvasOrigin, canvasSize, backdropTextureId);
  MapScale scale;
  scale.center = {canvasOrigin.x + (canvasSize.x * 0.5f), canvasOrigin.y + (canvasSize.y * 0.5f)};
  scale.maxRadiusPx = (0.5f * std::min(canvasSize.x, canvasSize.y)) - 8.0f;

  const double rMax = std::accumulate(view.bands.begin(), view.bands.end(), view.authorityRadiusCm,
                                      [](double radiusCm, const game::BandView &band) {
                                        return std::max(radiusCm, band.radiusCm);
                                      });
  scale.rMinCm = view.innerBoundaryRadiusCm > 0.0 ? view.innerBoundaryRadiusCm : rMax / 1000.0;
  scale.rMaxCm = rMax * 1.15;

  // Ergosphere shell: the static limit. Drawn as a filled amber band between
  // the horizon and r_ergo so the forbidden-retrograde zone reads at a glance.
  // Only meaningful with spin (without it r_ergo coincides with the horizon).
  if (view.spinDimensionless != 0.0 && view.ergosphereRadiusCm > view.innerBoundaryRadiusCm) {
    const float ergoPx = scale.pixelRadius(view.ergosphereRadiusCm);
    drawList->AddCircleFilled(scale.center, ergoPx, IM_COL32(70, 45, 15, 90), 96);
    drawGlow(drawList, scale.center, ergoPx, IM_COL32(210, 150, 60, 255));
    drawList->AddCircle(scale.center, ergoPx, IM_COL32(210, 150, 60, 200), 96, 1.5f);
    drawList->AddText({scale.center.x + (ergoPx * 0.7071f) + 4.0f,
                       scale.center.y + (ergoPx * 0.7071f) + 4.0f},
                      IM_COL32(210, 150, 60, 220), "ergosphere");
  }

  // Horizon core: the forbidden zone every other radius is measured from.
  if (view.innerBoundaryRadiusCm > 0.0) {
    const float corePx = scale.maxRadiusPx * K_CORE_FRACTION;
    drawList->AddCircleFilled(scale.center, corePx, IM_COL32(8, 8, 12, 255), 64);
    drawList->AddCircle(scale.center, corePx, IM_COL32(200, 40, 40, 255), 64, 2.0f);
    if (view.spinDimensionless > 0.0) {
      drawFrameDragArc(drawList, scale.center, corePx);
    }
  }

  drawOrbitalBands(drawList, scale, view);

  // Authority station: command origin, drawn at the top of its ring. Seen
  // from a colony it is the host as last heard: its position is geometry,
  // its state only what its latest arrival stamped.
  const ImVec2 authorityPos = ringPoint(scale, view.authorityRadiusCm, -1.5707963f);
  drawList->AddCircle(scale.center, scale.pixelRadius(view.authorityRadiusCm),
                      IM_COL32(120, 140, 220, 140), 96, 1.0f);
  drawGlow(drawList, authorityPos, 7.0f, IM_COL32(120, 140, 220, 255));
  drawList->AddCircleFilled(authorityPos, 6.0f, IM_COL32(120, 140, 220, 255), 24);
  drawList->AddText({authorityPos.x + 8.0f, authorityPos.y - 8.0f},
                    IM_COL32(150, 170, 240, 255), authorityLabel(view).c_str());

  const std::vector<StationPos> stations = drawColonies(drawList, scale, view, authorityPos);
  const auto nodePos = [&stations, authorityPos](game::NodeId id) {
    const auto found = std::ranges::find(stations, id, &StationPos::node);
    return found == stations.end() ? authorityPos : found->pos;
  };

  // Fleet markers; remember positions for hit-testing and signal endpoints.
  struct Marker {
    game::FleetId fleet = game::K_INVALID_FLEET_ID;
    ImVec2 pos;
  };
  std::vector<Marker> markers;
  markers.reserve(view.fleets.size());
  std::string outOfContact;
  for (const game::FleetView &fleet : view.fleets) {
    if (!fleet.positionKnown) {
      // The viewer cannot place this fleet; it is listed, not drawn.
      outOfContact += std::format("{}{} {}", outOfContact.empty() ? "" : ", ", fleet.id,
                                  game::capabilityName(fleet.capability));
      continue;
    }
    const auto band = std::ranges::find(view.bands, fleet.bandIndex, &game::BandView::index);
    const double bandRadiusCm = band == view.bands.end() ? view.authorityRadiusCm : band->radiusCm;
    const ImVec2 pos = ringPoint(scale, bandRadiusCm, fleetAngleRad(fleet.id));
    markers.push_back({.fleet = fleet.id, .pos = pos});
    const bool selected = fleet.id == uiState.selectedFleet;
    // Without telemetry the marker takes its band's clock, not the fleet's.
    const double markerRate = fleet.telemetryKnown || band == view.bands.end()
                                  ? fleet.properTimeRate
                                  : band->properTimeRate;
    drawGlow(drawList, pos, 7.0f, rateColor(markerRate));
    drawList->AddCircleFilled(pos, 5.0f, rateColor(markerRate), 20);
    drawList->AddCircle(pos, selected ? 9.0f : 6.5f,
                        selected ? IM_COL32(255, 220, 80, 255) : IM_COL32(230, 230, 235, 200), 20,
                        selected ? 2.5f : 1.0f);
    // Relay fleets carry a cyan halo (they shorten signals crossing their band);
    // corrupted fleets a red one (their telemetry is discounted until verified).
    if (fleet.capability == game::FleetCapability::Relay) {
      drawList->AddCircle(pos, 11.0f, IM_COL32(90, 200, 255, 200), 20, 1.5f);
    }
    if (fleet.telemetryCorrupted) {
      drawList->AddCircle(pos, 12.5f, IM_COL32(255, 80, 80, 220), 20, 1.5f);
    }
    // A per-capability vector icon beside the marker, plus a small +/- lane tag
    // so orbital direction still reads at a glance.
    drawCapabilityIcon(drawList, {pos.x + 12.0f, pos.y}, fleet.capability,
                       IM_COL32(235, 235, 240, 255));
    const char laneText[2] = {fleet.lane == game::OrbitLane::Retrograde ? '-' : '+', '\0'};
    drawList->AddText({pos.x + 18.0f, pos.y - 7.0f}, IM_COL32(200, 200, 210, 255), laneText);
  }

  const auto markerFor = [&markers](game::FleetId fleetId) -> const Marker * {
    const auto marker = std::ranges::find(markers, fleetId, &Marker::fleet);
    return marker == markers.end() ? nullptr : &*marker;
  };

  // Orders in flight: origin station -> fleet, dot at the causal progress
  // fraction.
  for (const game::OrderInFlightView &order : view.ordersInFlight) {
    if (const Marker *target = markerFor(order.fleet); target != nullptr) {
      drawOrderInFlight(drawList, view, order, nodePos(order.origin), target->pos);
    }
  }

  // Completion reports in flight: fleet -> authority.
  for (const game::ReportInFlightView &report : view.reportsInFlight) {
    const Marker *source = markerFor(report.fleet);
    if (source == nullptr) {
      continue;
    }
    drawList->AddLine(source->pos, authorityPos, IM_COL32(255, 180, 70, 120), 1.0f);
    const ImVec2 dot = lerp(source->pos, authorityPos,
                            signalProgress(view.turn, report.completedTurn, report.effectTurn));
    drawList->AddCircleFilled(dot, 3.0f, IM_COL32(255, 180, 70, 255), 12);
  }

  drawStationSignals(drawList, view, nodePos);

  if (!outOfContact.empty()) {
    // Bottom-right, one line above the credit, clear of the station labels
    // along the top ring and the legend at bottom-left.
    const std::string text = "positions unknown here: " + outOfContact;
    const ImVec2 textSize = ImGui::CalcTextSize(text.c_str());
    drawList->AddText({canvasOrigin.x + canvasSize.x - textSize.x - 6.0f,
                       canvasOrigin.y + canvasSize.y - (2.0f * textSize.y) - 10.0f},
                      IM_COL32(200, 200, 210, 220), text.c_str());
  }

  if (canvasClicked) {
    const ImVec2 mouse = ImGui::GetMousePos();
    for (const Marker &marker : markers) {
      const float dx = mouse.x - marker.pos.x;
      const float dy = mouse.y - marker.pos.y;
      if (((dx * dx) + (dy * dy)) <= (K_HIT_RADIUS_PX * K_HIT_RADIUS_PX)) {
        uiState.selectedFleet = marker.fleet;
        break;
      }
    }
  }

  // Attribution for an image backdrop, bottom-right (required credit for the
  // NASA/agency public-domain imagery). Skipped for the procedural starfield.
  if (backdropTextureId != 0 && backdropCredit != nullptr && backdropCredit[0] != '\0') {
    const ImVec2 textSize = ImGui::CalcTextSize(backdropCredit);
    const ImVec2 creditPos = {canvasOrigin.x + canvasSize.x - textSize.x - 6.0f,
                              canvasOrigin.y + canvasSize.y - textSize.y - 5.0f};
    drawList->AddRectFilled({creditPos.x - 3.0f, creditPos.y - 2.0f},
                            {creditPos.x + textSize.x + 3.0f, creditPos.y + textSize.y + 2.0f},
                            IM_COL32(6, 8, 16, 150));
    drawList->AddText(creditPos, IM_COL32(190, 195, 210, 220), backdropCredit);
  }

  // Drawn last so the legend sits above the map and stays readable.
  drawMapLegend(drawList, canvasOrigin, canvasSize);

  ImGui::End();
}

} // namespace ui
