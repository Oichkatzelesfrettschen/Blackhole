/**
 * @file strategic_map.cpp
 * @brief ImDrawList orbital map implementation.
 */

#include "ui/strategic_map.h"

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <cstdio>
#include <vector>

#include <imgui.h>

#include "game/campaign_view.h"
#include "game/fleet.h"
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

char capabilityGlyph(game::FleetCapability capability) {
  switch (capability) {
  case game::FleetCapability::Research:
    return 'R';
  case game::FleetCapability::Fabrication:
    return 'F';
  case game::FleetCapability::Relay:
    return 'L';
  case game::FleetCapability::Verification:
    return 'V';
  case game::FleetCapability::Extraction:
    return 'E';
  }
  return '?';
}

} // namespace

void renderStrategicMap(const game::CampaignViewSnapshot &view, CampaignUiState &uiState) {
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
  MapScale scale;
  scale.center = {canvasOrigin.x + (canvasSize.x * 0.5f), canvasOrigin.y + (canvasSize.y * 0.5f)};
  scale.maxRadiusPx = (0.5f * std::min(canvasSize.x, canvasSize.y)) - 8.0f;

  double rMax = view.authorityRadiusCm;
  for (const game::BandView &band : view.bands) {
    rMax = std::max(rMax, band.radiusCm);
  }
  scale.rMinCm = view.innerBoundaryRadiusCm > 0.0 ? view.innerBoundaryRadiusCm : rMax / 1000.0;
  scale.rMaxCm = rMax * 1.15;

  // Ergosphere shell: the static limit. Drawn as a filled amber band between
  // the horizon and r_ergo so the forbidden-retrograde zone reads at a glance.
  // Only meaningful with spin (without it r_ergo coincides with the horizon).
  if (view.spinDimensionless != 0.0 && view.ergosphereRadiusCm > view.innerBoundaryRadiusCm) {
    const float ergoPx = scale.pixelRadius(view.ergosphereRadiusCm);
    drawList->AddCircleFilled(scale.center, ergoPx, IM_COL32(70, 45, 15, 90), 96);
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

  // Orbital bands, colored by proper-time rate; invalid bands draw as hazard.
  char label[96];
  for (const game::BandView &band : view.bands) {
    const float bandPx = scale.pixelRadius(band.radiusCm);
    if (band.validStation && band.insideErgosphere) {
      drawList->AddCircle(scale.center, bandPx, IM_COL32(210, 150, 60, 230), 96, 2.0f);
      static_cast<void>(std::snprintf(
          label, sizeof(label), "band %d  dtau/dt %.3f  omega %.2e  PROGRADE ONLY", band.index,
          band.properTimeRate, band.frameDragRateRadPerSec));
    } else if (band.validStation) {
      drawList->AddCircle(scale.center, bandPx, rateColor(band.properTimeRate), 96, 1.5f);
      static_cast<void>(std::snprintf(label, sizeof(label), "band %d  dtau/dt %.3f  delay %.1f d", band.index,
                    band.properTimeRate, band.delayToAuthoritySec / K_SECONDS_PER_DAY));
    } else {
      drawList->AddCircle(scale.center, bandPx, IM_COL32(120, 30, 30, 180), 96, 1.0f);
      static_cast<void>(std::snprintf(label, sizeof(label), "band %d  FORBIDDEN", band.index));
    }
    drawList->AddText({scale.center.x + (bandPx * 0.7071f) + 6.0f,
                       scale.center.y - (bandPx * 0.7071f) - 6.0f},
                      IM_COL32(200, 200, 210, 255), label);
  }

  // Authority station: command origin, drawn at the top of its ring.
  const ImVec2 authorityPos = ringPoint(scale, view.authorityRadiusCm, -1.5707963f);
  drawList->AddCircle(scale.center, scale.pixelRadius(view.authorityRadiusCm),
                      IM_COL32(120, 140, 220, 140), 96, 1.0f);
  drawList->AddCircleFilled(authorityPos, 6.0f, IM_COL32(120, 140, 220, 255), 24);
  drawList->AddText({authorityPos.x + 8.0f, authorityPos.y - 8.0f},
                    IM_COL32(150, 170, 240, 255), "authority");

  // Fleet markers; remember positions for hit-testing and signal endpoints.
  struct Marker {
    game::FleetId fleet = game::K_INVALID_FLEET_ID;
    ImVec2 pos;
  };
  std::vector<Marker> markers;
  markers.reserve(view.fleets.size());
  for (const game::FleetView &fleet : view.fleets) {
    double bandRadiusCm = view.authorityRadiusCm;
    for (const game::BandView &band : view.bands) {
      if (band.index == fleet.bandIndex) {
        bandRadiusCm = band.radiusCm;
        break;
      }
    }
    const ImVec2 pos = ringPoint(scale, bandRadiusCm, fleetAngleRad(fleet.id));
    markers.push_back({.fleet = fleet.id, .pos = pos});
    const bool selected = fleet.id == uiState.selectedFleet;
    drawList->AddCircleFilled(pos, 5.0f, rateColor(fleet.properTimeRate), 20);
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
    // Distinct glyph per capability: Research and Relay both start with 'R',
    // so Relay takes 'L' to keep map markers unambiguous.
    const char glyph = capabilityGlyph(fleet.capability);
    // Lane tag: '+' prograde, '-' retrograde, so orbital direction reads on the
    // marker without a legend.
    const char laneTag = fleet.lane == game::OrbitLane::Retrograde ? '-' : '+';
    const char markerText[4] = {glyph, laneTag, '\0', '\0'};
    drawList->AddText({pos.x + 8.0f, pos.y - 7.0f}, IM_COL32(235, 235, 240, 255), markerText);
  }

  const auto markerFor = [&markers](game::FleetId fleetId) -> const Marker * {
    for (const Marker &marker : markers) {
      if (marker.fleet == fleetId) {
        return &marker;
      }
    }
    return nullptr;
  };

  // Orders in flight: authority -> fleet, dot at the causal progress fraction.
  for (const game::OrderInFlightView &order : view.ordersInFlight) {
    const Marker *target = markerFor(order.fleet);
    if (target == nullptr) {
      continue;
    }
    drawList->AddLine(authorityPos, target->pos, IM_COL32(90, 200, 255, 120), 1.0f);
    const ImVec2 dot = lerp(authorityPos, target->pos,
                            signalProgress(view.turn, order.issueTurn, order.effectTurn));
    drawList->AddCircleFilled(dot, 3.0f, IM_COL32(90, 200, 255, 255), 12);
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

  ImGui::End();
}

} // namespace ui
