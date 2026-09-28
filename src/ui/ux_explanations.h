#ifndef BLACKHOLE_UI_UX_EXPLANATIONS_H
#define BLACKHOLE_UI_UX_EXPLANATIONS_H

#include <algorithm>
#include <cmath>
#include <cstdint>
#include <format>
#include <numbers>
#include <string>
#include <string_view>

namespace ui {

struct SimulatorExplanation {
  std::string_view disk;
  std::string_view shadow;
  std::string_view approachingSide;
  std::string_view inclination;
  std::string_view transfer;
  std::string_view display;
};

[[nodiscard]] inline SimulatorExplanation simulatorExplanation(bool diskEnabled, bool kerrTracer,
                                                               bool filmTransfer, bool bloomEnabled,
                                                               bool toneMappingEnabled) {
  std::string_view transfer = "Transfer: the legacy artistic tracer is active.";
  if (kerrTracer) {
    transfer = filmTransfer ? "Transfer: film mode keeps lensing and uses unshifted disk color."
                            : "Transfer: Physical mode applies gravitational and Doppler shifts.";
  }
  std::string_view display;
  if (bloomEnabled) {
    display = toneMappingEnabled
                  ? "Display: bloom spreads bright emission before exposure and tone mapping."
                  : "Display: bloom spreads bright emission before exposure; tone mapping is off.";
  } else {
    display = toneMappingEnabled
                  ? "Display: emission passes through exposure and tone mapping without bloom."
                  : "Display: emission passes through exposure without bloom or tone mapping.";
  }
  return {
      .disk = diskEnabled ? "Disk: orbiting gas emits the bright band; lensing shows its far side."
                          : "Disk: emission is disabled; the background remains visible.",
      .shadow = "Shadow: rays captured by the hole leave a dark region inside the lensed sky.",
      .approachingSide =
          kerrTracer && diskEnabled && !filmTransfer
              ? "Approaching side: Doppler boosting and frequency shift brighten orbiting gas."
              : "Approaching side: physical Doppler disk asymmetry is inactive.",
      .inclination =
          "Inclination: a more edge-on camera projects a thinner disk and stronger side contrast.",
      .transfer = transfer,
      .display = display};
}

[[nodiscard]] inline double angularScaleBarPixels(double fieldOfViewDegrees, double angleArcminutes,
                                                  int viewportHeight) {
  if (fieldOfViewDegrees <= 0.0 || fieldOfViewDegrees >= 180.0 || angleArcminutes <= 0.0 ||
      viewportHeight <= 0) {
    return 0.0;
  }
  const double halfAngle = angleArcminutes * std::numbers::pi / (180.0 * 60.0 * 2.0);
  const double halfField = fieldOfViewDegrees * std::numbers::pi / 360.0;
  return static_cast<double>(viewportHeight) * std::tan(halfAngle) / std::tan(halfField);
}

struct BoundedLabelPosition {
  float x = 0.0f;
  float y = 0.0f;
};

[[nodiscard]] inline BoundedLabelPosition boundedMapLabel(float desiredX, float desiredY,
                                                          float textWidth, float textHeight,
                                                          float mapX, float mapY, float mapWidth,
                                                          float mapHeight) {
  const float right = std::max(mapX, mapX + mapWidth - std::max(textWidth, 0.0f));
  const float bottom = std::max(mapY, mapY + mapHeight - std::max(textHeight, 0.0f));
  return {.x = std::clamp(desiredX, mapX, right), .y = std::clamp(desiredY, mapY, bottom)};
}

[[nodiscard]] inline std::string technologyMilestoneText(std::string_view name, std::int64_t points,
                                                         std::int64_t tier,
                                                         std::int64_t victoryTier) {
  const std::string effect = victoryTier > 0 && tier >= victoryTier
                                 ? "reaches the colony victory objective"
                                 : "raises the colony outcome tier";
  return std::format("{} ({} {}): {}", name, points, points == 1 ? "point" : "points", effect);
}

[[nodiscard]] inline std::string campaignPauseReason(std::string_view category,
                                                     std::int64_t arrivalTurn) {
  return std::format("{} arrival at the acting station on turn {}; read the inbox.", category,
                     arrivalTurn);
}

inline constexpr std::string_view K_FOCUS_EFFECT_TEXT =
    "Focus changes the acting station, perceived information, inbox, and order origin.";
inline constexpr std::string_view K_MAP_SCHEMATIC_LEGEND =
    "schematic: log radius, marker angle = fleet index";

} // namespace ui

#endif
