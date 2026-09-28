#ifndef BLACKHOLE_UI_CONSTELLATION_PANELS_H
#define BLACKHOLE_UI_CONSTELLATION_PANELS_H

#include <cstdint>
#include <memory>
#include <string>

#include "game/desktop_game.h"

namespace blackhole {
struct RenderState;
}

namespace ui {

struct ConstellationUiState {
  std::unique_ptr<game::DesktopGame> session = std::make_unique<game::DesktopGame>();
  game::SystemId selectedSystem = 0;
  game::FleetId selectedFleet = game::K_INVALID_FLEET_ID;
  int targetSystem = 0;
  int targetBand = 0;
  game::OrbitLane lane = game::OrbitLane::Prograde;
  game::StationKeeping station = game::StationKeeping::Orbit;
  game::OrderRejection lastRejection = game::OrderRejection::None;
  std::string saveMessage;
};

[[nodiscard]] inline bool selectConstellationSystem(ConstellationUiState &uiState,
                                                    const game::ConstellationViewSnapshot &snapshot,
                                                    game::SystemId system) {
  if (system >= snapshot.systems.size()) {
    return false;
  }
  uiState.selectedSystem = system;
  return true;
}

void renderConstellationPanels(ConstellationUiState &uiState, blackhole::RenderState &renderState);

} // namespace ui

#endif
