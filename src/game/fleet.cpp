/**
 * @file fleet.cpp
 * @brief Fleet helpers.
 */

#include "game/fleet.h"

#include "game/temporal_clock.h"

namespace game {

const char *capabilityName(FleetCapability capability) {
  switch (capability) {
  case FleetCapability::Research:
    return "research";
  case FleetCapability::Fabrication:
    return "fabrication";
  case FleetCapability::Relay:
    return "relay";
  case FleetCapability::Verification:
    return "verification";
  case FleetCapability::Extraction:
    return "extraction";
  }
  return "unknown";
}

void accrueProperTime(Fleet &fleet, double properTimeRate, double secondsPerTurn) {
  fleet.properTimeSec += properDeltaSec(properTimeRate, secondsPerTurn);
}

} // namespace game
