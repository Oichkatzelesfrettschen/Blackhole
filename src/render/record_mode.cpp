/**
 * @file record_mode.cpp
 * @brief Showcase-orbit composition table, lookup, and beauty-wiregrid tuning.
 */

#include "render/record_mode.h"

#include <array>

#include "render/render_state.h" // WiregridParams

namespace blackhole {
namespace {

constexpr std::array<ShowcaseOrbitComposition, 5> K_SHOWCASE_ORBIT_COMPOSITIONS = {{
    {"centered", "nasa_deep_starmap_galactic", 0.0f, 0.0f, -8.0f, 21.0f, 60.0f, 3.05f, 0.74f, -18.0f, 6.0f, 0.00f, 0.00f, 8.0f},
    {"left-third", "nasa_deep_starmap", 0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, -34.0f, 7.0f, 0.05f, -0.02f, 7.0f},
    {"right-third", "nasa_deep_starmap_galactic", -0.18f, 0.03f, -8.0f, 23.0f, 58.0f, 2.95f, 0.76f, 18.0f, 7.0f, -0.05f, -0.02f, 7.0f},
    {"wide-left", "eso_milkyway_brunier", 0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.75f, 0.70f, -42.0f, 8.0f, 0.08f, -0.03f, 6.0f},
    {"wide-right", "nasa_deep_starmap_galactic", -0.12f, -0.02f, -7.0f, 27.5f, 54.0f, 2.9f, 0.80f, 26.0f, 8.0f, -0.08f, -0.03f, 6.0f},
}};

} // namespace

const ShowcaseOrbitComposition *findShowcaseOrbitComposition(std::string_view name) {
  for (const auto &composition : K_SHOWCASE_ORBIT_COMPOSITIONS) {
    if (name == composition.name) {
      return &composition;
    }
  }
  return nullptr;
}

void applyShowcaseBeautyWiregridTuning(std::string_view compositionName, WiregridParams &params,
                                       glm::vec4 &color) {
  if (params.mode != WiregridParams::Mode::Beauty) {
    return;
  }

  if (compositionName == "wide-right") {
    params.gridScale = 0.78f;
    params.motionScale = 0.48f;
    params.infallScale = 0.16f;
    params.strength = 0.48f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.19f, 0.58f, 0.90f, 0.11f);
    return;
  }
  if (compositionName == "right-third") {
    params.gridScale = 0.84f;
    params.motionScale = 0.54f;
    params.infallScale = 0.20f;
    params.strength = 0.56f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.20f, 0.60f, 0.91f, 0.12f);
    return;
  }
  if (compositionName == "wide-left") {
    params.gridScale = 0.82f;
    params.motionScale = 0.50f;
    params.infallScale = 0.18f;
    params.strength = 0.52f;
    params.scenePreserve = 1.0f;
    color = glm::vec4(0.19f, 0.58f, 0.89f, 0.11f);
  }
}

} // namespace blackhole
