/**
 * @file record_mode.h
 * @brief Offline record-mode framing data and helpers.
 *
 * ShowcaseOrbitComposition is the per-composition framing table the
 * showcase-orbit record profile draws from (camera pitch/distance/fov,
 * background asset and orientation, sweep and frame offsets). The lookup and
 * the beauty-wiregrid tuning are shared by the CLI validation in main and the
 * record-mode clusters in the render loop.
 */

#ifndef BLACKHOLE_RENDER_RECORD_MODE_H
#define BLACKHOLE_RENDER_RECORD_MODE_H

#include <string_view>

#include <glm/ext/vector_float4.hpp>

namespace blackhole {

struct WiregridParams;

/** @brief Framing preset for one named showcase-orbit composition. */
struct ShowcaseOrbitComposition {
  const char *name;
  const char *backgroundId;
  float frameOffsetX;
  float frameOffsetY;
  float pitchDeg;
  float distance;
  float fovDeg;
  float exposure;
  float backgroundIntensity;
  float backgroundYawDeg;
  float backgroundPitchDeg;
  float backgroundOffsetX;
  float backgroundOffsetY;
  float sweepDeg;
};

/** @brief Returns the composition matching name, or nullptr if none matches. */
const ShowcaseOrbitComposition *findShowcaseOrbitComposition(std::string_view name);

/** @brief Applies per-composition beauty-wiregrid tuning; no-op unless params is
 *         in Beauty mode. */
void applyShowcaseBeautyWiregridTuning(std::string_view compositionName, WiregridParams &params,
                                       glm::vec4 &color);

} // namespace blackhole

#endif // BLACKHOLE_RENDER_RECORD_MODE_H
