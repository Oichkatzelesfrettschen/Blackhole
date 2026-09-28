#ifndef BLACKHOLE_RENDER_CAPTURE_IDENTITY_H
#define BLACKHOLE_RENDER_CAPTURE_IDENTITY_H

#include <algorithm>
#include <string_view>

#include "render/lut_manager.h"
#include "render/render_state.h"

namespace blackhole {

struct CaptureIdentity {
  std::string_view sceneMode;
  float tracerSpin;
  float lutSpin;
  bool lutSpinClamped;
  std::string_view diskTransferMode;
  int effectiveSteps;
  float effectiveStepSize;
};

inline CaptureIdentity captureIdentity(const RenderState &state) {
  const float tracerSpin = state.dispatch.contract.geodesic == GeodesicModel::SchwarzschildReference
                               ? 0.0f
                               : state.physicsCore.kerrSpin;
  const float lutSpin = std::clamp(tracerSpin, -K_LUT_SPIN_LIMIT, K_LUT_SPIN_LIMIT);
  std::string_view sceneMode = "blackhole";
  if (state.scene.mode == RenderState::SceneMode::ObserverSky) {
    sceneMode = "observer-sky";
  } else if (state.scene.mode == RenderState::SceneMode::Tesseract) {
    sceneMode = "tesseract";
  }
  return {.sceneMode = sceneMode,
          .tracerSpin = tracerSpin,
          .lutSpin = lutSpin,
          .lutSpinClamped = tracerSpin != lutSpin,
          .diskTransferMode = state.disk.diskTransferMode == 1 ? "interstellar" : "physical",
          .effectiveSteps = rendererStepBudget(state.dispatch.contract,
                                               state.dispatch.computeMaxSteps,
                                               state.dispatch.computeStepSize),
          .effectiveStepSize =
              rendererStepSize(state.dispatch.contract, state.dispatch.computeStepSize)};
}

std::string_view captureSourceRevision();

} // namespace blackhole

#endif
