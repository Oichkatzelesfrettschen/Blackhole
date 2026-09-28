#ifndef BLACKHOLE_RENDER_CAPTURE_IDENTITY_H
#define BLACKHOLE_RENDER_CAPTURE_IDENTITY_H

#include <algorithm>
#include <string_view>

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
  const float lutSpin = std::clamp(tracerSpin, -0.99f, 0.99f);
  std::string_view sceneMode = "blackhole";
  if (state.scene.mode == RenderState::SceneMode::ObserverSky) {
    sceneMode = "observer-sky";
  } else if (state.scene.mode == RenderState::SceneMode::Tesseract) {
    sceneMode = "tesseract";
  }
  return {sceneMode,
          tracerSpin,
          lutSpin,
          tracerSpin != lutSpin,
          state.disk.diskTransferMode == 1 ? "interstellar" : "physical",
          rendererStepBudget(state.dispatch.contract, state.dispatch.computeMaxSteps,
                             state.dispatch.computeStepSize),
          rendererStepSize(state.dispatch.contract, state.dispatch.computeStepSize)};
}

std::string_view captureSourceRevision();

} // namespace blackhole

#endif
