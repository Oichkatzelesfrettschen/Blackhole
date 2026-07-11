#include "render/settings_sync.h"

#include <algorithm>

#include "input.h"
#include "render/render_state.h"
#include "settings.h"

namespace blackhole {

void loadSettingsIntoRenderState(RenderState &rs, const Settings &settings) {
  if (!rs.camera.cameraSettingsLoaded) {
    rs.camera.cameraModeIndex = settings.cameraMode;
    rs.camera.orbitRadius = settings.orbitRadius;
    rs.camera.orbitSpeed = settings.orbitSpeed;
    rs.camera.cameraSettingsLoaded = true;
  }

  if (!rs.display.displaySettingsLoaded) {
    rs.display.renderScale = settings.renderScale;
    rs.display.swapInterval = settings.swapInterval;
    rs.display.displaySettingsLoaded = true;
  }
  if (!rs.post.postProcessingSettingsLoaded) {
    rs.post.bloomStrength = settings.bloomStrength;
    rs.post.tonemappingEnabled = settings.tonemappingEnabled;
    rs.post.toneExposure = 1.0f;
    rs.post.gamma = settings.gamma;
    rs.post.postProcessingSettingsLoaded = true;
  }
  if (!rs.post.bloomSettingsLoaded) {
    rs.post.bloomIterations = std::clamp(settings.bloomIterations, 1, kMaxBloomIterations);
    rs.post.bloomSettingsLoaded = true;
  }
}

void syncRenderStateToSettings(const RenderState &rs, Settings &settings, InputManager &input) {
  settings.fullscreen = input.isFullscreen();
  settings.swapInterval = rs.display.swapInterval;
  settings.renderScale = rs.display.renderScale;
  settings.bloomStrength = rs.post.bloomStrength;
  settings.tonemappingEnabled = rs.post.tonemappingEnabled;
  settings.gamma = rs.post.gamma;
  settings.bloomIterations = rs.post.bloomIterations;
}

} // namespace blackhole
