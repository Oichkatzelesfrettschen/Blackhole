#include "rmlui_overlay.h"

#if BLACKHOLE_ENABLE_RMLUI
#include <RmlUi/Core.h>
#endif

namespace ui {

bool RmlUiOverlay::init(GLFWwindow *window, int width, int height) {
  static_cast<void>(window);
  static_cast<void>(width);
  static_cast<void>(height);
  if (initialized_) {
    return true;
  }
#if BLACKHOLE_ENABLE_RMLUI
  if (!Rml::Core::Initialise()) {
    return false;
  }
#endif
  initialized_ = true;
  return true;
}

void RmlUiOverlay::shutdown() {
  if (!initialized_) {
    return;
  }
#if BLACKHOLE_ENABLE_RMLUI
  Rml::Core::Shutdown();
#endif
  initialized_ = false;
}

void RmlUiOverlay::resize(int width, int height) {
  static_cast<void>(width);
  static_cast<void>(height);
}

void RmlUiOverlay::render() {
  if (!enabled_ || !initialized_) {
    return;
  }
#if BLACKHOLE_ENABLE_RMLUI
  // TODO: Hook RmlUi context render.
#endif
}

bool RmlUiOverlay::isEnabled() const {
  return enabled_;
}

void RmlUiOverlay::setEnabled(bool enabled) {
  enabled_ = enabled;
}

} // namespace ui
