/**
 * @file rmlui_overlay.cpp
 * @brief Implementation of RmlUiOverlay -- RmlUi context lifecycle and per-frame render.
 *
 * WHY: The Blackhole renderer uses an optional RmlUi overlay for in-render HUD
 *      elements (physics readouts, debug panels) that sit on top of the GL framebuffer.
 * WHAT: When BLACKHOLE_ENABLE_RMLUI is defined, init() calls Rml::Initialise(),
 *       creates a named context at the given framebuffer dimensions, and render()
 *       drives the per-frame Update/Render cycle.  All paths are stubs when disabled.
 * HOW:  Rml::Context::Update() propagates tween animations and event dispatch.
 *       Rml::Context::Render() issues OpenGL draw calls via the installed RenderInterface.
 *       The context is destroyed and Rml::Shutdown() is called in shutdown().
 */
#include "rmlui_overlay.h"

#if BLACKHOLE_ENABLE_RMLUI
#include <RmlUi/Core.h>
#endif

namespace ui {

bool RmlUiOverlay::init(GLFWwindow *window, int width, int height) {
  static_cast<void>(window);
  if (initialized_) {
    return true;
  }
#if BLACKHOLE_ENABLE_RMLUI
  /* WHY: Rml::Initialise() must be called before any context is created.
   * It validates that a SystemInterface and RenderInterface have been installed
   * by the host application (the Blender addon or the main renderer must set
   * these up before calling init()).  If they are absent, Initialise() returns
   * false and we surface the failure to the caller. */
  if (!Rml::Initialise()) {
    return false;
  }

  /* Create the primary rendering context at the given framebuffer size.
   * The context name "blackhole_overlay" is arbitrary but must be unique
   * within the process -- it is used to retrieve the context later if needed. */
  context_ = Rml::CreateContext("blackhole_overlay",
                                 Rml::Vector2i(width, height));
  if (context_ == nullptr) {
    Rml::Shutdown();
    return false;
  }
#else
  static_cast<void>(width);
  static_cast<void>(height);
#endif
  initialized_ = true;
  return true;
}

void RmlUiOverlay::shutdown() {
  if (!initialized_) {
    return;
  }
#if BLACKHOLE_ENABLE_RMLUI
  /* WHY: Rml::RemoveContext destroys documents and event listeners attached to
   * this context before Rml::Shutdown() tears down the render interface.  Doing
   * this in the right order prevents use-after-free in the RmlUi backend. */
  if (context_ != nullptr) {
    Rml::RemoveContext("blackhole_overlay");
    context_ = nullptr;
  }
  Rml::Shutdown();
#endif
  initialized_ = false;
}

void RmlUiOverlay::resize(int width, int height) {
#if BLACKHOLE_ENABLE_RMLUI
  if (context_ != nullptr) {
    context_->SetDimensions(Rml::Vector2i(width, height));
  }
#else
  static_cast<void>(width);
  static_cast<void>(height);
#endif
}

void RmlUiOverlay::render() const {
  if (!enabled_ || !initialized_) {
    return;
  }
#if BLACKHOLE_ENABLE_RMLUI
  if (context_ == nullptr) {
    return;
  }
  /* WHY: Update() must precede Render() each frame.  It processes deferred
   * property animations, layout reflows triggered by data bindings, and queued
   * event dispatches.  Skipping it causes stale layout and flickering elements. */
  context_->Update();
  context_->Render();
#endif
}

bool RmlUiOverlay::isEnabled() const {
  return enabled_;
}

void RmlUiOverlay::setEnabled(bool enabled) {
  enabled_ = enabled;
}

} // namespace ui
