#pragma once
/**
 * @file rmlui_overlay.h
 * @brief Optional RmlUi-based overlay layer for the black hole renderer.
 *
 * Compiled in only when BLACKHOLE_ENABLE_RMLUI is defined.  When the macro is
 * absent all methods compile as stubs so call sites need no preprocessor guards.
 */

#if BLACKHOLE_ENABLE_RMLUI
namespace Rml {
class Context;
}
#endif

struct GLFWwindow;

namespace ui {

/**
 * @brief Manages the RmlUi context lifecycle and per-frame rendering.
 *
 * A single instance is owned by the application.  Call init() after the GL
 * context and GLFW window exist; call shutdown() before destroying the window.
 * The overlay renders nothing until setEnabled(true) is called.
 */
class RmlUiOverlay {
 public:
  /**
   * @brief Initialize the RmlUi context and attach it to the given window.
   *
   * Safe to call multiple times; subsequent calls return true immediately
   * if already initialized.
   *
   * @param window GLFW window that will receive RmlUi input events.
   * @param width  Initial framebuffer width in pixels.
   * @param height Initial framebuffer height in pixels.
   * @return true on success (or if already initialized), false on RmlUi error.
   */
  bool init(GLFWwindow *window, int width, int height);

  /**
   * @brief Shut down the RmlUi context and release its resources.
   *
   * No-op if not initialized.
   */
  void shutdown();

  /**
   * @brief Notify the overlay of a framebuffer resize.
   * @param width  New framebuffer width in pixels.
   * @param height New framebuffer height in pixels.
   */
  void resize(int width, int height);

  /**
   * @brief Render the RmlUi context for the current frame.
   *
   * No-op when the overlay is disabled or not yet initialized.
   */
  void render() const;

  /** @brief Return true when the overlay is both initialized and enabled. */
  [[nodiscard]] bool isEnabled() const;

  /**
   * @brief Enable or disable overlay rendering without releasing resources.
   * @param enabled Pass true to allow render() to draw; false to suppress it.
   */
  void setEnabled(bool enabled);

 private:
  bool enabled_ = false;
  bool initialized_ = false;
#if BLACKHOLE_ENABLE_RMLUI
  Rml::Context *context_ = nullptr;
#endif
};

} // namespace ui
