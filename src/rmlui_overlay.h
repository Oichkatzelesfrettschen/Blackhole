#pragma once

struct GLFWwindow;

namespace ui {

class RmlUiOverlay {
 public:
  bool init(GLFWwindow *window, int width, int height);
  void shutdown();
  void resize(int width, int height);
  void render();
  bool isEnabled() const;
  void setEnabled(bool enabled);

 private:
  bool enabled_ = false;
  bool initialized_ = false;
};

} // namespace ui
