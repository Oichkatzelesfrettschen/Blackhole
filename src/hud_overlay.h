#ifndef HUD_OVERLAY_H
#define HUD_OVERLAY_H

#include <string>
#include <vector>

#include "gl_loader.h"
#include <glm/glm.hpp>

struct HudOverlayLine {
  std::string text;
  glm::vec4 color;
};

class HudOverlay {
public:
  void init();
  void shutdown();
  void render(int width, int height, float scale, float margin,
              const std::vector<HudOverlayLine> &lines);

private:
  GLuint vao_ = 0;
  GLuint vbo_ = 0;
  GLuint program_ = 0;
  std::vector<float> vertices_;
};

#endif
