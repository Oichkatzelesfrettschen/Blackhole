#ifndef OVERLAY_H
#define OVERLAY_H

#include <glm/glm.hpp>

#include <string>
#include <vector>

struct OverlayCurve2D {
  std::string sourcePath;
  std::vector<glm::vec2> points;
  glm::vec2 min = glm::vec2(0.0f);
  glm::vec2 max = glm::vec2(0.0f);
  std::string lastError;

  bool LoadFromTsv(const std::string &path);
};

#endif /* OVERLAY_H */

