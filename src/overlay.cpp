#include "overlay.h"

#include <algorithm>
#include <fstream>
#include <sstream>
#include <string>

#include "physics/safe_limits.h"

namespace {
bool isIgnorableLine(const std::string &line) {
  for (char const c : line) {
    if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
      continue;
    }
    return c == '#';
  }
  return true;
}
} // anonymous namespace

bool OverlayCurve2D::loadFromTsv(const std::string &path) {
  sourcePath = path;
  points.clear();
  lastError.clear();

  std::ifstream in(path);
  if (!in.is_open()) {
    lastError = "failed to open file: " + path;
    return false;
  }

  auto minX = physics::safeMax<float>();
  auto minY = physics::safeMax<float>();
  auto maxX = physics::safeLowest<float>();
  auto maxY = physics::safeLowest<float>();

  std::string line;
  int lineNo = 0;
  while (std::getline(in, line)) {
    lineNo++;
    if (line.empty() || isIgnorableLine(line)) {
      continue;
    }

    std::istringstream iss(line);
    float x = 0.0f;
    float y = 0.0f;
    if (!(iss >> x >> y)) {
      lastError = "failed to parse 2 columns at line " + std::to_string(lineNo);
      points.clear();
      return false;
    }

    points.emplace_back(x, y);
    minX = std::min(minX, x);
    minY = std::min(minY, y);
    maxX = std::max(maxX, x);
    maxY = std::max(maxY, y);
  }

  if (points.empty()) {
    lastError = "no data points found (expected 2-column TSV)";
    return false;
  }

  min = glm::vec2(minX, minY);
  max = glm::vec2(maxX, maxY);
  return true;
}
