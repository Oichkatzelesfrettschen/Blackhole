/**
 * @file overlay.h
 * @brief 2D curve overlay loaded from tab-separated value files for debug visualisation.
 */

#ifndef OVERLAY_H
#define OVERLAY_H

#include <glm/glm.hpp>

#include <string>
#include <vector>

/**
 * @brief A 2D polyline curve loaded from a two-column TSV file.
 *
 * Intended for overlaying reference data (e.g. analytic photon-ring radii)
 * on top of rendered frames in the debug UI.  After a successful load(),
 * min and max hold the axis-aligned bounding box of the point set.
 */
struct OverlayCurve2D {
  std::string sourcePath;         /**< @brief Path of the TSV file that was loaded. */
  std::vector<glm::vec2> points;  /**< @brief Parsed (x, y) data points. */
  glm::vec2 min = glm::vec2(0.0f); /**< @brief Minimum (x, y) across all points. */
  glm::vec2 max = glm::vec2(0.0f); /**< @brief Maximum (x, y) across all points. */
  std::string lastError;          /**< @brief Human-readable error string, empty on success. */

  /**
   * @brief Loads point data from a whitespace-delimited two-column text file.
   *
   * Lines beginning with '#' and blank lines are skipped.  The bounding box
   * (min, max) is computed during the parse.
   *
   * @param path Path to the TSV (or space-separated) data file.
   * @return true on success; false if the file cannot be opened or parsed.
   *         On failure, lastError contains a diagnostic message.
   */
  bool loadFromTsv(const std::string &path);
};

#endif /* OVERLAY_H */

