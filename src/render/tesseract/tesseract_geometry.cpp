/**
 * @file tesseract_geometry.cpp
 * @brief 4-cube complex, 4D->3D projections, SO(4) motion, and the
 *        rectilinear lattice's pure math.
 */

#include "render/tesseract/tesseract_geometry.h"

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>

#include <glm/common.hpp>
#include <glm/ext/vector_float3.hpp>
#include <glm/ext/vector_float4.hpp>
#include <glm/ext/vector_int3.hpp>
#include <glm/geometric.hpp>

#include "render/tesseract/so4.h"

namespace blackhole::tesseract {
namespace {

constexpr std::size_t AXIS_COUNT = 4;

/** Bit mask with bit @p axis set. */
constexpr std::size_t bit(std::size_t axis) {
  return std::size_t{1} << axis;
}

/// Smallest lattice cell size latticeLocalPosition/latticeCellIndex divide by.
constexpr float LATTICE_MIN_CELL_SIZE = 1e-4f;

} // namespace

glm::vec4 tesseractVertex(std::size_t index) {
  auto coordinate = [index](std::size_t axis) { return (index & bit(axis)) != 0 ? 1.0f : -1.0f; };
  return {coordinate(0), coordinate(1), coordinate(2), coordinate(3)};
}

TesseractMesh buildTesseract() {
  TesseractMesh mesh;
  for (std::size_t i = 0; i < TESSERACT_VERTEX_COUNT; ++i) {
    mesh.vertices.at(i) = tesseractVertex(i);
  }
  for (std::size_t i = 0; i < TESSERACT_VERTEX_COUNT; ++i) {
    for (std::size_t axis = 0; axis < AXIS_COUNT; ++axis) {
      if ((i & bit(axis)) == 0) {
        mesh.edges.push_back({.a = i, .b = i | bit(axis), .axis = axis});
      }
    }
  }
  for (std::size_t axisA = 0; axisA < AXIS_COUNT; ++axisA) {
    for (std::size_t axisB = axisA + 1; axisB < AXIS_COUNT; ++axisB) {
      const std::size_t spanMask = bit(axisA) | bit(axisB);
      for (std::size_t base = 0; base < TESSERACT_VERTEX_COUNT; ++base) {
        if ((base & spanMask) != 0) {
          continue;
        }
        mesh.faces.push_back(
            {.vertices = {base, base | bit(axisA), base | spanMask, base | bit(axisB)},
             .axisA = axisA,
             .axisB = axisB});
      }
    }
  }
  for (std::size_t axis = 0; axis < AXIS_COUNT; ++axis) {
    for (const bool positive : {false, true}) {
      TesseractCell cell;
      cell.axis = axis;
      cell.sign = positive ? 1.0f : -1.0f;
      std::size_t slot = 0;
      for (std::size_t i = 0; i < TESSERACT_VERTEX_COUNT; ++i) {
        if (((i & bit(axis)) != 0) == positive) {
          cell.vertices.at(slot) = i;
          ++slot;
        }
      }
      mesh.cells.push_back(cell);
    }
  }
  return mesh;
}

glm::vec3 projectPerspective(const glm::vec4 &p, float eyeDistance) {
  const float denom = std::max(eyeDistance - p.w, PERSPECTIVE_MIN_DEPTH);
  return glm::vec3(p) * (eyeDistance / denom);
}

StereographicPoint projectStereographic(const glm::vec4 &p) {
  const float len = glm::length(p);
  const glm::vec4 s = len > STEREOGRAPHIC_MIN_NORM ? p / len : glm::vec4(0.0f, 0.0f, 0.0f, -1.0f);
  const float denom = 1.0f - s.w;
  StereographicPoint out;
  out.fade = glm::smoothstep(STEREOGRAPHIC_MIN_DENOM, STEREOGRAPHIC_FADE_END, denom);
  out.position = glm::vec3(s) / std::max(denom, STEREOGRAPHIC_MIN_DENOM);
  return out;
}

glm::vec3 latticeLocalPosition(const glm::vec3 &p, float cellSize) {
  const float size = std::max(cellSize, LATTICE_MIN_CELL_SIZE);
  return p - (size * glm::round(p / size));
}

glm::ivec3 latticeCellIndex(const glm::vec3 &p, float cellSize) {
  const float size = std::max(cellSize, LATTICE_MIN_CELL_SIZE);
  const glm::vec3 index = glm::round(p / size);
  return {static_cast<int>(index.x), static_cast<int>(index.y), static_cast<int>(index.z)};
}

float hueDegrees(const glm::vec3 &rgb) {
  const float maxC = std::max({rgb.r, rgb.g, rgb.b});
  const float minC = std::min({rgb.r, rgb.g, rgb.b});
  const float delta = maxC - minC;
  if (delta <= 1e-6f) {
    return 0.0f;
  }
  float hue = 0.0f;
  if (maxC == rgb.r) {
    hue = 60.0f * std::fmod((rgb.g - rgb.b) / delta, 6.0f);
  } else if (maxC == rgb.g) {
    hue = 60.0f * (((rgb.b - rgb.r) / delta) + 2.0f);
  } else {
    hue = 60.0f * (((rgb.r - rgb.g) / delta) + 4.0f);
  }
  return hue < 0.0f ? hue + 360.0f : hue;
}

glm::vec4 libraryToTesseract(const glm::vec4 &p, float timeSpan) {
  return {p.x, p.y, p.z, ((2.0f * p.w) / timeSpan) - 1.0f};
}

float litMomentEmission(float t, float litMoment, float width) {
  const float u = (t - litMoment) / std::max(width, EMISSION_MIN_WIDTH);
  return std::exp(-0.5f * u * u);
}

float advancePulseTravel(float travel, float distance, float span) {
  if (span <= 0.0f) {
    return 0.0f;
  }
  float wrapped = std::fmod(travel + distance, span);
  if (wrapped < 0.0f) {
    wrapped += span;
  }
  return wrapped;
}

So4Pair<double> advanceOrientation(const So4Pair<double> &orientation,
                                   const std::array<float, 3> &leftRate,
                                   const std::array<float, 3> &rightRate, double ds) {
  const auto step = [ds](const std::array<float, 3> &rate) {
    return quatExp(ds * static_cast<double>(rate.at(0)), ds * static_cast<double>(rate.at(1)),
                   ds * static_cast<double>(rate.at(2)));
  };
  return {.left = normalized(step(leftRate) * orientation.left),
          .right = normalized(step(rightRate) * orientation.right)};
}

TesseractMotion tesseractMotionAt(const std::array<float, 3> &leftRate,
                                  const std::array<float, 3> &rightRate, double resetPhase,
                                  double rotationSpeed, float pulseSpeed, float pulseSpan,
                                  double seconds) {
  TesseractMotion motion;
  motion.orientation = advanceOrientation(So4Pair<double>{}, leftRate, rightRate,
                                          resetPhase + (rotationSpeed * seconds));
  motion.pulseTravel = advancePulseTravel(
      0.0f, static_cast<float>(static_cast<double>(pulseSpeed) * seconds), pulseSpan);
  return motion;
}

} // namespace blackhole::tesseract
