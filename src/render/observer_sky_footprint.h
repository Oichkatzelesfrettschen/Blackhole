#ifndef BLACKHOLE_RENDER_OBSERVER_SKY_FOOTPRINT_H
#define BLACKHOLE_RENDER_OBSERVER_SKY_FOOTPRINT_H

#include <algorithm>
#include <cmath>
#include <cstddef>
#include <numbers>
#include <span>

namespace blackhole {

struct SkyFootprintBox {
  double left;
  double bottom;
  double right;
  double top;
};

// The first-quadrant primitive integrates a disk over [0, x] by [0, y].
inline double skyDiskQuadrant(double radius, double x, double y) {
  x = std::clamp(x, 0.0, radius);
  y = std::clamp(y, 0.0, radius);
  const double crossing = std::sqrt(std::max((radius * radius) - (y * y), 0.0));
  if (x <= crossing) {
    return x * y;
  }
  const auto primitive = [radius](double position) {
    return 0.5 * ((position * std::sqrt(std::max((radius * radius) - (position * position), 0.0))) +
                  (radius * radius * std::asin(std::clamp(position / radius, 0.0, 1.0))));
  };
  return (crossing * y) + primitive(x) - primitive(crossing);
}

inline double skyDiskSigned(double radius, double x, double y) {
  return std::copysign(1.0, x) * std::copysign(1.0, y) *
         skyDiskQuadrant(radius, std::abs(x), std::abs(y));
}

inline double skyDiskBoxArea(double radius, const SkyFootprintBox &box) {
  return skyDiskSigned(radius, box.right, box.top) -
         skyDiskSigned(radius, box.left, box.top) -
         skyDiskSigned(radius, box.right, box.bottom) +
         skyDiskSigned(radius, box.left, box.bottom);
}

// Cumulative ring flux is spread uniformly over each annulus in the tile plane.
inline double skyFootprintFlux(std::span<const double> cumulativeFlux, double logRhoMin,
                              double logRhoMax, const SkyFootprintBox &box) {
  if (cumulativeFlux.empty()) {
    return 0.0;
  }
  const double ringWidth = (logRhoMax - logRhoMin) / static_cast<double>(cumulativeFlux.size());
  const double minimumRadius = std::exp(logRhoMin);
  const double nearestX = std::max({box.left, -box.right, 0.0});
  const double nearestY = std::max({box.bottom, -box.top, 0.0});
  const double nearestRadius = std::hypot(nearestX, nearestY);
  const double farthestRadius = std::hypot(std::max(std::abs(box.left), std::abs(box.right)),
                                          std::max(std::abs(box.bottom), std::abs(box.top)));
  const auto firstRing = static_cast<std::size_t>(std::clamp(
      std::floor((std::log(std::max(nearestRadius, minimumRadius)) - logRhoMin) / ringWidth),
      0.0, static_cast<double>(cumulativeFlux.size())));
  const auto lastRing = static_cast<std::size_t>(std::clamp(
      std::ceil((std::log(std::max(farthestRadius, minimumRadius)) - logRhoMin) / ringWidth),
      0.0, static_cast<double>(cumulativeFlux.size())));
  if (firstRing >= lastRing) {
    return 0.0;
  }
  double innerRadius = std::exp(logRhoMin + (static_cast<double>(firstRing) * ringWidth));
  double innerArea = skyDiskBoxArea(innerRadius, box);
  double previousFlux = firstRing > 0 ? cumulativeFlux[firstRing - 1] : 0.0;
  double result = 0.0;
  for (std::size_t ring = firstRing; ring < lastRing; ++ring) {
    const double outerRadius = std::exp(logRhoMin + (static_cast<double>(ring + 1) * ringWidth));
    const double outerArea = skyDiskBoxArea(outerRadius, box);
    const double annulusArea = std::numbers::pi *
                               ((outerRadius * outerRadius) - (innerRadius * innerRadius));
    result += (cumulativeFlux[ring] - previousFlux) *
              std::clamp((outerArea - innerArea) / annulusArea, 0.0, 1.0);
    innerArea = outerArea;
    innerRadius = outerRadius;
    previousFlux = cumulativeFlux[ring];
  }
  return result;
}

} // namespace blackhole

#endif
