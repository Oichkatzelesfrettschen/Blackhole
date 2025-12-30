#ifndef PHYSICS_BATCH_H
#define PHYSICS_BATCH_H

#include "kerr.h"
#include "thin_disk.h"
#include <algorithm>
#include <cmath>
#include <vector>

namespace physics {

inline void fill_linspace(std::vector<double> &out, double start, double end) {
  const std::size_t count = out.size();
  if (count == 0) {
    return;
  }
  if (count == 1) {
    out[0] = start;
    return;
  }
  const double step = (end - start) / static_cast<double>(count - 1);
  for (std::size_t i = 0; i < count; ++i) {
    out[i] = start + step * static_cast<double>(i);
  }
}

inline void disk_flux_batch(const std::vector<double> &radii, const DiskParams &disk,
                            std::vector<float> &out) {
  out.resize(radii.size());
  for (std::size_t i = 0; i < radii.size(); ++i) {
    double flux = disk_flux(radii[i], disk);
    if (!std::isfinite(flux) || flux < 0.0) {
      flux = 0.0;
    }
    out[i] = static_cast<float>(flux);
  }
}

inline void kerr_redshift_batch(const std::vector<double> &radii, double theta, double mass,
                                double a, std::vector<float> &out) {
  out.resize(radii.size());
  for (std::size_t i = 0; i < radii.size(); ++i) {
    double z = kerr_redshift(radii[i], theta, mass, a);
    if (!std::isfinite(z) || z < 0.0) {
      z = 0.0;
    }
    z = std::min(z, 10.0);
    out[i] = static_cast<float>(z);
  }
}

} // namespace physics

#endif
