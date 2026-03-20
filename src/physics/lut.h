/**
 * @file lut.h
 * @brief LUT generation helpers for emissivity and redshift.
 *
 * Generates normalized 1D lookup tables in geometric units (r/rS).
 */

#ifndef PHYSICS_LUT_H
#define PHYSICS_LUT_H

#include "batch.h"
#include "constants.h"
#include "kerr.h"
#include "schwarzschild.h"
#include "thin_disk.h"
#include <algorithm>
#include <cmath>
#include <cstddef>
#include <vector>

namespace physics {

struct Lut1D {
  std::vector<float> values;
  float rMin = 0.0f; // in units of rS
  float rMax = 0.0f; // in units of rS
};

struct SpinRadiiLut {
  std::vector<float> spins;
  std::vector<float> rIscoOverRs;
  std::vector<float> rPhOverRs;
};

inline Lut1D generateEmissivityLut(int size, double massSolar, double aStar,
                                     double mdotEdd, bool prograde = true) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  const double mass = massSolar * M_SUN;
  const double rS = schwarzschildRadius(mass);
  const double rG = G * mass / C2;
  const double a = aStar * rG;
  const double rIn = kerrIscoRadius(mass, a, prograde);
  const double rOut = rIn * 4.0;

  DiskParams disk = kerrDisk(massSolar, aStar, mdotEdd, prograde);
  disk.rIn  = rIn;
  disk.rOut = rOut;

  lut.rMin = static_cast<float>(rIn / rS);
  lut.rMax = static_cast<float>(rOut / rS);
  std::vector<double> radii(static_cast<std::size_t>(size));
  fillLinspace(radii, rIn, rOut);
  diskFluxBatch(radii, disk, lut.values);

  double maxFlux = 0.0;
  for (float const v : lut.values) {
    maxFlux = std::max(maxFlux, static_cast<double>(v));
  }

  if (maxFlux > 0.0) {
    for (auto &v : lut.values) {
      v = static_cast<float>(static_cast<double>(v) / maxFlux);
    }
  }

  return lut;
}

inline Lut1D generateRedshiftLut(int size, double massSolar, double aStar,
                                   double theta = 0.5 * PI) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  const double mass = massSolar * M_SUN;
  const double rS = schwarzschildRadius(mass);
  const double rG = G * mass / C2;
  const double a = aStar * rG;
  const double rIn = kerrIscoRadius(mass, a, true);
  const double rOut = rIn * 4.0;

  lut.rMin = static_cast<float>(rIn / rS);
  lut.rMax = static_cast<float>(rOut / rS);
  std::vector<double> radii(static_cast<std::size_t>(size));
  fillLinspace(radii, rIn, rOut);
  kerrRedshiftBatch(radii, theta, mass, a, lut.values);

  return lut;
}

inline SpinRadiiLut generateSpinRadiiLut(int size, double massSolar,
                                            double spinMin = -0.99,
                                            double spinMax = 0.99) {
  SpinRadiiLut lut;
  if (size <= 1) {
    return lut;
  }

  spinMin = std::clamp(spinMin, -0.99, 0.99);
  spinMax = std::clamp(spinMax, -0.99, 0.99);
  if (spinMax <= spinMin) {
    spinMax = std::min(spinMin + 0.01, 0.99);
  }

  const double mass = massSolar * M_SUN;
  const double rS = schwarzschildRadius(mass);
  const double rG = G * mass / C2;

  lut.spins.resize(static_cast<std::size_t>(size));
  lut.rIscoOverRs.resize(static_cast<std::size_t>(size));
  lut.rPhOverRs.resize(static_cast<std::size_t>(size));

  for (int i = 0; i < size; ++i) {
    double const u = static_cast<double>(i) / (size - 1);
    double const spin = spinMin + (u * (spinMax - spinMin));
    double const a = spin * rG;
    bool const prograde = spin >= 0.0;
    double const rIsco = kerrIscoRadius(mass, a, prograde);
    double const rPh =
        prograde ? kerrPhotonOrbitPrograde(mass, a) : kerrPhotonOrbitRetrograde(mass, a);

    lut.spins.at(static_cast<std::size_t>(i)) = static_cast<float>(spin);
    lut.rIscoOverRs.at(static_cast<std::size_t>(i)) = static_cast<float>(rIsco / rS);
    lut.rPhOverRs.at(static_cast<std::size_t>(i)) = static_cast<float>(rPh / rS);
  }

  return lut;
}

/**
 * Generate photon sphere glow LUT (Phase 8.2 optimization).
 * Precomputes exp(-distance * 4.0) for distance in [0, 0.5].
 * Used to replace transcendental exp() computation in shader.
 */
inline Lut1D generatePhotonGlowLut(int size = 256) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  lut.rMin = 0.0f;
  lut.rMax = 0.5f;
  lut.values.resize(static_cast<std::size_t>(size));

  for (int i = 0; i < size; ++i) {
    double const u = static_cast<double>(i) / (size - 1);
    double const distance = u * 0.5; // distance in [0, 0.5]
    double const glowIntensity = std::exp(-distance * 4.0);
    lut.values.at(static_cast<std::size_t>(i)) = static_cast<float>(glowIntensity);
  }

  return lut;
}

/**
 * Generate accretion disk density profile LUT (Phase 8.2 Priority 2).
 * Precomputes normalized density as function of normalized radius.
 * Formula: density(r) = (1 - r)^power for r in [0, 1]
 * Replaces inline pow() and smoothstep() calculations in disk shader.
 */
inline Lut1D generateDiskDensityLut(int size = 256, double power = 1.5) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  lut.rMin = 0.0f;
  lut.rMax = 1.0f;
  lut.values.resize(static_cast<std::size_t>(size));

  for (int i = 0; i < size; ++i) {
    double const u = static_cast<double>(i) / (size - 1);
    // u=0 corresponds to inner radius (ISCO), u=1 to outer radius
    // density decreases smoothly from 1.0 to 0.0
    double const density = std::pow(1.0 - u, power);
    lut.values.at(static_cast<std::size_t>(i)) = static_cast<float>(density);
  }

  return lut;
}

} // namespace physics

#endif // PHYSICS_LUT_H
