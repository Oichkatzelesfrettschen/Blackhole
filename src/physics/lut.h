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

/** @brief 1D float lookup table with radial domain in units of r_s. */
struct Lut1D {
  std::vector<float> values;
  float rMin = 0.0f; ///< Inner radius in units of r_s
  float rMax = 0.0f; ///< Outer radius in units of r_s
};

/** @brief Lookup table mapping spin values to ISCO and photon-sphere radii. */
struct SpinRadiiLut {
  std::vector<float> spins;        ///< Dimensionless spin a* values
  std::vector<float> rIscoOverRs;  ///< ISCO radius in units of r_s
  std::vector<float> rPhOverRs;    ///< Photon-sphere radius in units of r_s
};

/**
 * @brief Generate a normalized disk emissivity LUT for a Kerr black hole.
 *
 * Computes the Novikov-Thorne flux profile from r_ISCO to 4*r_ISCO,
 * then normalizes to [0, 1] by the peak flux value.
 *
 * @param size       Number of LUT samples
 * @param massSolar  Black hole mass [solar masses]
 * @param aStar      Dimensionless spin a* in (-1, 1)
 * @param mdotEdd    Eddington-scaled accretion rate
 * @param prograde   True for prograde orbits (default)
 * @return Lut1D with normalized emissivity values
 */
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

/**
 * @brief Generate a gravitational redshift LUT for a Kerr black hole.
 *
 * Samples the Kerr redshift factor from r_ISCO to 4*r_ISCO along
 * a geodesic at inclination angle theta.
 *
 * @param size       Number of LUT samples
 * @param massSolar  Black hole mass [solar masses]
 * @param aStar      Dimensionless spin a* in (-1, 1)
 * @param theta      Observer inclination angle [rad] (default pi/2, equatorial)
 * @return Lut1D with redshift values
 */
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

/**
 * @brief Generate a spin-radii LUT mapping a* to ISCO and photon-sphere radii.
 *
 * Sweeps spin from spinMin to spinMax and records r_ISCO/r_s and r_ph/r_s
 * for each value.  Used by the shader to look up orbital radii without
 * recomputing at runtime.
 *
 * @param size      Number of spin samples
 * @param massSolar Black hole mass [solar masses]
 * @param spinMin   Minimum spin value (clamped to [-0.99, 0.99])
 * @param spinMax   Maximum spin value (clamped to [-0.99, 0.99])
 * @return SpinRadiiLut with per-spin ISCO and photon-sphere radii
 */
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
 * @brief Generate a photon-sphere glow LUT.
 *
 * Precomputes exp(-distance * 4.0) for distance in [0, 0.5].
 * Used to replace the transcendental exp() call in the photon-glow shader path.
 *
 * @param size Number of samples (default 256)
 * @return Lut1D with glow intensity values in [0, 1]
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
 * @brief Generate a normalized accretion disk density profile LUT.
 *
 * Precomputes density(r) = (1 - r)^power for normalized radius r in [0, 1],
 * where r=0 is the ISCO and r=1 is the outer disk edge.
 * Replaces inline pow() and smoothstep() calculations in the disk shader.
 *
 * @param size  Number of samples (default 256)
 * @param power Falloff exponent (default 1.5)
 * @return Lut1D with density values decreasing from 1 to 0
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
