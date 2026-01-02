/**
 * @file lut.h
 * @brief LUT generation helpers for emissivity and redshift.
 *
 * Generates normalized 1D lookup tables in geometric units (r/r_s).
 */

#ifndef PHYSICS_LUT_H
#define PHYSICS_LUT_H

#include "batch.h"
#include "kerr.h"
#include "schwarzschild.h"
#include "thin_disk.h"
#include <algorithm>
#include <cmath>
#include <limits>
#include <vector>

namespace physics {

struct Lut1D {
  std::vector<float> values;
  float r_min = 0.0f; // in units of r_s
  float r_max = 0.0f; // in units of r_s
};

struct SpinRadiiLut {
  std::vector<float> spins;
  std::vector<float> r_isco_over_rs;
  std::vector<float> r_ph_over_rs;
};

inline Lut1D generate_emissivity_lut(int size, double mass_solar, double a_star,
                                     double mdot_edd, bool prograde = true) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  const double mass = mass_solar * M_SUN;
  const double r_s = schwarzschild_radius(mass);
  const double r_g = G * mass / C2;
  const double a = a_star * r_g;
  const double r_in = kerr_isco_radius(mass, a, prograde);
  const double r_out = r_in * 4.0;

  DiskParams disk = kerr_disk(mass_solar, a_star, mdot_edd, prograde);
  disk.r_in = r_in;
  disk.r_out = r_out;

  lut.r_min = static_cast<float>(r_in / r_s);
  lut.r_max = static_cast<float>(r_out / r_s);
  std::vector<double> radii(static_cast<std::size_t>(size));
  fill_linspace(radii, r_in, r_out);
  disk_flux_batch(radii, disk, lut.values);

  double max_flux = 0.0;
  for (float v : lut.values) {
    max_flux = std::max(max_flux, static_cast<double>(v));
  }

  if (max_flux > 0.0) {
    for (auto &v : lut.values) {
      v = static_cast<float>(static_cast<double>(v) / max_flux);
    }
  }

  return lut;
}

inline Lut1D generate_redshift_lut(int size, double mass_solar, double a_star,
                                   double theta = 0.5 * PI) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  const double mass = mass_solar * M_SUN;
  const double r_s = schwarzschild_radius(mass);
  const double r_g = G * mass / C2;
  const double a = a_star * r_g;
  const double r_in = kerr_isco_radius(mass, a, true);
  const double r_out = r_in * 4.0;

  lut.r_min = static_cast<float>(r_in / r_s);
  lut.r_max = static_cast<float>(r_out / r_s);
  std::vector<double> radii(static_cast<std::size_t>(size));
  fill_linspace(radii, r_in, r_out);
  kerr_redshift_batch(radii, theta, mass, a, lut.values);

  return lut;
}

inline SpinRadiiLut generate_spin_radii_lut(int size, double mass_solar,
                                            double spin_min = -0.99,
                                            double spin_max = 0.99) {
  SpinRadiiLut lut;
  if (size <= 1) {
    return lut;
  }

  spin_min = std::clamp(spin_min, -0.99, 0.99);
  spin_max = std::clamp(spin_max, -0.99, 0.99);
  if (spin_max <= spin_min) {
    spin_max = std::min(spin_min + 0.01, 0.99);
  }

  const double mass = mass_solar * M_SUN;
  const double r_s = schwarzschild_radius(mass);
  const double r_g = G * mass / C2;

  lut.spins.resize(static_cast<std::size_t>(size));
  lut.r_isco_over_rs.resize(static_cast<std::size_t>(size));
  lut.r_ph_over_rs.resize(static_cast<std::size_t>(size));

  for (int i = 0; i < size; ++i) {
    double u = static_cast<double>(i) / (size - 1);
    double spin = spin_min + u * (spin_max - spin_min);
    double a = spin * r_g;
    bool prograde = spin >= 0.0;
    double r_isco = kerr_isco_radius(mass, a, prograde);
    double r_ph = prograde ? kerr_photon_orbit_prograde(mass, a)
                           : kerr_photon_orbit_retrograde(mass, a);

    lut.spins[static_cast<std::size_t>(i)] = static_cast<float>(spin);
    lut.r_isco_over_rs[static_cast<std::size_t>(i)] = static_cast<float>(r_isco / r_s);
    lut.r_ph_over_rs[static_cast<std::size_t>(i)] = static_cast<float>(r_ph / r_s);
  }

  return lut;
}

/**
 * Generate photon sphere glow LUT (Phase 8.2 optimization).
 * Precomputes exp(-distance * 4.0) for distance in [0, 0.5].
 * Used to replace transcendental exp() computation in shader.
 */
inline Lut1D generate_photon_glow_lut(int size = 256) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  lut.r_min = 0.0f;
  lut.r_max = 0.5f;
  lut.values.resize(static_cast<std::size_t>(size));

  for (int i = 0; i < size; ++i) {
    double u = static_cast<double>(i) / (size - 1);
    double distance = u * 0.5;  // distance in [0, 0.5]
    double glow_intensity = std::exp(-distance * 4.0);
    lut.values[static_cast<std::size_t>(i)] = static_cast<float>(glow_intensity);
  }

  return lut;
}

/**
 * Generate accretion disk density profile LUT (Phase 8.2 Priority 2).
 * Precomputes normalized density as function of normalized radius.
 * Formula: density(r) = (1 - r)^power for r in [0, 1]
 * Replaces inline pow() and smoothstep() calculations in disk shader.
 */
inline Lut1D generate_disk_density_lut(int size = 256, double power = 1.5) {
  Lut1D lut;
  if (size <= 1) {
    return lut;
  }

  lut.r_min = 0.0f;
  lut.r_max = 1.0f;
  lut.values.resize(static_cast<std::size_t>(size));

  for (int i = 0; i < size; ++i) {
    double u = static_cast<double>(i) / (size - 1);
    // u=0 corresponds to inner radius (ISCO), u=1 to outer radius
    // density decreases smoothly from 1.0 to 0.0
    double density = std::pow(1.0 - u, power);
    lut.values[static_cast<std::size_t>(i)] = static_cast<float>(density);
  }

  return lut;
}

} // namespace physics

#endif // PHYSICS_LUT_H
