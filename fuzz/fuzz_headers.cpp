/**
 * @file fuzz_headers.cpp
 * @brief libFuzzer harness for header-only physics templates.
 *
 * Tests template instantiation with edge-case types and values.
 *
 * Build with:
 *   clang++ -g -O2 -fsanitize=fuzzer,address,undefined \
 *           -I../src -I../src/physics fuzz_headers.cpp \
 *           ../src/physics/schwarzschild.cpp \
 *           ../src/physics/geodesics.cpp \
 *           ../src/physics/cosmology.cpp \
 *           -o fuzz_headers
 */

#include "physics/constants.h"
#include "physics/doppler.h"
#include "physics/elliptic_integrals.h"
#include "physics/hawking.h"
#include "physics/kerr.h"
#include "physics/penrose.h"
#include "physics/raytracer.h"
#include "physics/schwarzschild.h"
#include "physics/synchrotron.h"
#include "physics/thin_disk.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <limits>

using namespace physics;

// Helper to extract values from fuzz data
class FuzzReader {
public:
  FuzzReader(const uint8_t *data, size_t size) : data_(data), size_(size), pos_(0) {}

  double next_double() {
    if (pos_ + sizeof(double) > size_) pos_ = 0;
    double val;
    std::memcpy(&val, data_ + pos_, sizeof(double));
    pos_ += sizeof(double);
    if (!std::isfinite(val)) val = 1.0;
    return val;
  }

  double positive() {
    return std::abs(next_double()) + 1e-30;
  }

  double fraction() {
    return std::fmod(std::abs(next_double()), 1.0);
  }

  double angle() {
    return std::fmod(std::abs(next_double()), 2.0 * M_PI);
  }

  double velocity_fraction() {
    // β in [0, 0.9999] to avoid γ → ∞
    return std::clamp(std::abs(next_double()), 0.0, 0.9999);
  }

private:
  const uint8_t *data_;
  size_t size_;
  size_t pos_;
};

// Fuzz Doppler module
void fuzz_doppler(FuzzReader &r) {
  double beta = r.velocity_fraction();
  double theta = r.angle();
  double nu_emit = r.positive() * 1e15; // ~optical frequency
  double z = r.positive() * 10.0;       // redshift

  // Lorentz factor
  (void)lorentz_factor(beta);

  // Doppler factor
  (void)doppler_factor(beta, theta);

  // Relativistic Doppler shift
  (void)doppler_shift_relativistic(nu_emit, beta, theta);

  // Beaming
  (void)relativistic_beaming_intensity(1.0, beta, theta, 3.0);

  // Aberration
  (void)relativistic_aberration(theta, beta);

  // Cosmological redshift
  (void)observed_frequency(nu_emit, z);
  (void)k_correction_power_law(1.0, z, -0.7);
}

// Fuzz synchrotron module
void fuzz_synchrotron(FuzzReader &r) {
  double gamma_e = r.positive() * 1e6; // Electron Lorentz factor
  double B = r.positive() * 1e3;       // Magnetic field [G]
  double nu = r.positive() * 1e15;     // Frequency [Hz]
  double p = 2.0 + r.fraction();       // Power-law index

  // Characteristic frequency
  (void)synchrotron_frequency_critical(gamma_e, B);

  // Power radiated
  (void)synchrotron_power_single_electron(gamma_e, B);

  // Cooling time
  (void)synchrotron_cooling_time(gamma_e, B);

  // Spectrum shape
  double x = nu / (synchrotron_frequency_critical(gamma_e, B) + 1e-30);
  (void)synchrotron_F(x);
  (void)synchrotron_G(x);

  // Power-law distribution
  double nu_min = r.positive() * 1e9;
  double nu_max = nu_min * 1e6;
  (void)synchrotron_spectrum_power_law(nu, B, gamma_e, 1e6 * gamma_e, p);
}

// Fuzz Penrose process
void fuzz_penrose(FuzzReader &r) {
  double mass = r.positive() * 1e6 * M_SUN;
  double a_star = r.fraction() * 0.998;

  Kerr kerr = Kerr::from_dimensionless_spin(mass, a_star);

  // Ergosphere properties
  double theta = r.angle();
  (void)kerr.ergosphere(theta);
  (void)kerr.in_ergosphere(kerr.outer_horizon() * 1.5, theta);

  // Penrose energy extraction
  double E_in = r.positive();
  double L_in = r.next_double();
  auto result = penrose_process_energy_extraction(kerr, E_in, L_in);
  (void)result.E_out;
  (void)result.efficiency;

  // Maximum efficiency
  (void)penrose_maximum_efficiency(a_star);

  // Blandford-Znajek power
  double B_field = r.positive() * 1e4;
  (void)blandford_znajek_power(mass, a_star, B_field);
}

// Fuzz Hawking radiation
void fuzz_hawking(FuzzReader &r) {
  double mass = r.positive() * M_SUN;

  // Temperature
  (void)hawking_temperature(mass);

  // Luminosity
  (void)hawking_luminosity(mass);

  // Evaporation time
  (void)hawking_evaporation_time(mass);

  // Peak wavelength
  (void)hawking_peak_wavelength(mass);

  // Entropy
  (void)bekenstein_hawking_entropy(mass);

  // Information paradox related
  (void)page_time(mass);
  (void)scrambling_time(mass);
}

// Fuzz raytracer
void fuzz_raytracer(FuzzReader &r) {
  double mass = r.positive() * 1e6 * M_SUN;
  double r_s = schwarzschild_radius(mass);

  // Initial conditions: position outside horizon
  double r0 = r_s * (2.0 + r.positive() * 100.0);
  double theta0 = r.angle();
  double phi0 = r.angle();

  // Initial direction
  double theta_dir = r.angle();
  double phi_dir = r.angle();

  // Create ray
  PhotonRay ray;
  ray.position = {r0, theta0, phi0};
  ray.direction = {std::sin(theta_dir) * std::cos(phi_dir),
                   std::sin(theta_dir) * std::sin(phi_dir),
                   std::cos(theta_dir)};
  ray.frequency = r.positive() * 1e15;
  ray.status = RayStatus::PROPAGATING;

  // Trace (limited steps for fuzzing)
  SchwarzschildRaytracer tracer(mass);
  tracer.set_max_steps(100);
  tracer.set_step_size(r_s * 0.1);

  auto result = tracer.trace(ray);
  (void)result.final_position[0];
  (void)result.steps_taken;
  (void)result.redshift;
}

// Main entry point
extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size < 16) return 0;

  FuzzReader reader(data, size);
  uint8_t selector = data[0] % 5;

  switch (selector) {
  case 0: fuzz_doppler(reader); break;
  case 1: fuzz_synchrotron(reader); break;
  case 2: fuzz_penrose(reader); break;
  case 3: fuzz_hawking(reader); break;
  case 4: fuzz_raytracer(reader); break;
  }

  return 0;
}
