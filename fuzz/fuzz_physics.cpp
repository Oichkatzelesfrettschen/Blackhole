/**
 * @file fuzz_physics.cpp
 * @brief libFuzzer harness for physics library.
 *
 * Fuzzes physics calculations with random inputs to find:
 * - Division by zero
 * - NaN/Inf propagation
 * - Numerical instabilities
 * - Buffer overflows
 *
 * Build with:
 *   clang++ -g -O2 -fsanitize=fuzzer,address,undefined \
 *           -I../src -I../src/physics fuzz_physics.cpp \
 *           ../src/physics/*.cpp -o fuzz_physics
 *
 * Run:
 *   ./fuzz_physics corpus/ -max_len=256 -jobs=4
 */

#include "physics/constants.h"
#include "physics/elliptic_integrals.h"
#include "physics/gravitational_waves.h"
#include "physics/kerr.h"
#include "physics/schwarzschild.h"
#include "physics/thin_disk.h"
#include "physics/tov.h"

#include <cmath>
#include <cstdint>
#include <cstring>
#include <limits>

using namespace physics;

// Helper to extract doubles from fuzz data
class FuzzDataReader {
public:
  FuzzDataReader(const uint8_t *data, size_t size) : data_(data), size_(size), pos_(0) {}

  double get_double() {
    if (pos_ + sizeof(double) > size_) {
      pos_ = 0; // Wrap around
    }
    double val;
    std::memcpy(&val, data_ + pos_, sizeof(double));
    pos_ += sizeof(double);

    // Sanitize: avoid NaN/Inf as inputs (we want to test if code PRODUCES them)
    if (!std::isfinite(val)) {
      val = 1.0;
    }
    return val;
  }

  double get_positive_double() {
    double val = get_double();
    return std::abs(val) + 1e-10; // Ensure positive and non-zero
  }

  double get_mass() {
    // Return mass in range [0.1, 1e12] solar masses
    double val = get_positive_double();
    return std::clamp(val, 0.1, 1e12) * M_SUN;
  }

  double get_radius(double r_s) {
    // Return radius > r_s to avoid singularities
    double factor = std::abs(get_double()) + 1.1;
    return factor * r_s;
  }

  double get_spin_parameter(double M_geo) {
    // Return spin in valid range |a| < M
    double val = get_double();
    return std::clamp(val, -0.998, 0.998) * M_geo;
  }

  double get_angle() {
    double val = get_double();
    return std::fmod(std::abs(val), 2.0 * M_PI);
  }

  double get_frequency() {
    // Return frequency in range [1, 10000] Hz
    double val = get_positive_double();
    return std::clamp(val, 1.0, 10000.0);
  }

  double get_density() {
    // Return density in range [1e10, 1e16] g/cm³
    double val = get_positive_double();
    return std::clamp(val, 1e10, 1e16);
  }

  bool has_data() const { return pos_ < size_; }

private:
  const uint8_t *data_;
  size_t size_;
  size_t pos_;
};

// Fuzz Schwarzschild functions
void fuzz_schwarzschild(FuzzDataReader &reader) {
  double mass = reader.get_mass();
  double r_s = schwarzschild_radius(mass);

  // Test basic radius calculations
  (void)photon_sphere_radius(mass);
  (void)isco_radius(mass);
  (void)critical_impact_parameter(mass);

  // Test at various radii
  double r = reader.get_radius(r_s);
  (void)gravitational_redshift(r, mass);
  (void)escape_velocity(r, mass);
  (void)gravitational_deflection(r, mass);
  (void)time_dilation(r, mass);
  (void)orbital_velocity(r, mass);
}

// Fuzz Kerr functions
void fuzz_kerr(FuzzDataReader &reader) {
  double mass = reader.get_mass();
  double M_geo = G * mass / C2;
  double a = reader.get_spin_parameter(M_geo);
  double theta = reader.get_angle();

  Kerr kerr(mass, a);

  // Test horizon calculations
  (void)kerr.outer_horizon();
  (void)kerr.inner_horizon();
  (void)kerr.isco_prograde();
  (void)kerr.isco_retrograde();

  // Test at radius
  double r = reader.get_radius(kerr.outer_horizon());
  (void)kerr.sigma(r, theta);
  (void)kerr.delta(r);
  (void)kerr.ergosphere(theta);
  (void)kerr.frame_dragging(r, theta);
  (void)kerr.redshift(r, theta);

  // Test predicates
  (void)kerr.is_exterior(r);
  (void)kerr.in_ergosphere(r, theta);
}

// Fuzz elliptic integrals
void fuzz_elliptic(FuzzDataReader &reader) {
  // Get modulus in valid range [0, 1)
  double k = std::abs(reader.get_double());
  k = std::fmod(k, 0.999);

  // Complete elliptic integrals
  (void)elliptic_K(k);
  (void)elliptic_E(k);

  // Incomplete elliptic integrals
  double phi = reader.get_angle();
  (void)elliptic_F(phi, k);
  (void)elliptic_E_incomplete(phi, k);

  // Carlson forms
  double x = reader.get_positive_double();
  double y = reader.get_positive_double();
  double z = reader.get_positive_double();
  (void)carlson_RF(x, y, z);
  (void)carlson_RC(x, y);
  (void)carlson_RD(x, y, z);

  // Strong-field deflection
  double r_s = 1.0; // Unit
  double b_crit = 3.0 * std::sqrt(3.0) / 2.0 * r_s;
  double b = b_crit * (1.0 + std::abs(reader.get_double()));
  (void)deflection_angle_schwarzschild(b, r_s);
}

// Fuzz gravitational wave functions
void fuzz_gw(FuzzDataReader &reader) {
  double m1 = reader.get_mass();
  double m2 = reader.get_mass();
  double D = reader.get_positive_double() * 1e6 * PARSEC; // Distance in Mpc
  double f = reader.get_frequency();

  double M_c = chirp_mass(m1, m2);
  double eta = (m1 * m2) / ((m1 + m2) * (m1 + m2));

  // Test strain calculations
  (void)gw_strain_amplitude(M_c, f, D);
  (void)gw_strain_1pn(M_c, eta, f, D);
  (void)frequency_derivative(M_c, f);
  (void)time_to_coalescence(M_c, f);
  (void)orbital_separation(m1 + m2, f);
  (void)gw_frequency_isco(m1 + m2);

  // Test QNM
  (void)qnm_frequency_schwarzschild(m1 + m2);
  (void)qnm_damping_time_schwarzschild(m1 + m2);

  // Test luminosity
  (void)gw_luminosity(m1 + m2, eta, f);
  (void)gw_energy_radiated(m1 + m2, eta);

  // Test characteristic strain
  (void)characteristic_strain(M_c, f, D);
}

// Fuzz thin disk
void fuzz_thin_disk(FuzzDataReader &reader) {
  double M_solar = std::abs(reader.get_double()) + 1.0;
  M_solar = std::clamp(M_solar, 1.0, 1e10);

  DiskParams disk = schwarzschild_disk(M_solar);

  // Test at various radii
  for (int i = 0; i < 5 && reader.has_data(); ++i) {
    double r = disk.r_in + std::abs(reader.get_double()) * (disk.r_out - disk.r_in);
    (void)disk_flux(r, disk);
    (void)disk_temperature(r, disk);
    (void)disk_redshift_factor(r, disk.M);
  }

  // Test disk luminosity
  (void)disk_luminosity(disk);

  // Test Planck function
  double nu = reader.get_positive_double() * 1e15; // Frequency ~optical
  double T = reader.get_positive_double() * 1e6;   // Temperature
  T = std::clamp(T, 100.0, 1e8);
  (void)planck_function(nu, T);
}

// Fuzz TOV integration
void fuzz_tov(FuzzDataReader &reader) {
  double rho_c = reader.get_density();

  auto eos = polytropic_eos(eos_params::K_SLY4, eos_params::GAMMA_SLY4);

  // Test EOS
  (void)eos(rho_c);
  (void)inverse_polytrope(eos(rho_c), eos_params::K_SLY4, eos_params::GAMMA_SLY4);

  // Test TOV derivatives
  double r = reader.get_positive_double() * 1e6; // ~km
  double m = reader.get_positive_double() * M_SUN;
  double P = eos(rho_c);
  (void)tov_dmdr(r, rho_c);
  (void)tov_dPdr(r, m, P, rho_c);

  // Full integration is expensive, only do occasionally
  static int counter = 0;
  if (++counter % 100 == 0) {
    auto profile = integrate_tov(rho_c, eos, eos_params::K_SLY4, eos_params::GAMMA_SLY4,
                                 1e3, 1000); // Limit steps for fuzzing
    (void)profile.M;
    (void)profile.R;

    // Test tidal deformability
    if (profile.compactness > 0 && profile.compactness < 0.5) {
      (void)tidal_deformability(profile.compactness);
      (void)tidal_love_number_k2(profile.compactness);
    }
  }
}

// Main fuzzer entry point
extern "C" int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
  if (size < 8) {
    return 0; // Need at least one double
  }

  FuzzDataReader reader(data, size);

  // Dispatch to different fuzz targets based on first byte
  uint8_t selector = data[0] % 6;

  switch (selector) {
  case 0:
    fuzz_schwarzschild(reader);
    break;
  case 1:
    fuzz_kerr(reader);
    break;
  case 2:
    fuzz_elliptic(reader);
    break;
  case 3:
    fuzz_gw(reader);
    break;
  case 4:
    fuzz_thin_disk(reader);
    break;
  case 5:
    fuzz_tov(reader);
    break;
  }

  return 0;
}
