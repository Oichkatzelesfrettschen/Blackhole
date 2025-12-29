/**
 * physics_test.cpp
 * Validation tests for physics library calculations.
 *
 * Compares cleanroom C++ implementation against known reference values.
 * Reference: OpenUniverse compact domain physics formulas.
 *
 * To build and run:
 *   g++ -std=c++17 -I../.. physics_test.cpp schwarzschild.cpp geodesics.cpp cosmology.cpp -o physics_test && ./physics_test
 */

#include "constants.h"
#include "cosmology.h"
#include "geodesics.h"
#include "schwarzschild.h"

#include <cmath>
#include <iomanip>
#include <iostream>
#include <string>

namespace {

constexpr double TOLERANCE = 1e-10;

bool approx_equal(double a, double b, double tol = TOLERANCE) {
  if (std::abs(b) < 1e-30) {
    return std::abs(a) < tol;
  }
  return std::abs(a - b) / std::abs(b) < tol;
}

struct TestResult {
  std::string name;
  double expected;
  double actual;
  bool passed;
};

void print_result(const TestResult &r) {
  std::cout << (r.passed ? "[PASS]" : "[FAIL]") << " " << r.name << "\n"
            << "  Expected: " << std::scientific << std::setprecision(10)
            << r.expected << "\n"
            << "  Actual:   " << r.actual << "\n";
  if (!r.passed) {
    double rel_err = std::abs(r.actual - r.expected) / std::abs(r.expected);
    std::cout << "  Rel.Err:  " << rel_err << "\n";
  }
  std::cout << "\n";
}

int run_tests() {
  int passed = 0;
  int failed = 0;

  std::cout << "=== Physics Library Validation Tests ===\n\n";

  // Test 1: Schwarzschild radius for 1 solar mass
  // r_s = 2GM/c^2 = 2 * 6.67430e-8 * 1.98841e33 / (2.99792458e10)^2
  // r_s = 2.95325e5 cm = 2.95325 km
  {
    double mass = physics::M_SUN; // 1 solar mass in grams
    double r_s = physics::schwarzschild_radius(mass);
    double expected = 2.9532500765e5; // cm (verified value)

    TestResult r{"Schwarzschild radius (1 M_sun)", expected, r_s,
                 approx_equal(r_s, expected, 1e-6)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 2: Schwarzschild radius for 4 million solar masses (Sgr A*)
  // This is the supermassive black hole at the center of our galaxy
  {
    double mass = 4.0e6 * physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double expected = 1.1813e12; // cm (~0.08 AU)

    TestResult r{"Schwarzschild radius (4e6 M_sun, Sgr A*)", expected, r_s,
                 approx_equal(r_s, expected, 1e-4)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 3: Photon sphere radius = 1.5 * r_s
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r_ph = physics::photon_sphere_radius(mass);
    double expected = 1.5 * r_s;

    TestResult r{"Photon sphere radius = 1.5 r_s", expected, r_ph,
                 approx_equal(r_ph, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 4: ISCO radius = 3 * r_s (for Schwarzschild)
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r_isco = physics::isco_radius(mass);
    double expected = 3.0 * r_s;

    TestResult r{"ISCO radius = 3 r_s", expected, r_isco,
                 approx_equal(r_isco, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 5: Gravitational redshift at r = 2 r_s (just above horizon)
  // z = 1/sqrt(1 - r_s/r) - 1 = 1/sqrt(1/2) - 1 = sqrt(2) - 1 ~ 0.414
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r = 2.0 * r_s;
    double z = physics::gravitational_redshift(r, mass);
    double expected = std::sqrt(2.0) - 1.0;

    TestResult r_test{"Gravitational redshift at r=2r_s", expected, z,
                      approx_equal(z, expected)};
    print_result(r_test);
    r_test.passed ? ++passed : ++failed;
  }

  // Test 6: Gravitational redshift at r = 10 r_s
  // z = 1/sqrt(1 - 0.1) - 1 = 1/sqrt(0.9) - 1 ~ 0.0541
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r = 10.0 * r_s;
    double z = physics::gravitational_redshift(r, mass);
    double expected = 1.0 / std::sqrt(0.9) - 1.0;

    TestResult r_test{"Gravitational redshift at r=10r_s", expected, z,
                      approx_equal(z, expected)};
    print_result(r_test);
    r_test.passed ? ++passed : ++failed;
  }

  // Test 7: Critical impact parameter for photon capture
  // b_crit = sqrt(27) * r_s / 2 ~ 2.598 * r_s
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double b_crit = physics::critical_impact_parameter(mass);
    double expected = std::sqrt(27.0) * r_s / 2.0;

    TestResult r{"Critical impact parameter", expected, b_crit,
                 approx_equal(b_crit, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 8: Escape velocity at r = 2 r_s
  // v_esc = c * sqrt(r_s/r) = c * sqrt(1/2) ~ 0.707 c
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r = 2.0 * r_s;
    double v_esc = physics::escape_velocity(r, mass);
    double expected = physics::C * std::sqrt(0.5);

    TestResult r_test{"Escape velocity at r=2r_s", expected, v_esc,
                      approx_equal(v_esc, expected)};
    print_result(r_test);
    r_test.passed ? ++passed : ++failed;
  }

  // Test 9: Light deflection angle for large impact parameter
  // delta_phi ~ 4GM/(b*c^2) for b >> r_s
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double b = 1000.0 * r_s; // Far from black hole
    double delta_phi = physics::gravitational_deflection(b, mass);
    double expected = 2.0 * r_s / b; // First-order approximation

    TestResult r{"Light deflection (weak field)", expected, delta_phi,
                 approx_equal(delta_phi, expected, 1e-3)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 10: Hubble parameter E(z=0) should equal 1
  {
    double E = physics::hubble_E(0.0);
    double expected = 1.0;

    TestResult r{"Hubble E(z=0) = 1", expected, E, approx_equal(E, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Summary
  std::cout << "=== Summary ===\n";
  std::cout << "Passed: " << passed << "/" << (passed + failed) << "\n";
  std::cout << "Failed: " << failed << "/" << (passed + failed) << "\n";

  return failed;
}

} // namespace

int main() { return run_tests(); }
