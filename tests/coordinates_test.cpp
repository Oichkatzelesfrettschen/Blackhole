/**
 * @file coordinates_test.cpp
 * @brief Validation tests for coordinate transformation functions.
 *
 * Tests verify:
 * - Inverse transform correctness: X_of_r(r_of_X(x)) == x
 * - Derefining parameter behavior for theta mapping
 * - Cartesian/spherical roundtrip accuracy
 * - Edge cases at polar singularities
 */

#include "physics/coordinates.h"

#include <cmath>
#include <cstdlib>
#include <iostream>
#include <random>
#include <vector>

// Tolerance for floating-point comparisons
static constexpr double TOLERANCE = 1e-12;

static bool approx_eq(double a, double b, double tol = TOLERANCE) {
  if (std::isnan(a) && std::isnan(b))
    return true;
  if (std::isinf(a) && std::isinf(b) && (std::signbit(a) == std::signbit(b)))
    return true;
  return std::abs(a - b) <= tol * std::max(1.0, std::abs(b));
}

// Test radial coordinate roundtrip: X_of_r(r_of_X(X1)) == X1
static int test_radial_roundtrip() {
  std::cout << "Testing radial coordinate roundtrip...\n";

  std::vector<double> test_X1 = {-5.0, -2.0, -1.0, 0.0, 1.0, 2.0, 5.0, 10.0};
  std::vector<double> test_R0 = {0.5, 1.0, 2.0, 10.0};

  for (double R0 : test_R0) {
    for (double X1 : test_X1) {
      double r = physics::r_of_X(X1, R0);
      double X1_back = physics::X_of_r(r, R0);

      if (!approx_eq(X1, X1_back)) {
        std::cerr << "  FAIL: R0=" << R0 << " X1=" << X1 << " -> r=" << r
                  << " -> X1_back=" << X1_back << "\n";
        return 1;
      }
    }
  }

  std::cout << "  PASS: Radial roundtrip\n";
  return 0;
}

// Test dr/dX1 derivative
static int test_radial_derivative() {
  std::cout << "Testing radial derivative dr/dX1...\n";

  // dr/dX1 = r for exponential mapping
  std::vector<double> test_X1 = {-2.0, -1.0, 0.0, 1.0, 2.0, 3.0};
  std::vector<double> test_R0 = {0.5, 1.0, 2.0};

  for (double R0 : test_R0) {
    for (double X1 : test_X1) {
      double r = physics::r_of_X(X1, R0);
      double dr_dx = physics::dr_dX1(X1, R0);

      // For r = R0 * exp(X1), dr/dX1 = r
      if (!approx_eq(dr_dx, r)) {
        std::cerr << "  FAIL: R0=" << R0 << " X1=" << X1 << " dr_dX1=" << dr_dx
                  << " expected=" << r << "\n";
        return 1;
      }
    }
  }

  std::cout << "  PASS: Radial derivative\n";
  return 0;
}

// Test theta coordinate mapping
static int test_theta_mapping() {
  std::cout << "Testing theta coordinate mapping...\n";

  // Test boundary values
  // X2=0 -> theta ~ 0 (clamped to 1e-10)
  // X2=0.5 -> theta = pi/2
  // X2=1 -> theta ~ pi (clamped to pi - 1e-10)

  double theta_0 = physics::th_of_X(0.0, 0.0);
  double theta_half = physics::th_of_X(0.5, 0.0);
  double theta_1 = physics::th_of_X(1.0, 0.0);

  if (!approx_eq(theta_0, 1e-10)) {
    std::cerr << "  FAIL: th_of_X(0) = " << theta_0 << " expected ~0\n";
    return 1;
  }

  if (!approx_eq(theta_half, physics::PI / 2.0)) {
    std::cerr << "  FAIL: th_of_X(0.5) = " << theta_half
              << " expected pi/2\n";
    return 1;
  }

  if (!approx_eq(theta_1, physics::PI - 1e-10)) {
    std::cerr << "  FAIL: th_of_X(1) = " << theta_1 << " expected ~pi\n";
    return 1;
  }

  std::cout << "  PASS: Theta mapping boundaries\n";
  return 0;
}

// Test theta derefining parameter effect
static int test_theta_derefining() {
  std::cout << "Testing theta derefining (hslope)...\n";

  // When hslope=0: theta = pi * X2
  // When hslope=1: theta = pi * X2 (no derefining term)
  // When hslope=0.5: theta = pi * X2 + 0.25 * sin(2*pi*X2)

  // At X2=0.5 (equator), sin(2*pi*X2) = 0, so all hslope values give pi/2
  for (double hslope : {0.0, 0.3, 0.5, 1.0}) {
    double theta = physics::th_of_X(0.5, hslope);
    if (!approx_eq(theta, physics::PI / 2.0, 1e-10)) {
      std::cerr << "  FAIL: th_of_X(0.5, " << hslope << ") = " << theta
                << " expected pi/2\n";
      return 1;
    }
  }

  // At X2=0.25, sin(2*pi*X2) = 1, so derefining has maximal effect
  double theta_h0 = physics::th_of_X(0.25, 0.0);
  double theta_h1 = physics::th_of_X(0.25, 1.0);

  // hslope=0: theta = pi*0.25 + 0.5 * 1 = pi/4 + 0.5 ~ 1.285
  // hslope=1: theta = pi*0.25 + 0 = pi/4 ~ 0.785
  double expected_h0 = physics::PI * 0.25 + 0.5;
  double expected_h1 = physics::PI * 0.25;

  if (!approx_eq(theta_h0, expected_h0, 1e-10)) {
    std::cerr << "  FAIL: th_of_X(0.25, 0) = " << theta_h0
              << " expected " << expected_h0 << "\n";
    return 1;
  }

  if (!approx_eq(theta_h1, expected_h1, 1e-10)) {
    std::cerr << "  FAIL: th_of_X(0.25, 1) = " << theta_h1
              << " expected " << expected_h1 << "\n";
    return 1;
  }

  std::cout << "  PASS: Theta derefining\n";
  return 0;
}

// Test dtheta/dX2 derivative
static int test_theta_derivative() {
  std::cout << "Testing theta derivative dtheta/dX2...\n";

  // For hslope=1: dtheta/dX2 = pi (constant, no derefining)
  for (double X2 : {0.0, 0.25, 0.5, 0.75, 1.0}) {
    double dth = physics::dth_dX2(X2, 1.0);
    if (!approx_eq(dth, physics::PI, 1e-10)) {
      std::cerr << "  FAIL: dth_dX2(" << X2 << ", 1) = " << dth
                << " expected pi\n";
      return 1;
    }
  }

  // For hslope=0: dtheta/dX2 = pi * (1 + cos(2*pi*X2)) varies with X2
  // At X2=0:    cos(0) = 1,     dth = pi * 2 = 2*pi
  // At X2=0.25: cos(pi/2) = 0,  dth = pi * 1 = pi
  // At X2=0.5:  cos(pi) = -1,   dth = pi * 0 = 0
  // At X2=0.75: cos(3pi/2) = 0, dth = pi * 1 = pi
  // At X2=1:    cos(2pi) = 1,   dth = pi * 2 = 2*pi
  struct DerivTest {
    double X2;
    double expected;
  };
  std::vector<DerivTest> h0_tests = {
      {0.0, 2.0 * physics::PI},
      {0.25, physics::PI},
      {0.5, 0.0},
      {0.75, physics::PI},
      {1.0, 2.0 * physics::PI},
  };
  for (const auto &t : h0_tests) {
    double dth = physics::dth_dX2(t.X2, 0.0);
    if (!approx_eq(dth, t.expected, 1e-10)) {
      std::cerr << "  FAIL: dth_dX2(" << t.X2 << ", 0) = " << dth
                << " expected " << t.expected << "\n";
      return 1;
    }
  }

  // For intermediate hslope=0.5, check at X2=0.25 where cos(2*pi*X2) = 0
  // dth = pi * (1 + 0.5 * 0) = pi
  double dth = physics::dth_dX2(0.25, 0.5);
  if (!approx_eq(dth, physics::PI, 1e-10)) {
    std::cerr << "  FAIL: dth_dX2(0.25, 0.5) = " << dth << " expected pi\n";
    return 1;
  }

  std::cout << "  PASS: Theta derivative\n";
  return 0;
}

// Test bl_coord full transformation
static int test_bl_coord() {
  std::cout << "Testing bl_coord full transformation...\n";

  physics::MKSParams params;
  params.R0 = 1.0;
  params.hslope = 0.0;

  // Test a set of code coordinates
  struct TestCase {
    double X1, X2, X3;
    double expected_r, expected_theta, expected_phi;
  };

  std::vector<TestCase> cases = {
      // X1=0 -> r=1, X2=0.5 -> theta=pi/2, X3=0 -> phi=0
      {0.0, 0.5, 0.0, 1.0, physics::PI / 2.0, 0.0},
      // X1=log(10) -> r=10
      {std::log(10.0), 0.5, physics::PI, 10.0, physics::PI / 2.0, physics::PI},
      // X2=0.25 -> theta=pi/4 + 0.5 (with hslope=0)
      {0.0, 0.25, 0.0, 1.0, physics::PI * 0.25 + 0.5, 0.0},
  };

  for (const auto &tc : cases) {
    auto bl = physics::bl_coord(tc.X1, tc.X2, tc.X3, params);

    if (!approx_eq(bl.r, tc.expected_r, 1e-10)) {
      std::cerr << "  FAIL: bl_coord r=" << bl.r << " expected "
                << tc.expected_r << "\n";
      return 1;
    }
    if (!approx_eq(bl.theta, tc.expected_theta, 1e-10)) {
      std::cerr << "  FAIL: bl_coord theta=" << bl.theta << " expected "
                << tc.expected_theta << "\n";
      return 1;
    }
    if (!approx_eq(bl.phi, tc.expected_phi, 1e-10)) {
      std::cerr << "  FAIL: bl_coord phi=" << bl.phi << " expected "
                << tc.expected_phi << "\n";
      return 1;
    }
  }

  std::cout << "  PASS: bl_coord transformation\n";
  return 0;
}

// Test Cartesian<->spherical roundtrip
static int test_cartesian_spherical_roundtrip() {
  std::cout << "Testing Cartesian<->spherical roundtrip...\n";

  std::mt19937 rng(42);
  std::uniform_real_distribution<double> dist_r(0.1, 100.0);
  std::uniform_real_distribution<double> dist_theta(0.1, physics::PI - 0.1);
  std::uniform_real_distribution<double> dist_phi(0.0, 2.0 * physics::PI);

  for (int i = 0; i < 100; ++i) {
    double r = dist_r(rng);
    double theta = dist_theta(rng);
    double phi = dist_phi(rng);

    auto cart = physics::spherical_to_cartesian(r, theta, phi);
    auto sph = physics::cartesian_to_spherical(cart[0], cart[1], cart[2]);

    if (!approx_eq(sph.r, r, 1e-10)) {
      std::cerr << "  FAIL: r roundtrip " << r << " -> " << sph.r << "\n";
      return 1;
    }
    if (!approx_eq(sph.theta, theta, 1e-10)) {
      std::cerr << "  FAIL: theta roundtrip " << theta << " -> " << sph.theta
                << "\n";
      return 1;
    }
    // phi may wrap around, check modulo 2*pi
    double phi_diff = std::abs(sph.phi - phi);
    if (phi_diff > physics::PI) {
      phi_diff = 2.0 * physics::PI - phi_diff;
    }
    if (phi_diff > 1e-10) {
      std::cerr << "  FAIL: phi roundtrip " << phi << " -> " << sph.phi << "\n";
      return 1;
    }
  }

  std::cout << "  PASS: Cartesian<->spherical roundtrip\n";
  return 0;
}

// Test edge cases at poles
static int test_polar_edge_cases() {
  std::cout << "Testing polar edge cases...\n";

  // At z-axis (theta=0), phi is undefined but should not cause issues
  auto sph_north = physics::cartesian_to_spherical(0.0, 0.0, 10.0);
  if (!approx_eq(sph_north.r, 10.0, 1e-10)) {
    std::cerr << "  FAIL: North pole r=" << sph_north.r << " expected 10\n";
    return 1;
  }
  if (!approx_eq(sph_north.theta, 0.0, 1e-10)) {
    std::cerr << "  FAIL: North pole theta=" << sph_north.theta
              << " expected 0\n";
    return 1;
  }

  auto sph_south = physics::cartesian_to_spherical(0.0, 0.0, -10.0);
  if (!approx_eq(sph_south.r, 10.0, 1e-10)) {
    std::cerr << "  FAIL: South pole r=" << sph_south.r << " expected 10\n";
    return 1;
  }
  if (!approx_eq(sph_south.theta, physics::PI, 1e-10)) {
    std::cerr << "  FAIL: South pole theta=" << sph_south.theta
              << " expected pi\n";
    return 1;
  }

  // Origin should return r=0
  auto sph_origin = physics::cartesian_to_spherical(0.0, 0.0, 0.0);
  if (!approx_eq(sph_origin.r, 0.0, 1e-30)) {
    std::cerr << "  FAIL: Origin r=" << sph_origin.r << " expected 0\n";
    return 1;
  }

  std::cout << "  PASS: Polar edge cases\n";
  return 0;
}

// Test MKS parameter struct defaults
static int test_mks_params_defaults() {
  std::cout << "Testing MKSParams defaults...\n";

  physics::MKSParams params;
  if (!approx_eq(params.R0, 1.0, 1e-10)) {
    std::cerr << "  FAIL: Default R0=" << params.R0 << " expected 1.0\n";
    return 1;
  }
  if (!approx_eq(params.hslope, 0.0, 1e-10)) {
    std::cerr << "  FAIL: Default hslope=" << params.hslope
              << " expected 0.0\n";
    return 1;
  }

  std::cout << "  PASS: MKSParams defaults\n";
  return 0;
}

int main() {
  std::cout << "=== Coordinate Transformation Tests ===\n\n";

  int result = 0;

  result |= test_radial_roundtrip();
  result |= test_radial_derivative();
  result |= test_theta_mapping();
  result |= test_theta_derefining();
  result |= test_theta_derivative();
  result |= test_bl_coord();
  result |= test_cartesian_spherical_roundtrip();
  result |= test_polar_edge_cases();
  result |= test_mks_params_defaults();

  std::cout << "\n";
  if (result == 0) {
    std::cout << "All coordinate tests PASSED\n";
  } else {
    std::cout << "Some coordinate tests FAILED\n";
  }

  return result;
}
