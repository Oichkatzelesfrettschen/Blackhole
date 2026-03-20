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

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>
#include <numbers>
#include <random>

#include "constants.h"
#include "physics/constants.h"
#include "physics/coordinates.h"
#include "physics/safe_limits.h"

// Tolerance for floating-point comparisons
constexpr double TOLERANCE = 1e-12;

namespace {

bool approxEq(double a, double b, double tol = TOLERANCE) {
  if (physics::safeIsnan(a) && physics::safeIsnan(b)) {
    return true;
  }
  if (physics::safeIsinf(a) && physics::safeIsinf(b) && (std::signbit(a) == std::signbit(b))) {
    return true;
  }
  return std::abs(a - b) <= tol * std::max(1.0, std::abs(b));
}

// Test radial coordinate roundtrip: X_of_r(r_of_X(X1)) == X1
int testRadialRoundtrip() {
  std::cout << "Testing radial coordinate roundtrip...\n";

  std::vector<double> const testX1 = {-5.0, -2.0, -1.0, 0.0, 1.0, 2.0, 5.0, 10.0};
  std::vector<double> const testR0 = {0.5, 1.0, 2.0, 10.0};

  for (double const r0 : testR0) {
    for (double const x1 : testX1) {
      double const r = physics::rOfX(x1, r0);
      double const x1Back = physics::xOfR(r, r0);

      if (!approxEq(x1, x1Back)) {
        std::cerr << "  FAIL: R0=" << r0 << " X1=" << x1 << " -> r=" << r
                  << " -> X1_back=" << x1Back << "\n";
        return 1;
      }
    }
  }

  std::cout << "  PASS: Radial roundtrip\n";
  return 0;
}

// Test dr/dX1 derivative
int testRadialDerivative() {
  std::cout << "Testing radial derivative dr/dX1...\n";

  // dr/dX1 = r for exponential mapping
  std::vector<double> const testX1 = {-2.0, -1.0, 0.0, 1.0, 2.0, 3.0};
  std::vector<double> const testR0 = {0.5, 1.0, 2.0};

  for (double const r0 : testR0) {
    for (double const x1 : testX1) {
      double const r = physics::rOfX(x1, r0);
      double const drDx = physics::drDX1(x1, r0);

      // For r = R0 * exp(X1), dr/dX1 = r
      if (!approxEq(drDx, r)) {
        std::cerr << "  FAIL: R0=" << r0 << " X1=" << x1 << " dr_dX1=" << drDx << " expected=" << r
                  << "\n";
        return 1;
      }
    }
  }

  std::cout << "  PASS: Radial derivative\n";
  return 0;
}

// Test theta coordinate mapping
int testThetaMapping() {
  std::cout << "Testing theta coordinate mapping...\n";

  // Test boundary values
  // X2=0 -> theta ~ 0 (clamped to 1e-10)
  // X2=0.5 -> theta = pi/2
  // X2=1 -> theta ~ pi (clamped to pi - 1e-10)

  double const theta0 = physics::thOfX(0.0, 0.0);
  double const thetaHalf = physics::thOfX(0.5, 0.0);
  double const theta1 = physics::thOfX(1.0, 0.0);

  if (!approxEq(theta0, 1e-10)) {
    std::cerr << "  FAIL: th_of_X(0) = " << theta0 << " expected ~0\n";
    return 1;
  }

  if (!approxEq(thetaHalf, physics::PI / 2.0)) {
    std::cerr << "  FAIL: th_of_X(0.5) = " << thetaHalf << " expected pi/2\n";
    return 1;
  }

  if (!approxEq(theta1, physics::PI - 1e-10)) {
    std::cerr << "  FAIL: th_of_X(1) = " << theta1 << " expected ~pi\n";
    return 1;
  }

  std::cout << "  PASS: Theta mapping boundaries\n";
  return 0;
}

// Test theta derefining parameter effect
int testThetaDerefining() {
  std::cout << "Testing theta derefining (hslope)...\n";

  // When hslope=0: theta = pi * X2
  // When hslope=1: theta = pi * X2 (no derefining term)
  // When hslope=0.5: theta = pi * X2 + 0.25 * sin(2*pi*X2)

  // At X2=0.5 (equator), sin(2*pi*X2) = 0, so all hslope values give pi/2
  for (double const hslope : {0.0, 0.3, 0.5, 1.0}) {
    double const theta = physics::thOfX(0.5, hslope);
    if (!approxEq(theta, physics::PI / 2.0, 1e-10)) {
      std::cerr << "  FAIL: th_of_X(0.5, " << hslope << ") = " << theta
                << " expected pi/2\n";
      return 1;
    }
  }

  // At X2=0.25, sin(2*pi*X2) = 1, so derefining has maximal effect
  double const thetaH0 = physics::thOfX(0.25, 0.0);
  double const thetaH1 = physics::thOfX(0.25, 1.0);

  // hslope=0: theta = pi*0.25 + 0.5 * 1 = pi/4 + 0.5 ~ 1.285
  // hslope=1: theta = pi*0.25 + 0 = pi/4 ~ 0.785
  double const expectedH0 = (physics::PI * 0.25) + 0.5;
  double const expectedH1 = physics::PI * 0.25;

  if (!approxEq(thetaH0, expectedH0, 1e-10)) {
    std::cerr << "  FAIL: th_of_X(0.25, 0) = " << thetaH0 << " expected " << expectedH0 << "\n";
    return 1;
  }

  if (!approxEq(thetaH1, expectedH1, 1e-10)) {
    std::cerr << "  FAIL: th_of_X(0.25, 1) = " << thetaH1 << " expected " << expectedH1 << "\n";
    return 1;
  }

  std::cout << "  PASS: Theta derefining\n";
  return 0;
}

// Test dtheta/dX2 derivative
int testThetaDerivative() {
  std::cout << "Testing theta derivative dtheta/dX2...\n";

  // For hslope=1: dtheta/dX2 = pi (constant, no derefining)
  for (double const x2 : {0.0, 0.25, 0.5, 0.75, 1.0}) {
    double const dth = physics::dthDX2(x2, 1.0);
    if (!approxEq(dth, physics::PI, 1e-10)) {
      std::cerr << "  FAIL: dth_dX2(" << x2 << ", 1) = " << dth << " expected pi\n";
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
    double x2;
    double expected;
  };
  std::vector<DerivTest> const h0Tests = {
      {.x2 = 0.0, .expected = 2.0 * physics::PI},
      {.x2 = 0.25, .expected = physics::PI},
      {.x2 = 0.5, .expected = 0.0},
      {.x2 = 0.75, .expected = physics::PI},
      {.x2 = 1.0, .expected = 2.0 * physics::PI},
  };
  for (const auto &t : h0Tests) {
    double const dth = physics::dthDX2(t.x2, 0.0);
    if (!approxEq(dth, t.expected, 1e-10)) {
      std::cerr << "  FAIL: dth_dX2(" << t.x2 << ", 0) = " << dth << " expected " << t.expected
                << "\n";
      return 1;
    }
  }

  // For intermediate hslope=0.5, check at X2=0.25 where cos(2*pi*X2) = 0
  // dth = pi * (1 + 0.5 * 0) = pi
  double const dth = physics::dthDX2(0.25, 0.5);
  if (!approxEq(dth, physics::PI, 1e-10)) {
    std::cerr << "  FAIL: dth_dX2(0.25, 0.5) = " << dth << " expected pi\n";
    return 1;
  }

  std::cout << "  PASS: Theta derivative\n";
  return 0;
}

// Test bl_coord full transformation
int testBlCoord() {
  std::cout << "Testing bl_coord full transformation...\n";

  physics::MKSParams params;
  params.r0 = 1.0;
  params.hslope = 0.0;

  // Test a set of code coordinates
  struct TestCase {
    double x1, x2, x3;
    double expectedR, expectedTheta, expectedPhi;
  };

  std::vector<TestCase> const cases = {
      // X1=0 -> r=1, X2=0.5 -> theta=pi/2, X3=0 -> phi=0
      {.x1 = 0.0,
       .x2 = 0.5,
       .x3 = 0.0,
       .expectedR = 1.0,
       .expectedTheta = physics::PI / 2.0,
       .expectedPhi = 0.0},
      // X1=log(10) -> r=10
      {.x1 = std::numbers::ln10,
       .x2 = 0.5,
       .x3 = physics::PI,
       .expectedR = 10.0,
       .expectedTheta = physics::PI / 2.0,
       .expectedPhi = physics::PI},
      // X2=0.25 -> theta=pi/4 + 0.5 (with hslope=0)
      {.x1 = 0.0,
       .x2 = 0.25,
       .x3 = 0.0,
       .expectedR = 1.0,
       .expectedTheta = (physics::PI * 0.25) + 0.5,
       .expectedPhi = 0.0},
  };

  for (const auto &tc : cases) {
    auto bl = physics::blCoord(tc.x1, tc.x2, tc.x3, params);

    if (!approxEq(bl.r, tc.expectedR, 1e-10)) {
      std::cerr << "  FAIL: bl_coord r=" << bl.r << " expected " << tc.expectedR << "\n";
      return 1;
    }
    if (!approxEq(bl.theta, tc.expectedTheta, 1e-10)) {
      std::cerr << "  FAIL: bl_coord theta=" << bl.theta << " expected " << tc.expectedTheta
                << "\n";
      return 1;
    }
    if (!approxEq(bl.phi, tc.expectedPhi, 1e-10)) {
      std::cerr << "  FAIL: bl_coord phi=" << bl.phi << " expected " << tc.expectedPhi << "\n";
      return 1;
    }
  }

  std::cout << "  PASS: bl_coord transformation\n";
  return 0;
}

// Test Cartesian<->spherical roundtrip
int testCartesianSphericalRoundtrip() {
  std::cout << "Testing Cartesian<->spherical roundtrip...\n";

  std::mt19937 rng(42); // NOLINT(cert-msc32-c,cert-msc51-cpp,bugprone-random-generator-seed) -- deterministic seed for reproducible test
  std::uniform_real_distribution<double> distR(0.1, 100.0);
  std::uniform_real_distribution<double> distTheta(0.1, physics::PI - 0.1);
  std::uniform_real_distribution<double> distPhi(0.0, 2.0 * physics::PI);

  for (int i = 0; i < 100; ++i) {
    double const r = distR(rng);
    double const theta = distTheta(rng);
    double const phi = distPhi(rng);

    auto cart = physics::sphericalToCartesian(r, theta, phi);
    auto sph = physics::cartesianToSpherical(cart[0], cart[1], cart[2]);

    if (!approxEq(sph.r, r, 1e-10)) {
      std::cerr << "  FAIL: r roundtrip " << r << " -> " << sph.r << "\n";
      return 1;
    }
    if (!approxEq(sph.theta, theta, 1e-10)) {
      std::cerr << "  FAIL: theta roundtrip " << theta << " -> " << sph.theta
                << "\n";
      return 1;
    }
    // phi may wrap around, check modulo 2*pi
    double phiDiff = std::abs(sph.phi - phi);
    if (phiDiff > physics::PI) {
      phiDiff = (2.0 * physics::PI) - phiDiff;
    }
    if (phiDiff > 1e-10) {
      std::cerr << "  FAIL: phi roundtrip " << phi << " -> " << sph.phi << "\n";
      return 1;
    }
  }

  std::cout << "  PASS: Cartesian<->spherical roundtrip\n";
  return 0;
}

// Test edge cases at poles
int testPolarEdgeCases() {
  std::cout << "Testing polar edge cases...\n";

  // At z-axis (theta=0), phi is undefined but should not cause issues
  auto sphNorth = physics::cartesianToSpherical(0.0, 0.0, 10.0);
  if (!approxEq(sphNorth.r, 10.0, 1e-10)) {
    std::cerr << "  FAIL: North pole r=" << sphNorth.r << " expected 10\n";
    return 1;
  }
  if (!approxEq(sphNorth.theta, 0.0, 1e-10)) {
    std::cerr << "  FAIL: North pole theta=" << sphNorth.theta << " expected 0\n";
    return 1;
  }

  auto sphSouth = physics::cartesianToSpherical(0.0, 0.0, -10.0);
  if (!approxEq(sphSouth.r, 10.0, 1e-10)) {
    std::cerr << "  FAIL: South pole r=" << sphSouth.r << " expected 10\n";
    return 1;
  }
  if (!approxEq(sphSouth.theta, physics::PI, 1e-10)) {
    std::cerr << "  FAIL: South pole theta=" << sphSouth.theta << " expected pi\n";
    return 1;
  }

  // Origin should return r=0
  auto sphOrigin = physics::cartesianToSpherical(0.0, 0.0, 0.0);
  if (!approxEq(sphOrigin.r, 0.0, 1e-30)) {
    std::cerr << "  FAIL: Origin r=" << sphOrigin.r << " expected 0\n";
    return 1;
  }

  std::cout << "  PASS: Polar edge cases\n";
  return 0;
}

// Test MKS parameter struct defaults
int testMksParamsDefaults() {
  std::cout << "Testing MKSParams defaults...\n";

  physics::MKSParams const params;
  if (!approxEq(params.r0, 1.0, 1e-10)) {
    std::cerr << "  FAIL: Default R0=" << params.r0 << " expected 1.0\n";
    return 1;
  }
  if (!approxEq(params.hslope, 0.0, 1e-10)) {
    std::cerr << "  FAIL: Default hslope=" << params.hslope
              << " expected 0.0\n";
    return 1;
  }

  std::cout << "  PASS: MKSParams defaults\n";
  return 0;
}

} // namespace

int main() {
  std::cout << "=== Coordinate Transformation Tests ===\n\n";

  int result = 0;

  result |= testRadialRoundtrip();
  result |= testRadialDerivative();
  result |= testThetaMapping();
  result |= testThetaDerefining();
  result |= testThetaDerivative();
  result |= testBlCoord();
  result |= testCartesianSphericalRoundtrip();
  result |= testPolarEdgeCases();
  result |= testMksParamsDefaults();

  std::cout << "\n";
  if (result == 0) {
    std::cout << "All coordinate tests PASSED\n";
  } else {
    std::cout << "Some coordinate tests FAILED\n";
  }

  return result;
}
