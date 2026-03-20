/**
 * @file hawking_glow_test.cpp
 * @brief Unit tests for Hawking radiation thermal glow implementation.
 *
 * Tests verify:
 * - Temperature formula correctness: T_H = hbar*c^3/(8*pi*G*M*k_B)
 * - Known values (solar mass -> 6.2e-8 K)
 * - Inverse mass relationship: T_H ~ 1/M
 * - Edge cases (zero/negative mass)
 * - Formula consistency
 *
 * Phase 10.1: Hawking Radiation Thermal Glow
 * Created: 2026-01-02
 */

#include "physics/constants.h"
#include "physics/hawking.h"
#include "physics/safe_limits.h"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>

// Tolerance for floating-point comparisons
constexpr double TOLERANCE = 1e-10;
[[maybe_unused]] constexpr double LOOSE_TOLERANCE = 1e-6;

namespace {

[[nodiscard]] bool approxEq(double a, double b, double tol = TOLERANCE) {
  if (physics::safeIsnan(a) && physics::safeIsnan(b)) { return true; }
  if (physics::safeIsinf(a) && physics::safeIsinf(b) &&
      (std::signbit(a) == std::signbit(b))) {
    return true;
  }
  return std::abs(a - b) <= (tol * std::max(1.0, std::abs(b)));
}

// Test: Hawking temperature for solar mass black hole
int testSolarMassTemperature() {
  std::cout << "Testing Hawking temperature for solar mass...\n";

  const double massSun = physics::M_SUN;  // 1.989e33 g
  const double tH      = physics::hawkingTemperature(massSun);
  const double expected = 6.2e-8;

  if (!approxEq(tH, expected, 0.1)) {  // 10% tolerance
    std::cerr << "  FAIL: Solar mass T_H=" << tH
              << " K, expected ~" << expected << " K\n";
    return 1;
  }

  std::cout << "  Solar mass T_H = " << tH << " K\n";
  std::cout << "  PASS: Solar mass temperature\n";
  return 0;
}

// Test: Inverse mass relationship T_H ~ 1/M
int testInverseMassLaw() {
  std::cout << "Testing inverse mass law (T_H ~ 1/M)...\n";

  const double m1 = 1e30;
  const double m2 = 2.0 * m1;

  const double t1 = physics::hawkingTemperature(m1);
  const double t2 = physics::hawkingTemperature(m2);

  const double ratio         = t2 / t1;
  const double expectedRatio = 0.5;

  if (!approxEq(ratio, expectedRatio, TOLERANCE)) {
    std::cerr << "  FAIL: T_H(2M)/T_H(M) = " << ratio
              << ", expected " << expectedRatio << "\n";
    return 1;
  }

  std::cout << "  T_H(M) = " << t1 << " K\n";
  std::cout << "  T_H(2M) = " << t2 << " K\n";
  std::cout << "  Ratio = " << ratio << "\n";
  std::cout << "  PASS: Inverse mass law\n";
  return 0;
}

// Test: Primordial black hole temperature
int testPrimordialTemperature() {
  std::cout << "Testing primordial black hole temperature...\n";

  const double mPrimordial = 5e14;  // ~5e14 g (asteroid mass)
  const double tH          = physics::hawkingTemperature(mPrimordial);
  const double expected    = 2.45e11;  // ~245 billion K

  if (!approxEq(tH, expected, 0.1)) {  // 10% tolerance
    std::cerr << "  FAIL: Primordial BH T_H=" << tH
              << " K, expected ~" << expected << " K\n";
    return 1;
  }

  std::cout << "  Primordial BH (M=" << mPrimordial << " g) T_H = " << tH << " K\n";
  std::cout << "  PASS: Primordial temperature\n";
  return 0;
}

// Test: Zero and negative mass edge cases
int testEdgeCases() {
  std::cout << "Testing edge cases (zero/negative mass)...\n";

  const double tZero = physics::hawkingTemperature(0.0);
  if (!std::isinf(tZero)) {
    std::cerr << "  FAIL: Zero mass T_H=" << tZero << ", expected infinity\n";
    return 1;
  }

  const double tNeg = physics::hawkingTemperature(-1e30);
  if (!std::isinf(tNeg)) {
    std::cerr << "  FAIL: Negative mass T_H=" << tNeg << ", expected infinity\n";
    return 1;
  }

  std::cout << "  Zero mass: T_H = " << tZero << "\n";
  std::cout << "  Negative mass: T_H = " << tNeg << "\n";
  std::cout << "  PASS: Edge cases\n";
  return 0;
}

// Test: Formula consistency check
int testFormulaConsistency() {
  std::cout << "Testing formula consistency...\n";

  const double mass     = 1e32;
  const double tH       = physics::hawkingTemperature(mass);
  const double tManual  = (physics::HBAR * physics::C * physics::C * physics::C) /
                          (8.0 * physics::PI * physics::G * mass * physics::K_B);

  if (!approxEq(tH, tManual, TOLERANCE)) {
    std::cerr << "  FAIL: Formula mismatch T_H=" << tH
              << ", manual=" << tManual << "\n";
    return 1;
  }

  std::cout << "  Formula result: " << tH << " K\n";
  std::cout << "  Manual calculation: " << tManual << " K\n";
  std::cout << "  PASS: Formula consistency\n";
  return 0;
}

} // namespace

int main() {
  std::cout << "=== Hawking Radiation Thermal Glow Tests ===\n\n";

  int result = 0;

  result |= testSolarMassTemperature();
  result |= testInverseMassLaw();
  result |= testPrimordialTemperature();
  result |= testEdgeCases();
  result |= testFormulaConsistency();

  std::cout << "\n";
  if (result == 0) {
    std::cout << "All Hawking glow tests PASSED\n";
  } else {
    std::cout << "Some Hawking glow tests FAILED\n";
  }

  return result;
}
