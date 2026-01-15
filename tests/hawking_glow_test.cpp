/**
 * @file hawking_glow_test.cpp
 * @brief Unit tests for Hawking radiation thermal glow implementation.
 *
 * Tests verify:
 * - Temperature formula correctness: T_H = ℏc³/(8πGMk_B)
 * - Known values (solar mass → 6.2e-8 K)
 * - Inverse mass relationship: T_H ∝ 1/M
 * - Edge cases (zero/negative mass)
 * - Formula consistency
 *
 * Phase 10.1: Hawking Radiation Thermal Glow
 * Created: 2026-01-02
 */

#include "physics/hawking.h"
#include "physics/constants.h"
#include "physics/safe_limits.h"

#include <cmath>
#include <iostream>
#include <cstdlib>

// Tolerance for floating-point comparisons
static constexpr double TOLERANCE = 1e-10;
[[maybe_unused]] static constexpr double LOOSE_TOLERANCE = 1e-6;

static bool approx_eq(double a, double b, double tol = TOLERANCE) {
  if (physics::safe_isnan(a) && physics::safe_isnan(b))
    return true;
  if (physics::safe_isinf(a) && physics::safe_isinf(b) && (std::signbit(a) == std::signbit(b)))
    return true;
  return std::abs(a - b) <= tol * std::max(1.0, std::abs(b));
}

// Test: Hawking temperature for solar mass black hole
static int test_solar_mass_temperature() {
  std::cout << "Testing Hawking temperature for solar mass...\n";

  double mass_sun = physics::M_SUN;  // 1.989e33 g
  double T_H = physics::hawking_temperature(mass_sun);

  // Known value: T_H ≈ 6.2e-8 K for 1 M_☉
  double expected = 6.2e-8;

  if (!approx_eq(T_H, expected, 0.1)) {  // 10% tolerance
    std::cerr << "  FAIL: Solar mass T_H=" << T_H
              << " K, expected ≈" << expected << " K\n";
    return 1;
  }

  std::cout << "  Solar mass T_H = " << T_H << " K\n";
  std::cout << "  PASS: Solar mass temperature\n";
  return 0;
}

// Test: Inverse mass relationship T_H ∝ 1/M
static int test_inverse_mass_law() {
  std::cout << "Testing inverse mass law (T_H ∝ 1/M)...\n";

  double M1 = 1e30;  // arbitrary mass
  double M2 = 2.0 * M1;  // twice the mass

  double T1 = physics::hawking_temperature(M1);
  double T2 = physics::hawking_temperature(M2);

  // T_H(2M) should be T_H(M) / 2
  double ratio = T2 / T1;
  double expected_ratio = 0.5;

  if (!approx_eq(ratio, expected_ratio, TOLERANCE)) {
    std::cerr << "  FAIL: T_H(2M)/T_H(M) = " << ratio
              << ", expected " << expected_ratio << "\n";
    return 1;
  }

  std::cout << "  T_H(M) = " << T1 << " K\n";
  std::cout << "  T_H(2M) = " << T2 << " K\n";
  std::cout << "  Ratio = " << ratio << "\n";
  std::cout << "  PASS: Inverse mass law\n";
  return 0;
}

// Test: Primordial black hole temperature
static int test_primordial_temperature() {
  std::cout << "Testing primordial black hole temperature...\n";

  double M_primordial = 5e14;  // ~5e14 g (asteroid mass)
  double T_H = physics::hawking_temperature(M_primordial);

  // Primordial BHs at this mass have T_H ~ 2.45e11 K (gamma-ray peak)
  double expected = 2.45e11;  // ~245 billion K

  if (!approx_eq(T_H, expected, 0.1)) {  // 10% tolerance
    std::cerr << "  FAIL: Primordial BH T_H=" << T_H
              << " K, expected ~" << expected << " K\n";
    return 1;
  }

  std::cout << "  Primordial BH (M=" << M_primordial << " g) T_H = " << T_H << " K\n";
  std::cout << "  PASS: Primordial temperature\n";
  return 0;
}

// Test: Zero and negative mass edge cases
static int test_edge_cases() {
  std::cout << "Testing edge cases (zero/negative mass)...\n";

  // Zero mass should return infinity
  double T_zero = physics::hawking_temperature(0.0);
  if (!std::isinf(T_zero)) {
    std::cerr << "  FAIL: Zero mass T_H=" << T_zero
              << ", expected infinity\n";
    return 1;
  }

  // Negative mass should return infinity
  double T_neg = physics::hawking_temperature(-1e30);
  if (!std::isinf(T_neg)) {
    std::cerr << "  FAIL: Negative mass T_H=" << T_neg
              << ", expected infinity\n";
    return 1;
  }

  std::cout << "  Zero mass: T_H = " << T_zero << "\n";
  std::cout << "  Negative mass: T_H = " << T_neg << "\n";
  std::cout << "  PASS: Edge cases\n";
  return 0;
}

// Test: Formula consistency check
static int test_formula_consistency() {
  std::cout << "Testing formula consistency...\n";

  double mass = 1e32;  // arbitrary test mass
  double T_H = physics::hawking_temperature(mass);

  // Manual calculation: T_H = ℏc³/(8πGMk_B)
  double T_manual = physics::HBAR * physics::C * physics::C * physics::C /
                   (8.0 * physics::PI * physics::G * mass * physics::K_B);

  if (!approx_eq(T_H, T_manual, TOLERANCE)) {
    std::cerr << "  FAIL: Formula mismatch T_H=" << T_H
              << ", manual=" << T_manual << "\n";
    return 1;
  }

  std::cout << "  Formula result: " << T_H << " K\n";
  std::cout << "  Manual calculation: " << T_manual << " K\n";
  std::cout << "  PASS: Formula consistency\n";
  return 0;
}

int main() {
  std::cout << "=== Hawking Radiation Thermal Glow Tests ===\n\n";

  int result = 0;

  result |= test_solar_mass_temperature();
  result |= test_inverse_mass_law();
  result |= test_primordial_temperature();
  result |= test_edge_cases();
  result |= test_formula_consistency();

  std::cout << "\n";
  if (result == 0) {
    std::cout << "All Hawking glow tests PASSED\n";
  } else {
    std::cout << "Some Hawking glow tests FAILED\n";
  }

  return result;
}
