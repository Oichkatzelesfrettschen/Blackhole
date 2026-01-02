/**
 * @file hawking_spectrum_test.cpp
 * @brief Unit tests for Hawking radiation spectrum calculations.
 *
 * Tests verify:
 * - Wien's displacement law: λ_peak × T = b (constant)
 * - Peak frequency formula: ν_peak = 2.821 k_B T / h
 * - Planck blackbody spectrum shape and normalization
 * - Temperature-to-wavelength mapping
 * - Spectrum consistency across different masses
 *
 * Phase 10.1: Hawking Radiation Thermal Glow
 * Created: 2026-01-02
 */

#include "physics/hawking.h"
#include "physics/constants.h"

#include <cmath>
#include <iostream>
#include <cstdlib>

// Tolerance for floating-point comparisons
static constexpr double TOLERANCE = 1e-10;
static constexpr double LOOSE_TOLERANCE = 1e-6;

static bool approx_eq(double a, double b, double tol = TOLERANCE) {
  if (std::isnan(a) && std::isnan(b))
    return true;
  if (std::isinf(a) && std::isinf(b) && (std::signbit(a) == std::signbit(b)))
    return true;
  return std::abs(a - b) <= tol * std::max(1.0, std::abs(b));
}

// Test: Wien's displacement law (λ_peak × T = constant)
static int test_wien_displacement_law() {
  std::cout << "Testing Wien's displacement law...\\n";

  // Wien displacement constant b = 2.898 × 10^-3 m·K = 0.2898 cm·K
  constexpr double b_wien = 0.2898;  // cm·K

  // Test for solar mass
  double M_sun = physics::M_SUN;
  double T_sun = physics::hawking_temperature(M_sun);
  double lambda_sun = physics::hawking_peak_wavelength(M_sun);
  double product_sun = lambda_sun * T_sun;

  if (!approx_eq(product_sun, b_wien, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Solar mass λ_peak × T = " << product_sun
              << " cm·K, expected " << b_wien << " cm·K\\n";
    return 1;
  }

  // Test for primordial mass
  double M_primordial = 5e14;  // ~5e14 g
  double T_primordial = physics::hawking_temperature(M_primordial);
  double lambda_primordial = physics::hawking_peak_wavelength(M_primordial);
  double product_primordial = lambda_primordial * T_primordial;

  if (!approx_eq(product_primordial, b_wien, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Primordial mass λ_peak × T = " << product_primordial
              << " cm·K, expected " << b_wien << " cm·K\\n";
    return 1;
  }

  std::cout << "  Solar mass: λ_peak = " << lambda_sun << " cm, T = " << T_sun << " K\\n";
  std::cout << "  Product: " << product_sun << " cm·K\\n";
  std::cout << "  Primordial: λ_peak = " << lambda_primordial << " cm, T = " << T_primordial << " K\\n";
  std::cout << "  Product: " << product_primordial << " cm·K\\n";
  std::cout << "  PASS: Wien's displacement law\\n";
  return 0;
}

// Test: Peak frequency formula (ν_peak = 2.821 k_B T / h)
static int test_peak_frequency() {
  std::cout << "Testing peak frequency formula...\\n";

  double M_test = 1e30;  // arbitrary test mass
  double T = physics::hawking_temperature(M_test);
  double nu_peak = physics::hawking_peak_frequency(M_test);

  // Expected: ν_peak = 2.821 k_B T / h
  double nu_expected = 2.821 * physics::K_B * T / (physics::TWO_PI * physics::HBAR);

  if (!approx_eq(nu_peak, nu_expected, TOLERANCE)) {
    std::cerr << "  FAIL: ν_peak = " << nu_peak
              << " Hz, expected " << nu_expected << " Hz\\n";
    return 1;
  }

  std::cout << "  Temperature: " << T << " K\\n";
  std::cout << "  Peak frequency: " << nu_peak << " Hz\\n";
  std::cout << "  PASS: Peak frequency formula\\n";
  return 0;
}

// Test: Wien displacement relationship (λ_peak × ν_peak ≈ c)
static int test_wavelength_frequency_relation() {
  std::cout << "Testing wavelength-frequency relation...\\n";

  double M_test = 1e32;  // arbitrary test mass
  double lambda_peak = physics::hawking_peak_wavelength(M_test);
  double nu_peak = physics::hawking_peak_frequency(M_test);

  // λ_peak × ν_peak should be close to c (within factor due to Wien peak definitions)
  double product = lambda_peak * nu_peak;
  double ratio = product / physics::C;

  // The ratio should be ~0.57 (Wien displacement for wavelength vs frequency peaks differ)
  if (ratio < 0.5 || ratio > 0.7) {
    std::cerr << "  FAIL: λ_peak × ν_peak / c = " << ratio
              << ", expected ~0.57\\n";
    return 1;
  }

  std::cout << "  λ_peak = " << lambda_peak << " cm\\n";
  std::cout << "  ν_peak = " << nu_peak << " Hz\\n";
  std::cout << "  λ_peak × ν_peak / c = " << ratio << "\\n";
  std::cout << "  PASS: Wavelength-frequency relation\\n";
  return 0;
}

// Test: Planck spectrum decreases away from peak
static int test_planck_spectrum_shape() {
  std::cout << "Testing Planck spectrum shape...\\n";

  double M_test = 1e30;
  double nu_peak = physics::hawking_peak_frequency(M_test);

  // Get spectrum at peak, below peak, and above peak
  double I_peak = physics::hawking_spectrum(nu_peak, M_test);
  double I_below = physics::hawking_spectrum(nu_peak * 0.5, M_test);
  double I_above = physics::hawking_spectrum(nu_peak * 2.0, M_test);

  // Peak should be larger than both sides
  if (I_peak <= I_below || I_peak <= I_above) {
    std::cerr << "  FAIL: Spectrum not peaked at ν_peak\\n";
    std::cerr << "  I(0.5 ν_peak) = " << I_below << "\\n";
    std::cerr << "  I(ν_peak) = " << I_peak << "\\n";
    std::cerr << "  I(2 ν_peak) = " << I_above << "\\n";
    return 1;
  }

  // Spectrum should be symmetric on log scale (approximately)
  // High-frequency side drops faster than low-frequency side
  if (I_above >= I_below) {
    std::cerr << "  FAIL: Spectrum asymmetry incorrect\\n";
    std::cerr << "  I(0.5 ν_peak) = " << I_below << " should be > I(2 ν_peak) = " << I_above << "\\n";
    return 1;
  }

  std::cout << "  I(0.5 ν_peak) = " << I_below << " erg/s/Hz\\n";
  std::cout << "  I(ν_peak) = " << I_peak << " erg/s/Hz\\n";
  std::cout << "  I(2 ν_peak) = " << I_above << " erg/s/Hz\\n";
  std::cout << "  PASS: Planck spectrum shape\\n";
  return 0;
}

// Test: Temperature scaling affects peak wavelength correctly
static int test_temperature_wavelength_scaling() {
  std::cout << "Testing temperature-wavelength scaling...\\n";

  double M1 = 1e30;
  double M2 = 2.0 * M1;  // Double the mass

  double T1 = physics::hawking_temperature(M1);
  double T2 = physics::hawking_temperature(M2);
  double lambda1 = physics::hawking_peak_wavelength(M1);
  double lambda2 = physics::hawking_peak_wavelength(M2);

  // Since T_H ∝ 1/M, we have T2 = T1/2
  // Since λ_peak ∝ 1/T, we have λ2 = 2 × λ1
  double lambda_ratio = lambda2 / lambda1;
  double expected_ratio = 2.0;

  if (!approx_eq(lambda_ratio, expected_ratio, TOLERANCE)) {
    std::cerr << "  FAIL: λ(2M) / λ(M) = " << lambda_ratio
              << ", expected " << expected_ratio << "\\n";
    return 1;
  }

  std::cout << "  T(M) = " << T1 << " K, λ(M) = " << lambda1 << " cm\\n";
  std::cout << "  T(2M) = " << T2 << " K, λ(2M) = " << lambda2 << " cm\\n";
  std::cout << "  Ratio λ(2M)/λ(M) = " << lambda_ratio << "\\n";
  std::cout << "  PASS: Temperature-wavelength scaling\\n";
  return 0;
}

// Test: Visible light wavelength range
static int test_visible_spectrum_range() {
  std::cout << "Testing visible spectrum range...\\n";

  // Visible light: 380-750 nm = 3.8e-5 to 7.5e-5 cm
  constexpr double lambda_red = 7.0e-5;   // 700 nm (red)
  constexpr double lambda_green = 5.5e-5; // 550 nm (green)
  constexpr double lambda_blue = 4.5e-5;  // 450 nm (blue)

  // Wien: λ_peak = b / T
  // For visible light, T = b / λ_peak
  constexpr double b_wien = 0.2898;  // cm·K

  double T_red = b_wien / lambda_red;      // ~4140 K
  double T_green = b_wien / lambda_green;  // ~5270 K
  double T_blue = b_wien / lambda_blue;    // ~6440 K

  // Find masses that emit at these temperatures
  // T_H = ℏc³/(8πGMk_B), so M = ℏc³/(8πGTk_B)
  auto mass_from_temp = [](double T) {
    return physics::HBAR * physics::C * physics::C * physics::C /
           (8.0 * physics::PI * physics::G * T * physics::K_B);
  };

  double M_red = mass_from_temp(T_red);
  double M_green = mass_from_temp(T_green);
  double M_blue = mass_from_temp(T_blue);

  // Verify consistency
  double T_red_check = physics::hawking_temperature(M_red);
  double lambda_red_check = physics::hawking_peak_wavelength(M_red);

  if (!approx_eq(T_red, T_red_check, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Red temperature mismatch: " << T_red
              << " vs " << T_red_check << "\\n";
    return 1;
  }

  if (!approx_eq(lambda_red, lambda_red_check, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Red wavelength mismatch: " << lambda_red
              << " vs " << lambda_red_check << "\\n";
    return 1;
  }

  std::cout << "  Red (700 nm): T = " << T_red << " K, M = " << M_red << " g\\n";
  std::cout << "  Green (550 nm): T = " << T_green << " K, M = " << M_green << " g\\n";
  std::cout << "  Blue (450 nm): T = " << T_blue << " K, M = " << M_blue << " g\\n";
  std::cout << "  PASS: Visible spectrum range\\n";
  return 0;
}

// Test: Spectrum at extreme temperatures
static int test_extreme_temperatures() {
  std::cout << "Testing extreme temperatures...\\n";

  // Very hot (primordial BH): T ~ 10^5 K
  double M_hot = 5e14;
  double T_hot = physics::hawking_temperature(M_hot);
  double lambda_hot = physics::hawking_peak_wavelength(M_hot);

  // Very cold (solar mass): T ~ 10^-8 K
  double M_cold = physics::M_SUN;
  double T_cold = physics::hawking_temperature(M_cold);
  double lambda_cold = physics::hawking_peak_wavelength(M_cold);

  // Hot BH should have short wavelength (X-rays)
  if (lambda_hot > 1e-6) {  // Shorter than 10 nm
    std::cerr << "  FAIL: Primordial BH wavelength too long: " << lambda_hot << " cm\\n";
    return 1;
  }

  // Cold BH should have long wavelength (radio waves)
  if (lambda_cold < 1e5) {  // Longer than 1 km
    std::cerr << "  FAIL: Solar mass BH wavelength too short: " << lambda_cold << " cm\\n";
    return 1;
  }

  std::cout << "  Primordial (hot): T = " << T_hot << " K, λ_peak = " << lambda_hot << " cm\\n";
  std::cout << "  Solar mass (cold): T = " << T_cold << " K, λ_peak = " << lambda_cold << " cm\\n";
  std::cout << "  PASS: Extreme temperatures\\n";
  return 0;
}

// Test: Spectrum integral (Stefan-Boltzmann law)
static int test_stefan_boltzmann_consistency() {
  std::cout << "Testing Stefan-Boltzmann consistency...\\n";

  double M_test = 1e30;
  double L_hawking = physics::hawking_luminosity(M_test);

  // Stefan-Boltzmann: L = σ A T⁴
  // where σ = 2π⁵k⁴/(15h³c²) in CGS
  double T = physics::hawking_temperature(M_test);
  double r_s = physics::schwarzschild_radius(M_test);
  double area = 4.0 * physics::PI * r_s * r_s;

  // Stefan-Boltzmann constant σ (CGS units)
  constexpr double sigma_sb = 5.6704e-5;  // erg/(cm²·s·K⁴)

  double L_stefan = sigma_sb * area * std::pow(T, 4);

  // These should match within a factor of ~π (greybody factors)
  double ratio = L_hawking / L_stefan;

  if (ratio < 0.1 || ratio > 10.0) {
    std::cerr << "  FAIL: Luminosity ratio out of range: " << ratio << "\\n";
    std::cerr << "  L_hawking = " << L_hawking << " erg/s\\n";
    std::cerr << "  L_stefan = " << L_stefan << " erg/s\\n";
    return 1;
  }

  std::cout << "  L_hawking = " << L_hawking << " erg/s\\n";
  std::cout << "  L_stefan-boltzmann = " << L_stefan << " erg/s\\n";
  std::cout << "  Ratio = " << ratio << "\\n";
  std::cout << "  PASS: Stefan-Boltzmann consistency\\n";
  return 0;
}

int main() {
  std::cout << "=== Hawking Radiation Spectrum Tests ===\\n\\n";

  int result = 0;

  result |= test_wien_displacement_law();
  result |= test_peak_frequency();
  result |= test_wavelength_frequency_relation();
  result |= test_planck_spectrum_shape();
  result |= test_temperature_wavelength_scaling();
  result |= test_visible_spectrum_range();
  result |= test_extreme_temperatures();
  result |= test_stefan_boltzmann_consistency();

  std::cout << "\\n";
  if (result == 0) {
    std::cout << "All Hawking spectrum tests PASSED\\n";
  } else {
    std::cout << "Some Hawking spectrum tests FAILED\\n";
  }

  return result;
}
