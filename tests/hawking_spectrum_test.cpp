/**
 * @file hawking_spectrum_test.cpp
 * @brief Unit tests for Hawking radiation spectrum calculations.
 *
 * Tests verify:
 * - Wien's displacement law: lambda_peak * T = b (constant)
 * - Peak frequency formula: nu_peak = 2.821 k_B T / h
 * - Planck blackbody spectrum shape and normalization
 * - Temperature-to-wavelength mapping
 * - Spectrum consistency across different masses
 *
 * Phase 10.1: Hawking Radiation Thermal Glow
 * Created: 2026-01-02
 */

#include "physics/constants.h"
#include "physics/hawking.h"
#include "physics/schwarzschild.h"

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <iostream>

// Tolerance for floating-point comparisons
constexpr double TOLERANCE = 1e-10;
constexpr double LOOSE_TOLERANCE = 1e-6;

namespace {

[[nodiscard]] bool approxEq(double a, double b, double tol = TOLERANCE) {
  if (std::isnan(a) && std::isnan(b)) { return true; }
  if (std::isinf(a) && std::isinf(b) && (std::signbit(a) == std::signbit(b))) {
    return true;
  }
  return std::abs(a - b) <= (tol * std::max(1.0, std::abs(b)));
}

// Test: Wien's displacement law (lambda_peak * T = constant)
int testWienDisplacementLaw() {
  std::cout << "Testing Wien's displacement law...\n";

  constexpr double bWien = 0.2898;  // cm*K

  const double mSun       = physics::M_SUN;
  const double tSun       = physics::hawkingTemperature(mSun);
  const double lambdaSun  = physics::hawkingPeakWavelength(mSun);
  const double productSun = lambdaSun * tSun;

  if (!approxEq(productSun, bWien, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Solar mass lambda_peak * T = " << productSun
              << " cm*K, expected " << bWien << " cm*K\n";
    return 1;
  }

  const double mPrimordial       = 5e14;  // ~5e14 g
  const double tPrimordial       = physics::hawkingTemperature(mPrimordial);
  const double lambdaPrimordial  = physics::hawkingPeakWavelength(mPrimordial);
  const double productPrimordial = lambdaPrimordial * tPrimordial;

  if (!approxEq(productPrimordial, bWien, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Primordial mass lambda_peak * T = " << productPrimordial
              << " cm*K, expected " << bWien << " cm*K\n";
    return 1;
  }

  std::cout << "  Solar mass: lambda_peak = " << lambdaSun << " cm, T = " << tSun << " K\n";
  std::cout << "  Product: " << productSun << " cm*K\n";
  std::cout << "  Primordial: lambda_peak = " << lambdaPrimordial
            << " cm, T = " << tPrimordial << " K\n";
  std::cout << "  Product: " << productPrimordial << " cm*K\n";
  std::cout << "  PASS: Wien's displacement law\n";
  return 0;
}

// Test: Peak frequency formula (nu_peak = 2.821 k_B T / h)
int testPeakFrequency() {
  std::cout << "Testing peak frequency formula...\n";

  const double mTest       = 1e30;
  const double tVal        = physics::hawkingTemperature(mTest);
  const double nuPeak      = physics::hawkingPeakFrequency(mTest);
  const double nuExpected  = (2.821 * physics::K_B * tVal) / (physics::TWO_PI * physics::HBAR);

  if (!approxEq(nuPeak, nuExpected, TOLERANCE)) {
    std::cerr << "  FAIL: nu_peak = " << nuPeak
              << " Hz, expected " << nuExpected << " Hz\n";
    return 1;
  }

  std::cout << "  Temperature: " << tVal << " K\n";
  std::cout << "  Peak frequency: " << nuPeak << " Hz\n";
  std::cout << "  PASS: Peak frequency formula\n";
  return 0;
}

// Test: Wien displacement relationship (lambda_peak * nu_peak ~= c)
int testWavelengthFrequencyRelation() {
  std::cout << "Testing wavelength-frequency relation...\n";

  const double mTest    = 1e32;
  const double lambdaPk = physics::hawkingPeakWavelength(mTest);
  const double nuPk     = physics::hawkingPeakFrequency(mTest);

  const double product = lambdaPk * nuPk;
  const double ratio   = product / physics::C;

  // The ratio should be ~0.57 (Wien displacement for wavelength vs frequency peaks differ)
  if ((ratio < 0.5) || (ratio > 0.7)) {
    std::cerr << "  FAIL: lambda_peak * nu_peak / c = " << ratio
              << ", expected ~0.57\n";
    return 1;
  }

  std::cout << "  lambda_peak = " << lambdaPk << " cm\n";
  std::cout << "  nu_peak = " << nuPk << " Hz\n";
  std::cout << "  lambda_peak * nu_peak / c = " << ratio << "\n";
  std::cout << "  PASS: Wavelength-frequency relation\n";
  return 0;
}

// Test: Planck spectrum decreases away from peak
int testPlanckSpectrumShape() {
  std::cout << "Testing Planck spectrum shape...\n";

  const double mTest  = 1e30;
  const double nuPeak = physics::hawkingPeakFrequency(mTest);

  const double iPeak  = physics::hawkingSpectrum(nuPeak, mTest);
  const double iBelow = physics::hawkingSpectrum(nuPeak * 0.5, mTest);
  const double iAbove = physics::hawkingSpectrum(nuPeak * 2.0, mTest);

  if ((iPeak <= iBelow) || (iPeak <= iAbove)) {
    std::cerr << "  FAIL: Spectrum not peaked at nu_peak\n";
    std::cerr << "  I(0.5 nu_peak) = " << iBelow << "\n";
    std::cerr << "  I(nu_peak) = " << iPeak << "\n";
    std::cerr << "  I(2 nu_peak) = " << iAbove << "\n";
    return 1;
  }

  if (iAbove >= iBelow) {
    std::cerr << "  FAIL: Spectrum asymmetry incorrect\n";
    std::cerr << "  I(0.5 nu_peak) = " << iBelow
              << " should be > I(2 nu_peak) = " << iAbove << "\n";
    return 1;
  }

  std::cout << "  I(0.5 nu_peak) = " << iBelow << " erg/s/Hz\n";
  std::cout << "  I(nu_peak) = " << iPeak << " erg/s/Hz\n";
  std::cout << "  I(2 nu_peak) = " << iAbove << " erg/s/Hz\n";
  std::cout << "  PASS: Planck spectrum shape\n";
  return 0;
}

// Test: Temperature scaling affects peak wavelength correctly
int testTemperatureWavelengthScaling() {
  std::cout << "Testing temperature-wavelength scaling...\n";

  const double m1      = 1e30;
  const double m2      = 2.0 * m1;

  const double t1      = physics::hawkingTemperature(m1);
  const double t2      = physics::hawkingTemperature(m2);
  const double lambda1 = physics::hawkingPeakWavelength(m1);
  const double lambda2 = physics::hawkingPeakWavelength(m2);

  // Since T_H ~ 1/M, T2 = T1/2; since lambda_peak ~ 1/T, lambda2 = 2*lambda1
  const double lambdaRatio   = lambda2 / lambda1;
  const double expectedRatio = 2.0;

  if (!approxEq(lambdaRatio, expectedRatio, TOLERANCE)) {
    std::cerr << "  FAIL: lambda(2M) / lambda(M) = " << lambdaRatio
              << ", expected " << expectedRatio << "\n";
    return 1;
  }

  std::cout << "  T(M) = " << t1 << " K, lambda(M) = " << lambda1 << " cm\n";
  std::cout << "  T(2M) = " << t2 << " K, lambda(2M) = " << lambda2 << " cm\n";
  std::cout << "  Ratio lambda(2M)/lambda(M) = " << lambdaRatio << "\n";
  std::cout << "  PASS: Temperature-wavelength scaling\n";
  return 0;
}

// Test: Visible light wavelength range
int testVisibleSpectrumRange() {
  std::cout << "Testing visible spectrum range...\n";

  constexpr double lambdaRed   = 7.0e-5;  // 700 nm (red)
  constexpr double lambdaGreen = 5.5e-5;  // 550 nm (green)
  constexpr double lambdaBlue  = 4.5e-5;  // 450 nm (blue)
  constexpr double bWien       = 0.2898;  // cm*K

  const double tRed   = bWien / lambdaRed;    // ~4140 K
  const double tGreen = bWien / lambdaGreen;  // ~5270 K
  const double tBlue  = bWien / lambdaBlue;   // ~6440 K

  // Find masses that emit at these temperatures
  auto massFromTemp = [](double tK) {
    return (physics::HBAR * physics::C * physics::C * physics::C) /
           (8.0 * physics::PI * physics::G * tK * physics::K_B);
  };

  const double mRed   = massFromTemp(tRed);
  const double mGreen = massFromTemp(tGreen);
  const double mBlue  = massFromTemp(tBlue);

  const double tRedCheck      = physics::hawkingTemperature(mRed);
  const double lambdaRedCheck = physics::hawkingPeakWavelength(mRed);

  if (!approxEq(tRed, tRedCheck, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Red temperature mismatch: " << tRed
              << " vs " << tRedCheck << "\n";
    return 1;
  }

  if (!approxEq(lambdaRed, lambdaRedCheck, LOOSE_TOLERANCE)) {
    std::cerr << "  FAIL: Red wavelength mismatch: " << lambdaRed
              << " vs " << lambdaRedCheck << "\n";
    return 1;
  }

  std::cout << "  Red (700 nm): T = " << tRed << " K, M = " << mRed << " g\n";
  std::cout << "  Green (550 nm): T = " << tGreen << " K, M = " << mGreen << " g\n";
  std::cout << "  Blue (450 nm): T = " << tBlue << " K, M = " << mBlue << " g\n";
  std::cout << "  PASS: Visible spectrum range\n";
  return 0;
}

// Test: Spectrum at extreme temperatures
int testExtremeTemperatures() {
  std::cout << "Testing extreme temperatures...\n";

  const double mHot      = 5e14;
  const double tHot      = physics::hawkingTemperature(mHot);
  const double lambdaHot = physics::hawkingPeakWavelength(mHot);

  const double mCold      = physics::M_SUN;
  const double tCold      = physics::hawkingTemperature(mCold);
  const double lambdaCold = physics::hawkingPeakWavelength(mCold);

  if (lambdaHot > 1e-6) {  // Shorter than 10 nm
    std::cerr << "  FAIL: Primordial BH wavelength too long: " << lambdaHot << " cm\n";
    return 1;
  }

  if (lambdaCold < 1e5) {  // Longer than 1 km
    std::cerr << "  FAIL: Solar mass BH wavelength too short: " << lambdaCold << " cm\n";
    return 1;
  }

  std::cout << "  Primordial (hot): T = " << tHot << " K, lambda_peak = " << lambdaHot << " cm\n";
  std::cout << "  Solar mass (cold): T = " << tCold << " K, lambda_peak = " << lambdaCold << " cm\n";
  std::cout << "  PASS: Extreme temperatures\n";
  return 0;
}

// Test: Spectrum integral (Stefan-Boltzmann law)
int testStefanBoltzmannConsistency() {
  std::cout << "Testing Stefan-Boltzmann consistency...\n";

  const double mTest    = 1e30;
  const double lHawking = physics::hawkingLuminosity(mTest);

  const double tVal  = physics::hawkingTemperature(mTest);
  const double rS    = physics::schwarzschildRadius(mTest);
  const double area  = 4.0 * physics::PI * rS * rS;

  // Stefan-Boltzmann constant sigma (CGS units)
  constexpr double sigmaSb = 5.6704e-5;  // erg/(cm^2*s*K^4)

  const double lStefan = sigmaSb * area * std::pow(tVal, 4);
  const double ratio   = lHawking / lStefan;

  if ((ratio < 0.1) || (ratio > 10.0)) {
    std::cerr << "  FAIL: Luminosity ratio out of range: " << ratio << "\n";
    std::cerr << "  L_hawking = " << lHawking << " erg/s\n";
    std::cerr << "  L_stefan = " << lStefan << " erg/s\n";
    return 1;
  }

  std::cout << "  L_hawking = " << lHawking << " erg/s\n";
  std::cout << "  L_stefan-boltzmann = " << lStefan << " erg/s\n";
  std::cout << "  Ratio = " << ratio << "\n";
  std::cout << "  PASS: Stefan-Boltzmann consistency\n";
  return 0;
}

} // namespace

int main() {
  std::cout << "=== Hawking Radiation Spectrum Tests ===\n\n";

  int result = 0;

  result |= testWienDisplacementLaw();
  result |= testPeakFrequency();
  result |= testWavelengthFrequencyRelation();
  result |= testPlanckSpectrumShape();
  result |= testTemperatureWavelengthScaling();
  result |= testVisibleSpectrumRange();
  result |= testExtremeTemperatures();
  result |= testStefanBoltzmannConsistency();

  std::cout << "\n";
  if (result == 0) {
    std::cout << "All Hawking spectrum tests PASSED\n";
  } else {
    std::cout << "Some Hawking spectrum tests FAILED\n";
  }

  return result;
}
