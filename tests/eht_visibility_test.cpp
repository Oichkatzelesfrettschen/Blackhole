/**
 * @file tests/eht_visibility_test.cpp
 * @brief Validation tests for the synthetic EHT visibility pipeline.
 *
 * WHY: eht_visibility.h implements the core VLBI measurement model (van Cittert-
 * Zernike theorem, TMS 2017 UV baseline transform, closure quantities) needed to
 * compare Blackhole ray-traced images against EHT calibration-free observables.
 * These tests guard the formulas against regressions using analytically derivable
 * limits that do not require numerical relativity.
 *
 * Test list (18 tests):
 *
 * UV coordinate transform (TMS Eq. 4.1):
 *   1.  At H=0 (source on meridian): u = dY/lambda, v = (-dX sinD + dZ cosD)/lambda.
 *   2.  Equatorial source (d=0): v = dZ/lambda independent of hour angle.
 *   3.  Conjugate baseline (swap stations) gives negated (u,v).
 *   4.  uvTrack returns the requested number of sample points.
 *   5.  uvTrack single-point matches direct uvwCoordinates call.
 *
 * Complex visibility (van Cittert-Zernike):
 *   6.  complexVisibility at (u,v)=(0,0) equals total flux times pixel area.
 *   7.  Normalised visibility amplitude = 1 at (u,v)=(0,0) for any image.
 *   8.  Point source at image centre: normalised |V| = 1 at arbitrary (u,v).
 *   9.  Empty image: complexVisibility returns {0,0}.
 *  10.  Two-point antisymmetric source: V(u,0) oscillates as expected.
 *
 * Closure quantities:
 *  11.  Closure phase = 0 for a point source (all true phases zero).
 *  12.  Closure amplitude = 1 for a point source.
 *  13.  Closure phase is invariant to station-based phase errors.
 *  14.  Closure amplitude is invariant to station-based gain errors.
 *
 * Analytical ring visibility:
 *  15.  analyticalRingVisibility at q=0 equals totalFlux.
 *  16.  analyticalRingVisibility near first null is close to zero.
 *  17.  ringVisibilityFirstNull(0) returns 0 (degenerate guard).
 *  18.  M87* 42 uas shadow: first null baseline in [4000, 6000] km at 230 GHz.
 *
 * References:
 *   - Thompson, Moran & Swenson (2017), Interferometry and Synthesis, 3rd ed.
 *   - EHT Collaboration (2019), ApJ 875, L3 (M87* first image)
 *   - Jennison (1958), MNRAS 118, 276 (closure phase)
 */

#include <cmath>
#include <cstddef>
#include <exception>
#include <iostream>
#include <limits>
#include <numbers>
#include <stdexcept>
#include <vector>

#include "../src/physics/eht_visibility.h"

using namespace physics;

// ---------------------------------------------------------------------------
// Minimal test framework (mirrors gw_memory_precession_test.cpp pattern)
// ---------------------------------------------------------------------------

namespace {

bool gAllPass = true;

void check(bool condition, const char *test, const char *detail = "") {
  if (condition) {
    std::cout << "  [PASS] " << test << "\n";
  } else {
    std::cout << "  [FAIL] " << test;
    if ((detail != nullptr) && (detail[0] != 0)) {
      std::cout << " -- " << detail;
    }
    std::cout << "\n";
    gAllPass = false;
  }
}

bool near(double a, double b, double tol = 1.0e-10) {
  return std::abs(a - b) <= tol;
}

// Rotate a ComplexVis by angle theta (simulate station-based phase addition).
ComplexVis rotateVis(const ComplexVis &v, double theta) {
  return {v.re * std::cos(theta) - v.im * std::sin(theta),
          v.re * std::sin(theta) + v.im * std::cos(theta)};
}

// Scale a ComplexVis amplitude by gain g > 0.
ComplexVis scaleVis(const ComplexVis &v, double g) {
  return {v.re * g, v.im * g};
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

void testUvwAtMeridian() {
  // Test 1: at H=0, u = dY/lambda, v = (-dX sinD + dZ cosD)/lambda
  TelescopeStation const s1 = {"S1", 0.0, 0.0, 0.0, 10.0};
  TelescopeStation const s2 = {"S2", 1000.0, 2000.0, 3000.0, 10.0};
  const double lambda = 1.3e-3;
  const double decl = 12.391 * std::numbers::pi / 180.0; // M87*

  const double h = 0.0;
  const UVW uvw = uvwCoordinates(s1, s2, h, decl, lambda);

  // dX=1000, dY=2000, dZ=3000
  const double dX = 1000.0;
  const double dY = 2000.0;
  const double dZ = 3000.0;
  const double sinD = std::sin(decl);
  const double cosD = std::cos(decl);
  const double uExpected = dY / lambda;
  const double vExpected = (-dX * sinD + dZ * cosD) / lambda;
  const double wExpected = (dX * cosD + dZ * sinD) / lambda;

  check(near(uvw.u, uExpected, 1.0), "uvwCoordinates: u = dY/lambda at H=0");
  check(near(uvw.v, vExpected, 1.0), "uvwCoordinates: v = (-dX sinD + dZ cosD)/lambda at H=0");
  check(near(uvw.w, wExpected, 1.0), "uvwCoordinates: w = (dX cosD + dZ sinD)/lambda at H=0");
}

void testUvwEquatorialSource() {
  // Test 2: equatorial source (d=0): v = dZ/lambda for any H
  TelescopeStation const s1 = {"S1", 0.0, 0.0, 0.0, 10.0};
  TelescopeStation const s2 = {"S2", 500.0, -300.0, 1200.0, 10.0};
  const double lambda = 1.3e-3;
  const double decl = 0.0; // equatorial

  const double vExpected = (s2.z - s1.z) / lambda;
  bool vConstant = true;
  for (int k = 0; k < 8; ++k) {
    const double h = k * std::numbers::pi / 4.0;
    const UVW uvw = uvwCoordinates(s1, s2, h, decl, lambda);
    if (!near(uvw.v, vExpected, 1.0)) {
      vConstant = false;
    }
  }
  check(vConstant, "uvwCoordinates: v = dZ/lambda is constant for equatorial source");
}

void testConjugateBaseline() {
  // Test 3: swapping stations negates (u,v,w)
  TelescopeStation const s1 = {"S1", 2225144.2, -5441197.6, -2479303.4, 73.0}; // ALMA
  TelescopeStation const s2 = {"S2", -5464075.2, -2493028.4, 2150612.2, 15.0}; // JCMT

  const double lambda = EHT_WAVELENGTH;
  const double decl = M87_DEC_RAD;
  const double h = 0.3;

  const UVW uvw12 = uvwCoordinates(s1, s2, h, decl, lambda);
  const UVW uvw21 = uvwCoordinates(s2, s1, h, decl, lambda);

  check(near(uvw12.u + uvw21.u, 0.0, 1.0), "uvwCoordinates: conjugate baseline negates u");
  check(near(uvw12.v + uvw21.v, 0.0, 1.0), "uvwCoordinates: conjugate baseline negates v");
  check(near(uvw12.w + uvw21.w, 0.0, 1.0), "uvwCoordinates: conjugate baseline negates w");
}

void testUvTrackPointCount() {
  // Test 4: uvTrack returns the requested number of points
  TelescopeStation const alma = ehtStation(EhtStation::ALMA);
  TelescopeStation const spt = ehtStation(EhtStation::SPT);

  const std::size_t n = 37;
  auto track = uvTrack(alma, spt, -1.0, 1.0, M87_DEC_RAD, EHT_WAVELENGTH, n);

  check(track.size() == n, "uvTrack: returns requested nPoints");
}

void testUvTrackSinglePoint() {
  // Test 5: single-point uvTrack matches direct uvwCoordinates at haBeg
  TelescopeStation const alma = ehtStation(EhtStation::ALMA);
  TelescopeStation const iram = ehtStation(EhtStation::IRAM);
  const double ha = 0.7;

  auto track = uvTrack(alma, iram, ha, ha + 1.0, M87_DEC_RAD, EHT_WAVELENGTH, 1);
  const UVW uvw = uvwCoordinates(alma, iram, ha, M87_DEC_RAD, EHT_WAVELENGTH);

  check(near(track[0].first, uvw.u, 1.0), "uvTrack: single point u matches uvwCoordinates");
  check(near(track[0].second, uvw.v, 1.0), "uvTrack: single point v matches uvwCoordinates");
}

void testVisibilityAtZeroBaselineEqualsTotalFlux() {
  // Test 6: complexVisibility at (u,v)=(0,0) = sum(image) * pixelArea
  const std::size_t n = 4;
  const double pix = 1.0e-10; // 0.1 uas
  std::vector<double> image(n * n, 0.0);
  // Set a few pixels to known values
  image[0] = 1.0;
  image[5] = 2.0;
  image[10] = 0.5;
  const double totalFlux = (1.0 + 2.0 + 0.5) * pix * pix;

  const ComplexVis v00 = complexVisibility(image, n, pix, 0.0, 0.0);

  check(near(v00.re, totalFlux, 1.0e-30), "complexVisibility: V(0,0) = totalFlux * pixelArea");
  check(near(v00.im, 0.0, 1.0e-30), "complexVisibility: V(0,0) has zero imaginary part");
}

void testNormalisedVisibilityAtZeroBaseline() {
  // Test 7: normalised |V(0,0)| = 1 for any image
  const std::size_t n = 8;
  const double pix = 5.0e-11;
  std::vector<double> image(n * n, 0.0);
  for (std::size_t i = 0; i < n * n; ++i) {
    image[i] = static_cast<double>((i % 3) + 1);
  }

  const ComplexVis vn = normalisedVisibility(image, n, pix, 0.0, 0.0);
  check(near(vn.amplitude(), 1.0, 1.0e-12), "normalisedVisibility: |V_norm(0,0)| = 1");
}

void testPointSourceNormalisedVisibility() {
  // Test 8: single pixel at image centre gives |V_norm| = 1 at any (u,v)
  const std::size_t n = 64;
  const double pix = 1.0e-10;
  std::vector<double> image(n * n, 0.0);
  // Place flux at exact centre pixel -- (row = N/2, col = N/2)
  // With halfN=32.0, x=(32-32)*pix=0, y=(32-32)*pix=0 -> pure real DFT
  image[(n / 2) * n + (n / 2)] = 1.0;

  // Test at several (u,v) values
  const double uvVals[] = {0.0, 1.0e8, 3.76e9, -2.0e9};
  bool allOne = true;
  for (double const u : uvVals) {
    for (double const v : uvVals) {
      const ComplexVis vn = normalisedVisibility(image, n, pix, u, v);
      if (std::abs(vn.amplitude() - 1.0) > 1.0e-10) {
        allOne = false;
      }
    }
  }
  check(allOne, "normalisedVisibility: point source gives |V_norm| = 1 at all (u,v)");
}

void testComplexVisibilityEmptyImage() {
  // Test 9: empty image returns zero visibility
  const std::size_t n = 8;
  std::vector<double> const image(n * n, 0.0);
  const ComplexVis v = complexVisibility(image, n, 1.0e-10, 1.0e8, 0.0);
  check(near(v.re, 0.0, 1.0e-30) && near(v.im, 0.0, 1.0e-30),
        "complexVisibility: all-zero image gives zero visibility");

  // Also test with image smaller than N*N
  std::vector<double> const small(2, 1.0);
  const ComplexVis vs = complexVisibility(small, n, 1.0e-10, 0.0, 0.0);
  check(near(vs.re, 0.0, 1.0e-30), "complexVisibility: undersized image returns zero");
}

void testTwoPointSourceVisibility() {
  // Test 10: two equal-flux point sources symmetric about centre
  // Sources at (col=N/2+d, row=N/2) and (col=N/2-d, row=N/2)
  // Their DFT = 2*F*dOmega * cos(2*pi*u*d*pix)
  const std::size_t n = 64;
  const double pix = 1.0e-11;
  const std::size_t d = 8; // pixel offset from centre
  std::vector<double> image(n * n, 0.0);
  const double f = 1.0;
  image[(n / 2) * n + (n / 2 + d)] = f;
  image[(n / 2) * n + (n / 2 - d)] = f;

  // At u such that 2*pi*u*d*pix = pi/2: V_re should be ~0
  const double uQuarter = 1.0 / (4.0 * static_cast<double>(d) * pix);
  const ComplexVis vq = complexVisibility(image, n, pix, uQuarter, 0.0);
  // cos(pi/2) = 0 -> re ~ 0; two sources symmetric -> im = 0 exactly
  check(std::abs(vq.re) < 1.0e-20,
        "complexVisibility: antisymmetric two-source null at quarter period");
  check(std::abs(vq.im) < 1.0e-30,
        "complexVisibility: two symmetric sources give zero imaginary part");
}

void testClosurePhasePointSource() {
  // Test 11: closure phase = 0 for a point source
  const std::size_t n = 32;
  const double pix = 1.0e-10;
  std::vector<double> image(n * n, 0.0);
  image[(n / 2) * n + (n / 2)] = 1.0;

  // Three arbitrary (u,v) pairs forming a triangle
  const ComplexVis v12 = normalisedVisibility(image, n, pix, 1.0e8, 2.0e8);
  const ComplexVis v23 = normalisedVisibility(image, n, pix, 3.0e8, -1.0e8);
  const ComplexVis v31 = normalisedVisibility(image, n, pix, -4.0e8, -1.0e8);

  const double phi = closurePhase(v12, v23, v31);
  check(near(phi, 0.0, 1.0e-10), "closurePhase: zero for point source");
}

void testClosureAmplitudePointSource() {
  // Test 12: closure amplitude = 1 for a point source
  const std::size_t n = 32;
  const double pix = 1.0e-10;
  std::vector<double> image(n * n, 0.0);
  image[(n / 2) * n + (n / 2)] = 1.0;

  const ComplexVis v12 = normalisedVisibility(image, n, pix, 1.0e8, 2.0e8);
  const ComplexVis v34 = normalisedVisibility(image, n, pix, 5.0e8, -3.0e8);
  const ComplexVis v13 = normalisedVisibility(image, n, pix, 2.0e8, -1.0e8);
  const ComplexVis v24 = normalisedVisibility(image, n, pix, 4.0e8, 6.0e8);

  const double ca = closureAmplitude(v12, v34, v13, v24);
  check(near(ca, 1.0, 1.0e-10), "closureAmplitude: equals 1 for point source");
}

void testClosurePhaseInvariantToStationErrors() {
  // Test 13: closure phase is invariant to station-based phase errors.
  //
  // WHY use explicit ComplexVis values rather than DFT: if any baseline's
  // visibility falls near a null (J_0 zero) of the source brightness distribution,
  // the bispectrum amplitude can be so small that floating-point noise dominates
  // the phase, making the DFT-based comparison numerically ill-conditioned.
  // The closure phase cancellation is a purely algebraic property of the formula
  // arg(V12 * V23 * V31) regardless of how the visibilities were computed, so we
  // validate it directly with hand-chosen non-degenerate complex numbers.
  ComplexVis const v12 = {0.7, 0.3};  // amplitude ~0.762
  ComplexVis const v23 = {-0.4, 0.6}; // amplitude ~0.721
  ComplexVis const v31 = {0.5, -0.8}; // amplitude ~0.943

  const double phiTrue = closurePhase(v12, v23, v31);

  // Apply station-based phase errors: psi_1 = 0.7 rad, psi_2 = 1.3 rad, psi_3 = -0.5 rad.
  // The corrupted visibilities are V_ij^obs = V_ij^true * exp(i*(psi_i - psi_j)).
  // Sum of angle increments: (psi1-psi2)+(psi2-psi3)+(psi3-psi1) = 0 exactly.
  const double psi1 = 0.7;
  const double psi2 = 1.3;
  const double psi3 = -0.5;
  const ComplexVis v12c = rotateVis(v12, psi1 - psi2);
  const ComplexVis v23c = rotateVis(v23, psi2 - psi3);
  const ComplexVis v31c = rotateVis(v31, psi3 - psi1);

  const double phiCorrupted = closurePhase(v12c, v23c, v31c);
  check(near(phiTrue, phiCorrupted, 1.0e-12),
        "closurePhase: invariant to station-based phase errors");
}

void testClosureAmplitudeInvariantToGainErrors() {
  // Test 14: closure amplitude is invariant to station-based gain errors
  const std::size_t n = 16;
  const double pix = 3.0e-11;
  std::vector<double> image(n * n, 0.0);
  // Uniform disk
  for (std::size_t row = 0; row < n; ++row) {
    for (std::size_t col = 0; col < n; ++col) {
      const double dy = static_cast<double>(row) - static_cast<double>(n) / 2.0;
      const double dx = static_cast<double>(col) - static_cast<double>(n) / 2.0;
      if (std::hypot(dx, dy) < 3.5) {
        image[row * n + col] = 1.0;
      }
    }
  }

  const ComplexVis v12t = complexVisibility(image, n, pix, 1.5e9, -0.8e9);
  const ComplexVis v34t = complexVisibility(image, n, pix, -2.0e9, 1.2e9);
  const ComplexVis v13t = complexVisibility(image, n, pix, 0.8e9, 1.9e9);
  const ComplexVis v24t = complexVisibility(image, n, pix, -2.7e9, -2.3e9);

  const double caTrue = closureAmplitude(v12t, v34t, v13t, v24t);

  // Station gains: gain1=1.5, gain2=0.7, gain3=2.2, gain4=0.4
  const double gain1 = 1.5;
  const double gain2 = 0.7;
  const double gain3 = 2.2;
  const double gain4 = 0.4;
  const ComplexVis v12c = scaleVis(v12t, gain1 * gain2);
  const ComplexVis v34c = scaleVis(v34t, gain3 * gain4);
  const ComplexVis v13c = scaleVis(v13t, gain1 * gain3);
  const ComplexVis v24c = scaleVis(v24t, gain2 * gain4);

  const double caCorrupted = closureAmplitude(v12c, v34c, v13c, v24c);
  check(near(caTrue, caCorrupted, 1.0e-12),
        "closureAmplitude: invariant to station-based gain errors");
}

void testRingVisibilityAtZeroBaseline() {
  // Test 15: analyticalRingVisibility at q=0 equals totalFlux (J_0(0) = 1)
  const double r = 21.0 * MICROARCSEC_RAD;
  const double flux = 0.6; // 0.6 Jy (M87* typical)
  const double v0 = analyticalRingVisibility(r, flux, 0.0);
  check(near(v0, flux, 1.0e-15), "analyticalRingVisibility: V(q=0) = totalFlux");
}

void testRingVisibilityNearFirstNull() {
  // Test 16: analyticalRingVisibility near the first null is small
  const double r = 21.0 * MICROARCSEC_RAD;
  const double flux = 1.0;
  const double qNull = ringVisibilityFirstNull(r);
  // Evaluate at the exact first-null baseline: J_0(2.4048) ~ 0
  const double vNull = analyticalRingVisibility(r, flux, qNull);
  check(std::abs(vNull) < 1.0e-6, "analyticalRingVisibility: near zero at first null");

  // Visibility oscillates: at q slightly past null, V should be negative
  const double vPast = analyticalRingVisibility(r, flux, qNull * 1.05);
  check(vPast < 0.0, "analyticalRingVisibility: negative past first null (J_0 oscillates)");
}

void testRingVisibilityFirstNullDegenerate() {
  // Test 17: ringVisibilityFirstNull(0) returns 0 (degenerate guard)
  check(near(ringVisibilityFirstNull(0.0), 0.0, 1.0e-30),
        "ringVisibilityFirstNull: returns 0 for zero ring radius");
}

void testM87ShadowBaseline() {
  // Test 18: M87* 42 uas shadow -> first null physical baseline in [4000, 6000] km
  // R = 21 uas (half-diameter of shadow)
  const double rM87 = 21.0 * MICROARCSEC_RAD;               // [rad]
  const double qNull = ringVisibilityFirstNull(rM87);       // [wavelengths]
  const double baselineKm = qNull * EHT_WAVELENGTH / 1.0e3; // [km]

  // EHT 2017: longest US baselines ~5000 km for M87* shadow detection
  check(baselineKm > 4000.0 && baselineKm < 6000.0,
        "ringVisibilityFirstNull: M87* 42 uas shadow null in [4000, 6000] km at 230 GHz");
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

void testInvalidInputs() {
  bool caughtStation = false;
  try {
    (void)ehtStation(EhtStation::COUNT);
  } catch (const std::out_of_range &) {
    caughtStation = true;
  }
  check(caughtStation, "ehtStation: invalid station throws catchable out_of_range");
  bool caughtRing = false;
  try {
    (void)analyticalRingVisibility(-1.0, 1.0, 1.0);
  } catch (const std::domain_error &) {
    caughtRing = true;
  }
  check(caughtRing,
        "analyticalRingVisibility: negative Bessel argument throws catchable domain_error");
  const ComplexVis tiny{1.0e-21, 0.0};
  check(near(closureAmplitude(tiny, tiny, tiny, tiny), 1.0),
        "closureAmplitude: nonzero visibility scale preserves ratio");
  check(std::isnan(closureAmplitude(tiny, tiny, {}, tiny)),
        "closureAmplitude: zero denominator returns NaN");
  const std::vector<double> image{1.0};
  const auto oversized =
      complexVisibility(image, std::numeric_limits<std::size_t>::max(), 1.0, 0.0, 0.0);
  check(oversized.re == 0.0 && oversized.im == 0.0,
        "complexVisibility: overflowing square extent returns zero");
}

} // namespace

int main() try {
  std::cout << "\n=== EHT Visibility Pipeline Tests ===\n\n";

  std::cout << "UV coordinate transform (TMS Eq. 4.1):\n";
  testUvwAtMeridian();
  testUvwEquatorialSource();
  testConjugateBaseline();
  testUvTrackPointCount();
  testUvTrackSinglePoint();

  std::cout << "\nComplex visibility (van Cittert-Zernike):\n";
  testVisibilityAtZeroBaselineEqualsTotalFlux();
  testNormalisedVisibilityAtZeroBaseline();
  testPointSourceNormalisedVisibility();
  testComplexVisibilityEmptyImage();
  testTwoPointSourceVisibility();

  std::cout << "\nClosure quantities:\n";
  testClosurePhasePointSource();
  testClosureAmplitudePointSource();
  testClosurePhaseInvariantToStationErrors();
  testClosureAmplitudeInvariantToGainErrors();

  std::cout << "\nAnalytical ring visibility:\n";
  testRingVisibilityAtZeroBaseline();
  testRingVisibilityNearFirstNull();
  testRingVisibilityFirstNullDegenerate();
  testM87ShadowBaseline();

  testInvalidInputs();

  std::cout << "\n";
  if (gAllPass) {
    std::cout << "[ALL PASS] EHT visibility checks passed.\n\n";
    return 0;
  }
  std::cout << "[FAILURE] One or more tests failed.\n\n";
  return 1;
} catch (const std::exception &error) {
  std::cerr << "Unexpected test exception: " << error.what() << '\n';
  return 1;
} catch (...) {
  std::cerr << "Unexpected non-standard test exception\n";
  return 1;
}
