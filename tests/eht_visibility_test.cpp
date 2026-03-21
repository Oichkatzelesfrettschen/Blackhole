/**
 * @file tests/eht_visibility_test.cpp
 * @brief Validation tests for the synthetic EHT visibility pipeline (D11).
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
#include <cstdio>
#include <iostream>
#include <numbers>
#include <vector>

#include "../src/physics/eht_visibility.h"

using namespace physics;

// ---------------------------------------------------------------------------
// Minimal test framework (mirrors gw_memory_precession_test.cpp pattern)
// ---------------------------------------------------------------------------

namespace {

bool gAllPass = true;

void check(bool condition, const char* test, const char* detail = "") {
    if (condition) {
        std::cout << "  [PASS] " << test << "\n";
    } else {
        std::cout << "  [FAIL] " << test;
        if (detail && detail[0]) { std::cout << " -- " << detail; }
        std::cout << "\n";
        gAllPass = false;
    }
}

bool near(double a, double b, double tol = 1.0e-10) {
    return std::abs(a - b) <= tol;
}

// Rotate a ComplexVis by angle theta (simulate station-based phase addition).
ComplexVis rotateVis(const ComplexVis& v, double theta) {
    return {v.re * std::cos(theta) - v.im * std::sin(theta),
            v.re * std::sin(theta) + v.im * std::cos(theta)};
}

// Scale a ComplexVis amplitude by gain g > 0.
ComplexVis scaleVis(const ComplexVis& v, double g) {
    return {v.re * g, v.im * g};
}

} // namespace

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

static void testUvwAtMeridian() {
    // Test 1: at H=0, u = dY/lambda, v = (-dX sinD + dZ cosD)/lambda
    TelescopeStation s1 = {"S1", 0.0, 0.0, 0.0, 10.0};
    TelescopeStation s2 = {"S2", 1000.0, 2000.0, 3000.0, 10.0};
    const double lambda = 1.3e-3;
    const double decl   = 12.391 * std::numbers::pi / 180.0;  // M87*

    const double H = 0.0;
    const UVW uvw = uvwCoordinates(s1, s2, H, decl, lambda);

    // dX=1000, dY=2000, dZ=3000
    const double dX = 1000.0, dY = 2000.0, dZ = 3000.0;
    const double sinD = std::sin(decl), cosD = std::cos(decl);
    const double u_expected = dY / lambda;
    const double v_expected = (-dX * sinD + dZ * cosD) / lambda;
    const double w_expected = ( dX * cosD + dZ * sinD) / lambda;

    check(near(uvw.u, u_expected, 1.0), "uvwCoordinates: u = dY/lambda at H=0");
    check(near(uvw.v, v_expected, 1.0), "uvwCoordinates: v = (-dX sinD + dZ cosD)/lambda at H=0");
    check(near(uvw.w, w_expected, 1.0), "uvwCoordinates: w = (dX cosD + dZ sinD)/lambda at H=0");
}

static void testUvwEquatorialSource() {
    // Test 2: equatorial source (d=0): v = dZ/lambda for any H
    TelescopeStation s1 = {"S1", 0.0, 0.0, 0.0, 10.0};
    TelescopeStation s2 = {"S2", 500.0, -300.0, 1200.0, 10.0};
    const double lambda = 1.3e-3;
    const double decl   = 0.0;  // equatorial

    const double v_expected = (s2.Z - s1.Z) / lambda;
    bool vConstant = true;
    for (int k = 0; k < 8; ++k) {
        const double H = k * std::numbers::pi / 4.0;
        const UVW uvw = uvwCoordinates(s1, s2, H, decl, lambda);
        if (!near(uvw.v, v_expected, 1.0)) { vConstant = false; }
    }
    check(vConstant, "uvwCoordinates: v = dZ/lambda is constant for equatorial source");
}

static void testConjugateBaseline() {
    // Test 3: swapping stations negates (u,v,w)
    TelescopeStation s1 = {"S1",  2225144.2, -5441197.6, -2479303.4, 73.0};  // ALMA
    TelescopeStation s2 = {"S2", -5464075.2, -2493028.4,  2150612.2, 15.0};  // JCMT

    const double lambda = kEhtWavelength;
    const double decl   = kM87DecRad;
    const double H      = 0.3;

    const UVW uvw12 = uvwCoordinates(s1, s2, H, decl, lambda);
    const UVW uvw21 = uvwCoordinates(s2, s1, H, decl, lambda);

    check(near(uvw12.u + uvw21.u, 0.0, 1.0), "uvwCoordinates: conjugate baseline negates u");
    check(near(uvw12.v + uvw21.v, 0.0, 1.0), "uvwCoordinates: conjugate baseline negates v");
    check(near(uvw12.w + uvw21.w, 0.0, 1.0), "uvwCoordinates: conjugate baseline negates w");
}

static void testUvTrackPointCount() {
    // Test 4: uvTrack returns the requested number of points
    TelescopeStation alma = ehtStation(EhtStation::ALMA);
    TelescopeStation spt  = ehtStation(EhtStation::SPT);

    const std::size_t N = 37;
    auto track = uvTrack(alma, spt, -1.0, 1.0, kM87DecRad, kEhtWavelength, N);

    check(track.size() == N, "uvTrack: returns requested nPoints");
}

static void testUvTrackSinglePoint() {
    // Test 5: single-point uvTrack matches direct uvwCoordinates at haBeg
    TelescopeStation alma = ehtStation(EhtStation::ALMA);
    TelescopeStation iram = ehtStation(EhtStation::IRAM);
    const double ha = 0.7;

    auto track = uvTrack(alma, iram, ha, ha + 1.0, kM87DecRad, kEhtWavelength, 1);
    const UVW uvw = uvwCoordinates(alma, iram, ha, kM87DecRad, kEhtWavelength);

    check(near(track[0].first,  uvw.u, 1.0), "uvTrack: single point u matches uvwCoordinates");
    check(near(track[0].second, uvw.v, 1.0), "uvTrack: single point v matches uvwCoordinates");
}

static void testVisibilityAtZeroBaselineEqualsTotalFlux() {
    // Test 6: complexVisibility at (u,v)=(0,0) = sum(image) * pixelArea
    const std::size_t N = 4;
    const double pix = 1.0e-10;  // 0.1 uas
    std::vector<double> image(N * N, 0.0);
    // Set a few pixels to known values
    image[0] = 1.0;
    image[5] = 2.0;
    image[10] = 0.5;
    const double totalFlux = (1.0 + 2.0 + 0.5) * pix * pix;

    const ComplexVis v00 = complexVisibility(image, N, pix, 0.0, 0.0);

    check(near(v00.re, totalFlux, 1.0e-30), "complexVisibility: V(0,0) = totalFlux * pixelArea");
    check(near(v00.im, 0.0, 1.0e-30), "complexVisibility: V(0,0) has zero imaginary part");
}

static void testNormalisedVisibilityAtZeroBaseline() {
    // Test 7: normalised |V(0,0)| = 1 for any image
    const std::size_t N = 8;
    const double pix = 5.0e-11;
    std::vector<double> image(N * N, 0.0);
    for (std::size_t i = 0; i < N * N; ++i) {
        image[i] = static_cast<double>((i % 3) + 1);
    }

    const ComplexVis vn = normalisedVisibility(image, N, pix, 0.0, 0.0);
    check(near(vn.amplitude(), 1.0, 1.0e-12), "normalisedVisibility: |V_norm(0,0)| = 1");
}

static void testPointSourceNormalisedVisibility() {
    // Test 8: single pixel at image centre gives |V_norm| = 1 at any (u,v)
    const std::size_t N = 64;
    const double pix = 1.0e-10;
    std::vector<double> image(N * N, 0.0);
    // Place flux at exact centre pixel -- (row = N/2, col = N/2)
    // With halfN=32.0, x=(32-32)*pix=0, y=(32-32)*pix=0 -> pure real DFT
    image[(N / 2) * N + (N / 2)] = 1.0;

    // Test at several (u,v) values
    const double uvVals[] = {0.0, 1.0e8, 3.76e9, -2.0e9};
    bool allOne = true;
    for (double u : uvVals) {
        for (double v : uvVals) {
            const ComplexVis vn = normalisedVisibility(image, N, pix, u, v);
            if (std::abs(vn.amplitude() - 1.0) > 1.0e-10) { allOne = false; }
        }
    }
    check(allOne, "normalisedVisibility: point source gives |V_norm| = 1 at all (u,v)");
}

static void testComplexVisibilityEmptyImage() {
    // Test 9: empty image returns zero visibility
    const std::size_t N = 8;
    std::vector<double> image(N * N, 0.0);
    const ComplexVis v = complexVisibility(image, N, 1.0e-10, 1.0e8, 0.0);
    check(near(v.re, 0.0, 1.0e-30) && near(v.im, 0.0, 1.0e-30),
          "complexVisibility: all-zero image gives zero visibility");

    // Also test with image smaller than N*N
    std::vector<double> small(2, 1.0);
    const ComplexVis vs = complexVisibility(small, N, 1.0e-10, 0.0, 0.0);
    check(near(vs.re, 0.0, 1.0e-30), "complexVisibility: undersized image returns zero");
}

static void testTwoPointSourceVisibility() {
    // Test 10: two equal-flux point sources symmetric about centre
    // Sources at (col=N/2+d, row=N/2) and (col=N/2-d, row=N/2)
    // Their DFT = 2*F*dOmega * cos(2*pi*u*d*pix)
    const std::size_t N   = 64;
    const double      pix = 1.0e-11;
    const std::size_t d   = 8;  // pixel offset from centre
    std::vector<double> image(N * N, 0.0);
    const double F = 1.0;
    image[(N / 2) * N + (N / 2 + d)] = F;
    image[(N / 2) * N + (N / 2 - d)] = F;

    // At u such that 2*pi*u*d*pix = pi/2: V_re should be ~0
    const double u_quarter = 1.0 / (4.0 * static_cast<double>(d) * pix);
    const ComplexVis vq = complexVisibility(image, N, pix, u_quarter, 0.0);
    // cos(pi/2) = 0 -> re ~ 0; two sources symmetric -> im = 0 exactly
    check(std::abs(vq.re) < 1.0e-20, "complexVisibility: antisymmetric two-source null at quarter period");
    check(std::abs(vq.im) < 1.0e-30, "complexVisibility: two symmetric sources give zero imaginary part");
}

static void testClosurePhasePointSource() {
    // Test 11: closure phase = 0 for a point source
    const std::size_t N = 32;
    const double pix = 1.0e-10;
    std::vector<double> image(N * N, 0.0);
    image[(N / 2) * N + (N / 2)] = 1.0;

    // Three arbitrary (u,v) pairs forming a triangle
    const ComplexVis v12 = normalisedVisibility(image, N, pix, 1.0e8,  2.0e8);
    const ComplexVis v23 = normalisedVisibility(image, N, pix, 3.0e8, -1.0e8);
    const ComplexVis v31 = normalisedVisibility(image, N, pix, -4.0e8, -1.0e8);

    const double phi = closurePhase(v12, v23, v31);
    check(near(phi, 0.0, 1.0e-10), "closurePhase: zero for point source");
}

static void testClosureAmplitudePointSource() {
    // Test 12: closure amplitude = 1 for a point source
    const std::size_t N = 32;
    const double pix = 1.0e-10;
    std::vector<double> image(N * N, 0.0);
    image[(N / 2) * N + (N / 2)] = 1.0;

    const ComplexVis v12 = normalisedVisibility(image, N, pix,  1.0e8,  2.0e8);
    const ComplexVis v34 = normalisedVisibility(image, N, pix,  5.0e8, -3.0e8);
    const ComplexVis v13 = normalisedVisibility(image, N, pix,  2.0e8, -1.0e8);
    const ComplexVis v24 = normalisedVisibility(image, N, pix,  4.0e8,  6.0e8);

    const double ca = closureAmplitude(v12, v34, v13, v24);
    check(near(ca, 1.0, 1.0e-10), "closureAmplitude: equals 1 for point source");
}

static void testClosurePhaseInvariantToStationErrors() {
    // Test 13: closure phase is invariant to station-based phase errors.
    //
    // WHY use explicit ComplexVis values rather than DFT: if any baseline's
    // visibility falls near a null (J_0 zero) of the source brightness distribution,
    // the bispectrum amplitude can be so small that floating-point noise dominates
    // the phase, making the DFT-based comparison numerically ill-conditioned.
    // The closure phase cancellation is a purely algebraic property of the formula
    // arg(V12 * V23 * V31) regardless of how the visibilities were computed, so we
    // validate it directly with hand-chosen non-degenerate complex numbers.
    ComplexVis v12 = {0.7,  0.3};   // amplitude ~0.762
    ComplexVis v23 = {-0.4, 0.6};   // amplitude ~0.721
    ComplexVis v31 = {0.5, -0.8};   // amplitude ~0.943

    const double phi_true = closurePhase(v12, v23, v31);

    // Apply station-based phase errors: psi_1 = 0.7 rad, psi_2 = 1.3 rad, psi_3 = -0.5 rad.
    // The corrupted visibilities are V_ij^obs = V_ij^true * exp(i*(psi_i - psi_j)).
    // Sum of angle increments: (psi1-psi2)+(psi2-psi3)+(psi3-psi1) = 0 exactly.
    const double psi1 = 0.7, psi2 = 1.3, psi3 = -0.5;
    const ComplexVis v12c = rotateVis(v12, psi1 - psi2);
    const ComplexVis v23c = rotateVis(v23, psi2 - psi3);
    const ComplexVis v31c = rotateVis(v31, psi3 - psi1);

    const double phi_corrupted = closurePhase(v12c, v23c, v31c);
    check(near(phi_true, phi_corrupted, 1.0e-12),
          "closurePhase: invariant to station-based phase errors");
}

static void testClosureAmplitudeInvariantToGainErrors() {
    // Test 14: closure amplitude is invariant to station-based gain errors
    const std::size_t N = 16;
    const double pix = 3.0e-11;
    std::vector<double> image(N * N, 0.0);
    // Uniform disk
    for (std::size_t row = 0; row < N; ++row) {
        for (std::size_t col = 0; col < N; ++col) {
            const double dy = static_cast<double>(row) - static_cast<double>(N) / 2.0;
            const double dx = static_cast<double>(col) - static_cast<double>(N) / 2.0;
            if (std::hypot(dx, dy) < 3.5) { image[row * N + col] = 1.0; }
        }
    }

    const ComplexVis v12t = complexVisibility(image, N, pix,  1.5e9, -0.8e9);
    const ComplexVis v34t = complexVisibility(image, N, pix, -2.0e9,  1.2e9);
    const ComplexVis v13t = complexVisibility(image, N, pix,  0.8e9,  1.9e9);
    const ComplexVis v24t = complexVisibility(image, N, pix, -2.7e9, -2.3e9);

    const double ca_true = closureAmplitude(v12t, v34t, v13t, v24t);

    // Station gains: G1=1.5, G2=0.7, G3=2.2, G4=0.4
    const double G1=1.5, G2=0.7, G3=2.2, G4=0.4;
    const ComplexVis v12c = scaleVis(v12t, G1 * G2);
    const ComplexVis v34c = scaleVis(v34t, G3 * G4);
    const ComplexVis v13c = scaleVis(v13t, G1 * G3);
    const ComplexVis v24c = scaleVis(v24t, G2 * G4);

    const double ca_corrupted = closureAmplitude(v12c, v34c, v13c, v24c);
    check(near(ca_true, ca_corrupted, 1.0e-12),
          "closureAmplitude: invariant to station-based gain errors");
}

static void testRingVisibilityAtZeroBaseline() {
    // Test 15: analyticalRingVisibility at q=0 equals totalFlux (J_0(0) = 1)
    const double R     = 21.0 * kMicroarcsecRad;
    const double flux  = 0.6;  // 0.6 Jy (M87* typical)
    const double V0    = analyticalRingVisibility(R, flux, 0.0);
    check(near(V0, flux, 1.0e-15), "analyticalRingVisibility: V(q=0) = totalFlux");
}

static void testRingVisibilityNearFirstNull() {
    // Test 16: analyticalRingVisibility near the first null is small
    const double R     = 21.0 * kMicroarcsecRad;
    const double flux  = 1.0;
    const double q_null = ringVisibilityFirstNull(R);
    // Evaluate at the exact first-null baseline: J_0(2.4048) ~ 0
    const double V_null = analyticalRingVisibility(R, flux, q_null);
    check(std::abs(V_null) < 1.0e-6, "analyticalRingVisibility: near zero at first null");

    // Visibility oscillates: at q slightly past null, V should be negative
    const double V_past = analyticalRingVisibility(R, flux, q_null * 1.05);
    check(V_past < 0.0, "analyticalRingVisibility: negative past first null (J_0 oscillates)");
}

static void testRingVisibilityFirstNullDegenerate() {
    // Test 17: ringVisibilityFirstNull(0) returns 0 (degenerate guard)
    check(near(ringVisibilityFirstNull(0.0), 0.0, 1.0e-30),
          "ringVisibilityFirstNull: returns 0 for zero ring radius");
}

static void testM87ShadowBaseline() {
    // Test 18: M87* 42 uas shadow -> first null physical baseline in [4000, 6000] km
    // R = 21 uas (half-diameter of shadow)
    const double R_m87 = 21.0 * kMicroarcsecRad;          // [rad]
    const double q_null = ringVisibilityFirstNull(R_m87);   // [wavelengths]
    const double baseline_km = q_null * kEhtWavelength / 1.0e3;  // [km]

    // EHT 2017: longest US baselines ~5000 km for M87* shadow detection
    check(baseline_km > 4000.0 && baseline_km < 6000.0,
          "ringVisibilityFirstNull: M87* 42 uas shadow null in [4000, 6000] km at 230 GHz");
}

// ---------------------------------------------------------------------------
// Main
// ---------------------------------------------------------------------------

int main() {
    std::cout << "\n=== EHT Visibility Pipeline Tests (D11) ===\n\n";

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

    std::cout << "\n";
    if (gAllPass) {
        std::cout << "[ALL PASS] 18/18 tests passed.\n\n";
        return 0;
    }
    std::cout << "[FAILURE] One or more tests failed.\n\n";
    return 1;
}
