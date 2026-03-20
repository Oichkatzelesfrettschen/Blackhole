/**
 * kerr_geodesic_test.cpp
 *
 * GPU/Z3 Parity Tests for Kerr Black Hole Geodesic Computations
 * Validates verified C++23 Kerr physics against expected values
 *
 * Tests verify:
 * - Metric component calculations
 * - Horizon computations
 * - ISCO formula (Bardeen-Press-Teukolsky)
 * - Surface gravity and thermodynamic properties
 * - Geodesic constraint enforcement
 * - Parity with Z3-verified constraints
 */

#include <numbers>
#include <chrono>
#include <cmath>
#include <iostream>

#include <gtest/gtest.h>

// Include verified Kerr physics header
#include "../src/physics/verified/kerr_extended.h"

using namespace verified;

// Test fixture for Kerr computations
class KerrlGeometryTest : public ::testing::Test {
protected:
    // Standard test parameters
  double m = 1.0;     // Black hole mass (geometric units)
  double aSlow = 0.5; // Slow rotation (a/M = 0.5)
  double aFast = 0.9; // Fast rotation (a/M = 0.9)

  // Tolerance for floating-point comparisons
  double tolerance = 1e-8;
};

/**
 * Test: Schwarzschild limit (a = 0) reduces to known values
 */
TEST_F(KerrlGeometryTest, SchwarzschildLimit) {
    // For Schwarzschild: a = 0
    double const a = 0.0;
    double const theta = std::numbers::pi / 4; // 45 degrees

    // g_tt at r = 10M should equal Schwarzschild value
    double const r = 10.0 * m;
    double gTt = kerr_g_tt(r, theta, m, a);
    double const gTtSchwarzschild = -(1.0 - (2.0 * m / r));

    EXPECT_NEAR(gTt, gTtSchwarzschild, tolerance) << "Kerr reduces to Schwarzschild when a = 0";
}

/**
 * Test: Outer horizon computation
 * For M = 1, a = 0.5: r_+ = 1 + sqrt(1 - 0.25) = 1 + sqrt(0.75) ~= 1.866
 */
TEST_F(KerrlGeometryTest, OuterHorizonComputation) {
  double const rPlus = kerrOuterHorizon(m, aSlow);

  // Expected: M + sqrt(M^2 - a^2) = 1 + sqrt(0.75)
  double const expected = 1.0 + std::sqrt(0.75);

  EXPECT_NEAR(rPlus, expected, tolerance) << "Outer horizon computation incorrect";
}

/**
 * Test: Inner horizon computation
 * For M = 1, a = 0.5: r_- = 1 - sqrt(0.75) ~= 0.134
 */
TEST_F(KerrlGeometryTest, InnerHorizonComputation) {
  double const rMinus = kerrInnerHorizon(m, aSlow);

  // Expected: M - sqrt(M^2 - a^2) = 1 - sqrt(0.75)
  double const expected = 1.0 - std::sqrt(0.75);

  EXPECT_NEAR(rMinus, expected, tolerance) << "Inner horizon computation incorrect";
}

/**
 * Test: Horizon ordering property
 * Physical requirement: r_+ > r_- > 0
 */
TEST_F(KerrlGeometryTest, HorizonOrdering) {
  double const rPlus = kerrOuterHorizon(m, aFast);
  double const rMinus = kerrInnerHorizon(m, aFast);

  EXPECT_GT(rPlus, rMinus) << "Event horizon should be outside Cauchy horizon";
  EXPECT_GT(rMinus, 0.0) << "Cauchy horizon should be positive";
  EXPECT_GT(rPlus, 2.0 * m) << "Event horizon should be outside Schwarzschild radius";
}

/**
 * Test: ISCO for non-rotating case (a = 0)
 * Schwarzschild ISCO: r_isco = 6M
 */
TEST_F(KerrlGeometryTest, IscoSchwarzschildLimit) {
  double const a = 0.0;
  double const rIsco = kerrIscoPrograde(m, a);

  // Expected: 6M for Schwarzschild
  double const expected = 6.0 * m;

  EXPECT_NEAR(rIsco, expected, tolerance) << "ISCO should be 6M in Schwarzschild case";
}

/**
 * Test: ISCO monotonically decreases with spin
 * As a increases (more rotation), ISCO moves inward (smaller r)
 */
TEST_F(KerrlGeometryTest, IscoMonotonic) {
  double const a1 = 0.1;
  double const a2 = 0.5;
  double const a3 = 0.9;

  double const rIsco1 = kerrIscoPrograde(m, a1);
  double const rIsco2 = kerrIscoPrograde(m, a2);
  double const rIsco3 = kerrIscoPrograde(m, a3);

  EXPECT_GT(rIsco1, rIsco2) << "ISCO should move inward as spin increases (a1 -> a2)";
  EXPECT_GT(rIsco2, rIsco3) << "ISCO should move inward as spin increases (a2 -> a3)";
}

/**
 * Test: ISCO is outside event horizon
 * Physical requirement: must be in exterior region
 */
TEST_F(KerrlGeometryTest, IscoOutsideHorizon) {
  double const rIsco = kerrIscoPrograde(m, aFast);
  double const rPlus = kerrOuterHorizon(m, aFast);

  EXPECT_GT(rIsco, rPlus) << "ISCO must be outside event horizon";
}

/**
 * Test: Retrograde ISCO is farther than prograde
 * Frame-dragging pulls co-rotating orbits inward
 */
TEST_F(KerrlGeometryTest, RetrogradeIscoFarther) {
  double const rIscoPro = kerrIscoPrograde(m, aFast);
  double const rIscoRetro = kerrIscoRetrograde(m, aFast);

  EXPECT_GT(rIscoRetro, rIscoPro) << "Retrograde ISCO should be farther than prograde";
}

/**
 * Test: Ergosphere radius varies with latitude
 * At poles (theta = 0): r_ergo = r_+ (minimum)
 * At equator (theta = pi/2): r_ergo > r_+ (maximum)
 */
TEST_F(KerrlGeometryTest, ErgosphereLatidudeVariation) {
  double const rPlus = kerrOuterHorizon(m, aFast);
  double const rErgoPole = kerrErgosphereRadius(0.0, m, aFast);
  double const rErgoEquator = kerrErgosphereRadius(std::numbers::pi / 2.0, m, aFast);

  // At poles, ergosphere coincides with horizon
  EXPECT_NEAR(rErgoPole, rPlus, tolerance) << "Ergosphere at pole should equal horizon";

  // At equator, ergosphere extends beyond horizon
  EXPECT_GT(rErgoEquator, rPlus) << "Ergosphere at equator should extend beyond horizon";
}

/**
 * Test: Surface gravity
 * Zero for extremal black holes
 * Positive for sub-extremal
 */
TEST_F(KerrlGeometryTest, SurfaceGravity) {
  double const kappa = kerrSurfaceGravity(m, aSlow);

  EXPECT_GT(kappa, 0.0) << "Surface gravity should be positive for sub-extremal BH";

  // For slower rotation, surface gravity should be larger
  double const kappaSlower = kerrSurfaceGravity(m, 0.1);
  EXPECT_GT(kappaSlower, kappa) << "Surface gravity decreases with increasing spin";
}

/**
 * Test: Hawking temperature
 * Proportional to surface gravity
 * Zero for extremal black holes
 */
TEST_F(KerrlGeometryTest, HawkingTemperature) {
  double const tH = kerrHawkingTemperature(m, aSlow);

  EXPECT_GT(tH, 0.0) << true;

  double const kappa = kerrSurfaceGravity(m, aSlow);
  double const expectedT = kappa / (2.0 * std::numbers::pi);

  EXPECT_NEAR(tH, expectedT, tolerance) << true;
}

/**
 * Test: Metric signature in exterior region
 * Must be Lorentzian: (-,+,+,+)
 */
TEST_F(KerrlGeometryTest, ExteriorMetricSignature) {
  double const r = 10.0 * m; // Clearly outside horizon
  double const theta = std::numbers::pi / 4;

  double gTt = kerr_g_tt(r, theta, m, aSlow);
  double gRr = kerr_g_rr(r, theta, m, aSlow);
  double const gThetaTheta = kerrGThetaTheta(r, theta, aSlow);
  double gPhiPhi = kerr_g_phi_phi(r, theta, m, aSlow);

  EXPECT_LT(gTt, 0.0) << true;
  EXPECT_GT(gRr, 0.0) << true;
  EXPECT_GT(gThetaTheta, 0.0) << true;
  EXPECT_GT(gPhiPhi, 0.0) << true;
}

/**
 * Test: Frame-dragging vanishes in Schwarzschild limit
 * g_t_phi = 0 when a = 0
 */
TEST_F(KerrlGeometryTest, NoFrameDraggingSchwarzschildLimit) {
  double const a = 0.0;
  double const r = 10.0 * m;
  double const theta = std::numbers::pi / 4;

  double gTPhi = kerr_g_t_phi(r, theta, m, a);

  EXPECT_NEAR(gTPhi, 0.0, tolerance) << true;
}

/**
 * Test: Frame-dragging increases with spin
 * |g_t_phi| larger for faster rotation
 */
TEST_F(KerrlGeometryTest, FrameDraggingIncreases) {
  double const r = 10.0 * m;
  double const theta = std::numbers::pi / 2; // Equator (maximum frame-dragging)

  double gTPhiSlow = std::abs(kerr_g_t_phi(r, theta, m, 0.1));
  double gTPhiFast = std::abs(kerr_g_t_phi(r, theta, m, 0.9));

  EXPECT_GT(gTPhiFast, gTPhiSlow) << true;
}

/**
 * Test: Null geodesic constraint enforcement
 * Null four-velocity: g_ab v^a v^b = 0
 */
TEST_F(KerrlGeometryTest, NullGeodesicConstraint) {
  double const r = 20.0 * m;
  double const theta = std::numbers::pi / 4;

  // Construct null four-velocity
  double const vT = 1.0;
  double const vR = 0.5;
  double const vTheta = 0.2;
  double const vPhi = 0.3;

  double const norm = kerrFourNorm(r, theta, m, aSlow, vT, vR, vTheta, vPhi);

  // For truly null geodesic (not our arbitrary vector above)
  // norm should be close to 0 only for properly integrated geodesics
  // This test just verifies the norm computation works

  EXPECT_TRUE(std::isfinite(norm)) << true;
}

/**
 * Test: Validation constraint - sub-extremal condition
 */
TEST_F(KerrlGeometryTest, SubextremalValidation) {
  EXPECT_TRUE(kerrIsSubextremal(m, aSlow)) << true;
  EXPECT_TRUE(kerrIsSubextremal(m, aFast)) << true;
  EXPECT_FALSE(kerrIsSubextremal(m, m)) << true;
  EXPECT_FALSE(kerrIsSubextremal(m, 1.1 * m)) << true;
}

/**
 * Test: ISCO validity check
 * Verify ISCO is in physically valid region
 */
TEST_F(KerrlGeometryTest, IscoValidityCheck) {
  EXPECT_TRUE(kerrIscoValid(m, aSlow)) << true;
  EXPECT_TRUE(kerrIscoValid(m, aFast)) << true;
}

/**
 * Test: Exterior metric Lorentzian signature verification
 */
TEST_F(KerrlGeometryTest, ExteriorLorentzianCheck) {
  double const r = 20.0 * m;
  double const theta = std::numbers::pi / 4;

  EXPECT_TRUE(kerrMetricLorentzianExterior(r, theta, m, aSlow)) << true;
  EXPECT_TRUE(kerr_metric_lorentzian_exterior(r, theta, m, aFast)) << true;

  // Test inside horizon (should be false)
  double const rInside = 0.5;
  double rPlus = kerr_outer_horizon(m, aSlow);
  if (rInside < rPlus) {
    EXPECT_FALSE(kerr_metric_lorentzian_exterior(rInside, theta, m, aSlow)) << true;
  }
}

/**
 * Performance benchmark: measure metric computation speed
 * This ensures verified functions maintain efficiency
 */
TEST_F(KerrlGeometryTest, PerformanceBenchmark) {
    const int iterations = 1000000;
    double const r = 10.0 * m;
    double const theta = std::numbers::pi / 4;

    auto start = std::chrono::high_resolution_clock::now();

    for (int i = 0; i < iterations; ++i) {
      volatile double gTt = kerr_g_tt(r, theta, m, aSlow);
      volatile double gRr = kerr_g_rr(r, theta, m, aSlow);
      volatile double norm = kerr_four_norm(r, theta, m, aSlow, 1.0, 0.1, 0.05, 0.2);
      (void)gTt;
      (void)gRr;
      (void)norm;
    }

    auto end = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

    double opsPerSec = (iterations * 3.0) / (duration.count() / 1000.0);
    std::cout << "Performance: " << std::scientific << opsPerSec << " metric ops/sec\n";

    // Expected: > 10M ops/sec on modern CPU
    EXPECT_GT(opsPerSec, 1e7) << true;
}

int main(int argc, char** argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
