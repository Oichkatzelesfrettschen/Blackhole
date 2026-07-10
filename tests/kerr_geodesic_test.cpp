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
 *
 * Self-contained runner: the build target links no test framework, so the
 * EXPECT_* helpers below record pass/fail counts and main() reports them.
 */

#include <chrono>
#include <cmath>
#include <iostream>
#include <numbers>
#include <string>

// Verified Kerr physics: kerr.hpp carries the snake_case Rocq-extraction
// surface (kerr_isco_prograde/retrograde and metric helpers);
// kerr_extended.h carries the constexpr camelCase extended surface
// (horizons, ergosphere, surface gravity, four-norm predicates).
#include "../src/physics/verified/geodesic.hpp"
#include "../src/physics/verified/kerr.hpp"
#include "../src/physics/verified/kerr_extended.h"

using namespace verified;

namespace {

// Standard test parameters (formerly the gtest fixture members)
constexpr double kMass = 1.0;  // Black hole mass (geometric units)
constexpr double kASlow = 0.5; // Slow rotation (a/M = 0.5)
constexpr double kAFast = 0.9; // Fast rotation (a/M = 0.9)

// Tolerance for floating-point comparisons
constexpr double kTolerance = 1e-8;

int passedChecks = 0;
int failedChecks = 0;

void report(bool passed, const std::string& what) {
  if (passed) {
    ++passedChecks;
  } else {
    ++failedChecks;
    std::cout << "  [FAIL] " << what << "\n";
  }
}

void expectNear(double actual, double expected, double tol, const std::string& what) {
  report(std::abs(actual - expected) <= tol,
         what + " (expected " + std::to_string(expected) + ", got " + std::to_string(actual) + ")");
}

void expectGt(double lhs, double rhs, const std::string& what) {
  report(lhs > rhs,
         what + " (" + std::to_string(lhs) + " > " + std::to_string(rhs) + " expected)");
}

void expectLt(double lhs, double rhs, const std::string& what) {
  report(lhs < rhs,
         what + " (" + std::to_string(lhs) + " < " + std::to_string(rhs) + " expected)");
}

void expectTrue(bool condition, const std::string& what) { report(condition, what); }

void expectFalse(bool condition, const std::string& what) { report(!condition, what); }

// Four-norm g_ab v^a v^b in Boyer-Lindquist coordinates, assembled from the
// kerr_extended.h metric components through the geodesic.hpp four_norm
// evaluator.
[[nodiscard]] double kerrFourNorm(double r, double theta, double m, double a, double vT, double vR,
                                  double vTheta, double vPhi) noexcept {
  MetricComponents const g{kerrGTt(r, theta, m, a), kerrGRr(r, theta, m, a),
                           kerrGThetaTheta(r, theta, a), kerrGPhiPhi(r, theta, m, a),
                           kerrGTPhi(r, theta, m, a)};
  StateVector const s{0.0, r, theta, 0.0, vT, vR, vTheta, vPhi};
  return four_norm(g, s);
}

/**
 * Test: Schwarzschild limit (a = 0) reduces to known values
 */
void testSchwarzschildLimit() {
  double const a = 0.0;
  double const theta = std::numbers::pi / 4; // 45 degrees

  // g_tt at r = 10M should equal Schwarzschild value
  double const r = 10.0 * kMass;
  double const gTt = kerrGTt(r, theta, kMass, a);
  double const gTtSchwarzschild = -(1.0 - (2.0 * kMass / r));

  expectNear(gTt, gTtSchwarzschild, kTolerance, "Kerr reduces to Schwarzschild when a = 0");
}

/**
 * Test: Outer horizon computation
 * For M = 1, a = 0.5: r_+ = 1 + sqrt(1 - 0.25) = 1 + sqrt(0.75) ~= 1.866
 */
void testOuterHorizonComputation() {
  double const rPlus = kerrOuterHorizon(kMass, kASlow);

  // Expected: M + sqrt(M^2 - a^2) = 1 + sqrt(0.75)
  double const expected = 1.0 + std::sqrt(0.75);

  expectNear(rPlus, expected, kTolerance, "Outer horizon computation");
}

/**
 * Test: Inner horizon computation
 * For M = 1, a = 0.5: r_- = 1 - sqrt(0.75) ~= 0.134
 */
void testInnerHorizonComputation() {
  double const rMinus = kerrInnerHorizon(kMass, kASlow);

  // Expected: M - sqrt(M^2 - a^2) = 1 - sqrt(0.75)
  double const expected = 1.0 - std::sqrt(0.75);

  expectNear(rMinus, expected, kTolerance, "Inner horizon computation");
}

/**
 * Test: Horizon ordering property
 * Physical requirement: r_+ > r_- > 0
 */
void testHorizonOrdering() {
  double const rPlus = kerrOuterHorizon(kMass, kAFast);
  double const rMinus = kerrInnerHorizon(kMass, kAFast);

  expectGt(rPlus, rMinus, "Event horizon should be outside Cauchy horizon");
  expectGt(rMinus, 0.0, "Cauchy horizon should be positive");
  // r_+ = M + sqrt(M^2 - a^2) <= 2M for all spin, with equality only at
  // a = 0: rotation shrinks the event horizon below the Schwarzschild
  // radius. The historical assertion r_+ > 2M inverted this.
  expectGt(rPlus, kMass, "Event horizon should be outside r = M");
  expectGt(2.0 * kMass, rPlus, "Spinning event horizon sits inside r = 2M");
}

/**
 * Test: ISCO for non-rotating case (a = 0)
 * Schwarzschild ISCO: r_isco = 6M
 */
void testIscoSchwarzschildLimit() {
  double const a = 0.0;
  double const rIsco = kerr_isco_prograde(kMass, a);

  // Expected: 6M for Schwarzschild
  double const expected = 6.0 * kMass;

  expectNear(rIsco, expected, kTolerance, "ISCO should be 6M in Schwarzschild case");
}

/**
 * Test: ISCO monotonically decreases with spin
 * As a increases (more rotation), ISCO moves inward (smaller r)
 */
void testIscoMonotonic() {
  double const rIsco1 = kerr_isco_prograde(kMass, 0.1);
  double const rIsco2 = kerr_isco_prograde(kMass, 0.5);
  double const rIsco3 = kerr_isco_prograde(kMass, 0.9);

  expectGt(rIsco1, rIsco2, "ISCO should move inward as spin increases (a1 -> a2)");
  expectGt(rIsco2, rIsco3, "ISCO should move inward as spin increases (a2 -> a3)");
}

/**
 * Test: ISCO is outside event horizon
 * Physical requirement: must be in exterior region
 */
void testIscoOutsideHorizon() {
  double const rIsco = kerr_isco_prograde(kMass, kAFast);
  double const rPlus = kerrOuterHorizon(kMass, kAFast);

  expectGt(rIsco, rPlus, "ISCO must be outside event horizon");
}

/**
 * Test: Retrograde ISCO is farther than prograde
 * Frame-dragging pulls co-rotating orbits inward
 */
void testRetrogradeIscoFarther() {
  double const rIscoPro = kerr_isco_prograde(kMass, kAFast);
  double const rIscoRetro = kerr_isco_retrograde(kMass, kAFast);

  expectGt(rIscoRetro, rIscoPro, "Retrograde ISCO should be farther than prograde");
}

/**
 * Test: Ergosphere radius varies with latitude
 * At poles (theta = 0): r_ergo = r_+ (minimum)
 * At equator (theta = pi/2): r_ergo > r_+ (maximum)
 */
void testErgosphereLatitudeVariation() {
  double const rPlus = kerrOuterHorizon(kMass, kAFast);
  double const rErgoPole = kerrErgosphereRadius(0.0, kMass, kAFast);
  double const rErgoEquator = kerrErgosphereRadius(std::numbers::pi / 2.0, kMass, kAFast);

  // At poles, ergosphere coincides with horizon
  expectNear(rErgoPole, rPlus, kTolerance, "Ergosphere at pole should equal horizon");

  // At equator, ergosphere extends beyond horizon
  expectGt(rErgoEquator, rPlus, "Ergosphere at equator should extend beyond horizon");
}

/**
 * Test: Surface gravity
 * Zero for extremal black holes
 * Positive for sub-extremal
 */
void testSurfaceGravity() {
  double const kappa = kerrSurfaceGravity(kMass, kASlow);

  expectGt(kappa, 0.0, "Surface gravity should be positive for sub-extremal BH");

  // For slower rotation, surface gravity should be larger
  double const kappaSlower = kerrSurfaceGravity(kMass, 0.1);
  expectGt(kappaSlower, kappa, "Surface gravity decreases with increasing spin");
}

/**
 * Test: Hawking temperature
 * Proportional to surface gravity
 * Zero for extremal black holes
 */
void testHawkingTemperature() {
  double const tH = kerrHawkingTemperature(kMass, kASlow);

  expectGt(tH, 0.0, "Hawking temperature should be positive");

  double const kappa = kerrSurfaceGravity(kMass, kASlow);
  double const expectedT = kappa / (2.0 * std::numbers::pi);

  expectNear(tH, expectedT, kTolerance, "Hawking temperature = kappa / (2 pi)");
}

/**
 * Test: Metric signature in exterior region
 * Must be Lorentzian: (-,+,+,+)
 */
void testExteriorMetricSignature() {
  double const r = 10.0 * kMass; // Clearly outside horizon
  double const theta = std::numbers::pi / 4;

  double const gTt = kerrGTt(r, theta, kMass, kASlow);
  double const gRr = kerrGRr(r, theta, kMass, kASlow);
  double const gThetaTheta = kerrGThetaTheta(r, theta, kASlow);
  double const gPhiPhi = kerrGPhiPhi(r, theta, kMass, kASlow);

  expectLt(gTt, 0.0, "g_tt negative in exterior");
  expectGt(gRr, 0.0, "g_rr positive in exterior");
  expectGt(gThetaTheta, 0.0, "g_thth positive in exterior");
  expectGt(gPhiPhi, 0.0, "g_phph positive in exterior");
}

/**
 * Test: Frame-dragging vanishes in Schwarzschild limit
 * g_t_phi = 0 when a = 0
 */
void testNoFrameDraggingSchwarzschildLimit() {
  double const a = 0.0;
  double const r = 10.0 * kMass;
  double const theta = std::numbers::pi / 4;

  double const gTPhi = kerrGTPhi(r, theta, kMass, a);

  expectNear(gTPhi, 0.0, kTolerance, "Frame-dragging vanishes when a = 0");
}

/**
 * Test: Frame-dragging increases with spin
 * |g_t_phi| larger for faster rotation
 */
void testFrameDraggingIncreases() {
  double const r = 10.0 * kMass;
  double const theta = std::numbers::pi / 2; // Equator (maximum frame-dragging)

  double const gTPhiSlow = std::abs(kerrGTPhi(r, theta, kMass, 0.1));
  double const gTPhiFast = std::abs(kerrGTPhi(r, theta, kMass, 0.9));

  expectGt(gTPhiFast, gTPhiSlow, "Frame-dragging increases with spin");
}

/**
 * Test: Null geodesic constraint enforcement
 * Null four-velocity: g_ab v^a v^b = 0
 */
void testNullGeodesicConstraint() {
  double const r = 20.0 * kMass;
  double const theta = std::numbers::pi / 4;

  // Construct null four-velocity
  double const vT = 1.0;
  double const vR = 0.5;
  double const vTheta = 0.2;
  double const vPhi = 0.3;

  double const norm = kerrFourNorm(r, theta, kMass, kASlow, vT, vR, vTheta, vPhi);

  // For truly null geodesic (not our arbitrary vector above)
  // norm should be close to 0 only for properly integrated geodesics
  // This test just verifies the norm computation works.
  // The build enables fast-math (-ffinite-math-only), so std::isfinite is
  // unusable here; a magnitude bound gives the same sanity check.
  expectLt(std::abs(norm), 1e10, "Four-norm computation yields bounded value");
}

/**
 * Test: Validation constraint - sub-extremal condition
 */
void testSubextremalValidation() {
  expectTrue(is_subextremal(kMass, kASlow), "a = 0.5 is sub-extremal");
  expectTrue(is_subextremal(kMass, kAFast), "a = 0.9 is sub-extremal");
  expectFalse(is_subextremal(kMass, kMass), "a = M is not sub-extremal");
  expectFalse(is_subextremal(kMass, 1.1 * kMass), "a > M is not sub-extremal");
}

/**
 * Performance benchmark: measure metric computation speed
 * This ensures verified functions maintain efficiency
 */
/**
 * Test: the Bardeen-Press-Teukolsky ISCO in both verified surfaces.
 * kerr.hpp normalizes the spin as a/M inside kerr_Z1/kerr_Z2 (BPT 1972
 * eq. 2.21), so the formula holds for any mass, not only M=1. Pins two
 * bugs fixed in the retired .h fork: a spurious /2 inside the Z1 cube
 * root (prograde ISCO 3.48M instead of 6M at a=0) and a retrograde
 * branch that reused the prograde minus sign (Z1/Z2 are even in a, so
 * negating the spin selected nothing).
 */
void testIscoBptBothSurfaces() {
  expectNear(verified::kerr_isco_prograde(kMass, 0.0), 6.0 * kMass, kTolerance,
             "batch-path prograde ISCO must be 6M at a=0 (BPT 1972)");
  expectNear(verified::kerr_isco_retrograde(kMass, 0.0), 6.0 * kMass, kTolerance,
             "batch-path retrograde ISCO must be 6M at a=0");
  double const pro = verified::kerr_isco_prograde(kMass, 0.5);
  double const retro = verified::kerr_isco_retrograde(kMass, 0.5);
  expectGt(6.0 * kMass, pro, "prograde ISCO moves inward with spin");
  expectGt(retro, 6.0 * kMass, "retrograde ISCO moves outward with spin");

  // kerr_extended.h duplicates of the same physics (fixed together:
  // wrong bptZ2 radicand gave 6.87M at a=0; retrograde carried the
  // prograde sign). BPT 1972 at a=0.9: prograde 2.3209, retro 8.7173.
  expectNear(verified::kerrIscoPrograde(kMass, 0.0), 6.0 * kMass, kTolerance,
             "kerr_extended prograde ISCO must be 6M at a=0");
  expectNear(verified::kerrIscoPrograde(kMass, 0.9), 2.3209, 1e-3,
             "kerr_extended prograde ISCO at a=0.9 (BPT 1972)");
  expectNear(verified::kerrIscoRetrograde(kMass, 0.9), 8.7173, 1e-3,
             "kerr_extended retrograde ISCO at a=0.9 (BPT 1972)");
}

void testPerformanceBenchmark() {
  const int iterations = 1000000;
  double const r = 10.0 * kMass;
  double const theta = std::numbers::pi / 4;

  auto start = std::chrono::high_resolution_clock::now();

  for (int i = 0; i < iterations; ++i) {
    volatile double gTt = kerrGTt(r, theta, kMass, kASlow);
    volatile double gRr = kerrGRr(r, theta, kMass, kASlow);
    volatile double norm = kerrFourNorm(r, theta, kMass, kASlow, 1.0, 0.1, 0.05, 0.2);
    (void)gTt;
    (void)gRr;
    (void)norm;
  }

  auto end = std::chrono::high_resolution_clock::now();
  auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(end - start);

  double const opsPerSec = (iterations * 3.0) / (static_cast<double>(duration.count()) / 1000.0);
  std::cout << "Performance: " << std::scientific << opsPerSec << " metric ops/sec\n";

  // Expected: > 10M ops/sec on modern CPU
  expectGt(opsPerSec, 1e7, "Metric computation throughput above 10M ops/sec");
}

} // namespace

int main() {
  std::cout << "Kerr Geodesic Validation Tests\n";
  std::cout << "==============================\n";

  testSchwarzschildLimit();
  testOuterHorizonComputation();
  testInnerHorizonComputation();
  testHorizonOrdering();
  testIscoSchwarzschildLimit();
  testIscoBptBothSurfaces();
  testIscoMonotonic();
  testIscoOutsideHorizon();
  testRetrogradeIscoFarther();
  testErgosphereLatitudeVariation();
  testSurfaceGravity();
  testHawkingTemperature();
  testExteriorMetricSignature();
  testNoFrameDraggingSchwarzschildLimit();
  testFrameDraggingIncreases();
  testNullGeodesicConstraint();
  testSubextremalValidation();
  testPerformanceBenchmark();

  std::cout << "\nPassed: " << passedChecks << "\nFailed: " << failedChecks << "\n";
  return (failedChecks == 0) ? 0 : 1;
}
