/**
 * @file eht_shadow_test.cpp
 * @brief Analytic Schwarzschild shadow-size self-consistency checks.
 *
 * The angular size of a black-hole shadow seen by a distant observer is set by
 * the critical impact parameter for photon capture, b_c = 3 sqrt(3) M (geometric
 * mass length M = GM/c^2), equivalently b_c = (3 sqrt(3) / 2) r_s ~ 2.598 r_s.
 * A photon aimed with impact parameter below b_c is captured; above it, it
 * escapes. The apparent shadow radius on the observer's sky is b_c / D, so the
 * angular diameter is 2 b_c / D.
 *
 * These tests exercise that closed form and its scaling laws directly. They do
 * NOT render an image, integrate a geodesic, or model emission. The shadow
 * *size* is a robust geometric prediction of the metric; the ring brightness,
 * polarization, and Kerr asymmetry are emission-dependent and must be validated
 * against real rendered output, not a hand-authored image. A prior version of
 * this file built a synthetic 2D image, used the photon-orbit coordinate radius
 * 1.5 r_s (= 3 M) as the shadow radius instead of b_c, halved an angular radius
 * a second time as if it were a diameter, and painted the shadow interior bright
 * -- producing ~18 uas for M87* and then accepting a 10-25 uas band. Using b_c
 * the same parameters give ~40 uas (M87*) and ~51 uas (Sgr A*), consistent with
 * the EHT-measured ring diameters. The bright emission ring the EHT resolves is
 * set by, but not identical to, the b_c critical curve, so these checks assert
 * the analytic shadow scale and its proximity to the ring diameters, not an
 * exact match to a measured geometric shadow.
 *
 * References:
 * - Event Horizon Telescope Collaboration (2019) ApJ 875, L1 (M87* shadow ~42 uas).
 * - Event Horizon Telescope Collaboration (2022) ApJ 930, L12 (Sgr A* shadow ~52 uas).
 * - Psaltis et al. (2020) ApJ 905, L8 (shadow-size measurement and b_c).
 */

#include <algorithm>
#include <cmath>
#include <iomanip>
#include <iostream>
#include <numbers>

namespace {

// Physical constants (SI).
constexpr double GRAV = 6.67430e-11;      // [m^3 kg^-1 s^-2]
constexpr double LIGHT_SPEED = 2.99792458e8; // [m/s]
constexpr double SOLAR_MASS = 1.989e30;   // [kg]
constexpr double MPC = 3.086e22;          // [m]

// Radians to microarcseconds.
constexpr double RAD_TO_UAS = (180.0 * 3600.0 / std::numbers::pi) * 1e6;

// Source parameters and EHT-measured ring diameters. The ring value is context
// for the size tests; those gate on the closed form and check proximity to the
// ring diameter with a loose astrophysical tolerance, since the emission ring is
// set by, but not identical to, the b_c critical curve.
constexpr double M87_MASS = 6.5e9;        // [Msun]
constexpr double M87_DISTANCE = 16.8;     // [Mpc]
constexpr double M87_RING_UAS = 42.0;     // EHT 2019 ring diameter

constexpr double SGRA_MASS = 4.1e6;       // [Msun]
constexpr double SGRA_DISTANCE = 0.0082;  // [Mpc] (8.2 kpc)
constexpr double SGRA_RING_UAS = 52.0;    // EHT 2022 ring diameter

// Geometric mass length M = GM/c^2 [m]. The Schwarzschild radius is 2 M.
double geometricMassLength(double massSolar) {
  return GRAV * massSolar * SOLAR_MASS / (LIGHT_SPEED * LIGHT_SPEED);
}

double schwarzschildRadius(double massSolar) { return 2.0 * geometricMassLength(massSolar); }

// Critical impact parameter for photon capture, b_c = 3 sqrt(3) M.
double criticalImpactParameter(double massSolar) {
  return 3.0 * std::numbers::sqrt3 * geometricMassLength(massSolar);
}

// Apparent shadow angular diameter [uas] for a distant observer at distanceMpc.
double shadowAngularDiameterUas(double massSolar, double distanceMpc) {
  double const bc = criticalImpactParameter(massSolar);
  double const distanceM = distanceMpc * MPC;
  double const angularRadius = std::atan(bc / distanceM); // radians
  return 2.0 * angularRadius * RAD_TO_UAS;
}

bool approxEqual(double lhs, double rhs, double relTolerance) {
  double const scale = std::max(std::abs(lhs), std::abs(rhs));
  return std::abs(lhs - rhs) <= relTolerance * scale;
}

// Test 1: b_c is the capture radius 3 sqrt(3) M = 2.598 r_s, not the photon
// sphere 1.5 r_s. Guards against reintroducing the photon-orbit-radius bug.
bool testCriticalImpactParameterIdentity() {
  double const bc = criticalImpactParameter(M87_MASS);
  double const rs = schwarzschildRadius(M87_MASS);
  double const ratio = bc / rs;                 // expect 1.5 sqrt(3) ~ 2.598
  double const expected = 1.5 * std::numbers::sqrt3;

  bool const matchesClosedForm = approxEqual(ratio, expected, 1e-12);
  bool const distinctFromPhotonSphere = std::abs(ratio - 1.5) > 1.0;
  bool const pass = matchesClosedForm && distinctFromPhotonSphere;

  std::cout << "Test 1: critical impact parameter identity\n"
            << "  b_c / r_s: " << std::fixed << std::setprecision(6) << ratio << "\n"
            << "  expected (1.5*sqrt(3)): " << expected << "\n"
            << "  photon-sphere radius (rejected): 1.5\n"
            << "  Status: " << (pass ? "PASS" : "FAIL") << "\n\n";
  return pass;
}

// Test 2: M87* shadow diameter from b_c matches the closed form and is
// consistent with the EHT ring diameter of ~42 uas.
bool testM87ShadowDiameter() {
  double const diameter = shadowAngularDiameterUas(M87_MASS, M87_DISTANCE);
  double const bc = criticalImpactParameter(M87_MASS);
  double const closedForm = 2.0 * std::atan(bc / (M87_DISTANCE * MPC)) * RAD_TO_UAS;

  bool const selfConsistent = approxEqual(diameter, closedForm, 1e-12);
  bool const nearRing = approxEqual(diameter, M87_RING_UAS, 0.15);
  bool const pass = selfConsistent && nearRing;

  std::cout << "Test 2: M87* shadow angular diameter\n"
            << "  b_c closed form:  " << std::fixed << std::setprecision(2) << diameter << " uas\n"
            << "  EHT ring diameter: " << M87_RING_UAS << " uas\n"
            << "  Status: " << (pass ? "PASS" : "FAIL") << "\n\n";
  return pass;
}

// Test 3: Sgr A* shadow diameter from b_c is consistent with the EHT ring
// diameter of ~52 uas.
bool testSgrAShadowDiameter() {
  double const diameter = shadowAngularDiameterUas(SGRA_MASS, SGRA_DISTANCE);
  bool const nearRing = approxEqual(diameter, SGRA_RING_UAS, 0.15);

  std::cout << "Test 3: Sgr A* shadow angular diameter\n"
            << "  b_c closed form:  " << std::fixed << std::setprecision(2) << diameter << " uas\n"
            << "  EHT ring diameter: " << SGRA_RING_UAS << " uas\n"
            << "  Status: " << (nearRing ? "PASS" : "FAIL") << "\n\n";
  return nearRing;
}

// Test 4: shadow diameter scales linearly with mass (b_c ~ M).
bool testMassLinearScaling() {
  double const d1 = shadowAngularDiameterUas(M87_MASS, M87_DISTANCE);
  double const d2 = shadowAngularDiameterUas(2.0 * M87_MASS, M87_DISTANCE);
  double const ratio = d2 / d1;
  bool const pass = approxEqual(ratio, 2.0, 1e-6);

  std::cout << "Test 4: mass linear scaling\n"
            << "  diameter(2M) / diameter(M): " << std::fixed << std::setprecision(4) << ratio
            << " (expected 2.0)\n"
            << "  Status: " << (pass ? "PASS" : "FAIL") << "\n\n";
  return pass;
}

// Test 5: shadow diameter scales inversely with distance (angular size ~ 1/D).
bool testDistanceInverseScaling() {
  double const d1 = shadowAngularDiameterUas(M87_MASS, M87_DISTANCE);
  double const d2 = shadowAngularDiameterUas(M87_MASS, 2.0 * M87_DISTANCE);
  double const ratio = d1 / d2;
  bool const pass = approxEqual(ratio, 2.0, 1e-6);

  std::cout << "Test 5: distance inverse scaling\n"
            << "  diameter(D) / diameter(2D): " << std::fixed << std::setprecision(4) << ratio
            << " (expected 2.0)\n"
            << "  Status: " << (pass ? "PASS" : "FAIL") << "\n\n";
  return pass;
}

// Test 6: shadow area scales as M^2 (diameter ~ M, area ~ diameter^2).
bool testAreaScalesWithMassSquared() {
  double const d1 = shadowAngularDiameterUas(M87_MASS, M87_DISTANCE);
  double const d2 = shadowAngularDiameterUas(2.0 * M87_MASS, M87_DISTANCE);
  double const areaRatio = (d2 * d2) / (d1 * d1);
  bool const pass = approxEqual(areaRatio, 4.0, 1e-6);

  std::cout << "Test 6: shadow area scales as mass squared\n"
            << "  area(2M) / area(M): " << std::fixed << std::setprecision(4) << areaRatio
            << " (expected 4.0)\n"
            << "  Status: " << (pass ? "PASS" : "FAIL") << "\n\n";
  return pass;
}

} // namespace

int main() {
  std::cout << "\n"
            << "====================================================\n"
            << "ANALYTIC SHADOW-SIZE SELF-CONSISTENCY (SCHWARZSCHILD)\n"
            << "====================================================\n\n";

  int passed = 0;
  int const total = 6;

  if (testCriticalImpactParameterIdentity()) {
    passed++;
  }
  if (testM87ShadowDiameter()) {
    passed++;
  }
  if (testSgrAShadowDiameter()) {
    passed++;
  }
  if (testMassLinearScaling()) {
    passed++;
  }
  if (testDistanceInverseScaling()) {
    passed++;
  }
  if (testAreaScalesWithMassSquared()) {
    passed++;
  }

  std::cout << "====================================================\n"
            << "RESULTS: " << passed << "/" << total << " tests passed\n"
            << "====================================================\n\n";

  return (passed == total) ? 0 : 1;
}
