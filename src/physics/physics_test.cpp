/**
 * physics_test.cpp
 * Validation tests for physics library calculations.
 *
 * Compares cleanroom C++ implementation against known reference values.
 * Reference: OpenUniverse compact domain physics formulas.
 *
 * To build and run:
 *   g++ -std=c++23 -I../.. physics_test.cpp schwarzschild.cpp geodesics.cpp cosmology.cpp -o physics_test && ./physics_test
 */

#include <algorithm>
#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

#include <numbers>

#include "constants.h"
#include "cosmology.h"
#include "geodesics.h"
#include "kerr.h"
#include "lut.h"
#include "raytracer.h"
#include "schwarzschild.h"

namespace {

constexpr double TOLERANCE = 1e-10;

bool approxEqual(double a, double b, double tol = TOLERANCE) {
  if (std::abs(b) < 1e-30) {
    return std::abs(a) < tol;
  }
  return std::abs(a - b) / std::abs(b) < tol;
}

struct TestResult {
  std::string name;
  double expected;
  double actual;
  bool passed;
};

void printResult(const TestResult &r) {
  std::cout << (r.passed ? "[PASS]" : "[FAIL]") << " " << r.name << "\n"
            << "  Expected: " << std::scientific << std::setprecision(10)
            << r.expected << "\n"
            << "  Actual:   " << r.actual << "\n";
  if (!r.passed) {
    double const relErr = std::abs(r.actual - r.expected) / std::abs(r.expected);
    std::cout << "  Rel.Err:  " << relErr << "\n";
  }
  std::cout << "\n";
}

bool readTextFile(const std::string &path, std::string &out) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::ostringstream buffer;
  buffer << file.rdbuf();
  out = buffer.str();
  return !out.empty();
}

bool parseJsonNumber(const std::string &text, const std::string &key, double &out) {
  std::string const needle = "\"" + key + "\"";
  std::size_t pos = text.find(needle);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find(':', pos);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find_first_of("+-0123456789.", pos);
  if (pos == std::string::npos) {
    return false;
  }
  const char *start = text.c_str() + pos;
  char *end = nullptr;
  out = std::strtod(start, &end);
  return end != start;
}

bool parseJsonString(const std::string &text, const std::string &key, std::string &out) {
  std::string const needle = "\"" + key + "\"";
  std::size_t pos = text.find(needle);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find(':', pos);
  if (pos == std::string::npos) {
    return false;
  }
  pos = text.find('"', pos);
  if (pos == std::string::npos) {
    return false;
  }
  std::size_t const end = text.find('"', pos + 1);
  if (end == std::string::npos || end <= pos + 1) {
    return false;
  }
  out = text.substr(pos + 1, end - pos - 1);
  return !out.empty();
}

bool loadLutCsv(const std::string &path, std::vector<float> &values) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::string line;
  bool first = true;
  while (std::getline(file, line)) {
    if (first) {
      first = false;
      continue;
    }
    if (line.empty()) {
      continue;
    }
    std::size_t const comma = line.find(',');
    if (comma == std::string::npos) {
      continue;
    }
    const char *start = line.c_str() + comma + 1;
    char *end = nullptr;
    double value = std::strtod(start, &end);
    if (end == start) {
      continue;
    }
    values.push_back(static_cast<float>(value));
  }
  return !values.empty();
}

bool loadLutMeta(double &massSolar, double &spin, double &mdot, double &rInOverRs,
                 double &rOutOverRs) {
  std::string metaText;
  if (!readTextFile("assets/luts/lut_meta.json", metaText)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "mass_solar", massSolar)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "spin", spin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "mdot", mdot)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_in_over_rs", rInOverRs)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_out_over_rs", rOutOverRs)) {
    return false;
  }
  return true;
}

bool loadValidationMeta(double &massSolar, double &spin, double &rS, double &rIco, double &rPh,
                        double &rMinOverRs, double &rMaxOverRs, std::string &source) {
  std::string metaText;
  if (!readTextFile("assets/validation/metrics.json", metaText)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "mass_solar", massSolar)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "spin", spin)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_s_cm", rS)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_isco_cm", rIco)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_ph_cm", rPh)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_min_over_rs", rMinOverRs)) {
    return false;
  }
  if (!parseJsonNumber(metaText, "r_max_over_rs", rMaxOverRs)) {
    return false;
  }
  parseJsonString(metaText, "source", source);
  return true;
}

bool loadCurveCsv(const std::string &path, std::vector<double> &rOverRs,
                  std::vector<double> &values) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::string line;
  bool first = true;
  while (std::getline(file, line)) {
    if (first) {
      first = false;
      continue;
    }
    if (line.empty()) {
      continue;
    }
    std::size_t const comma = line.find(',');
    if (comma == std::string::npos) {
      continue;
    }
    const char *rStart = line.c_str();
    char *rEnd = nullptr;
    double const rVal = std::strtod(rStart, &rEnd);
    if (rEnd == rStart) {
      continue;
    }
    const char *vStart = line.c_str() + comma + 1;
    char *vEnd = nullptr;
    double const vVal = std::strtod(vStart, &vEnd);
    if (vEnd == vStart) {
      continue;
    }
    rOverRs.push_back(rVal);
    values.push_back(vVal);
  }
  return !rOverRs.empty() && rOverRs.size() == values.size();
}

bool loadSpinCurveCsv(const std::string &path, std::vector<double> &spins,
                      std::vector<double> &iscoOverRs, std::vector<double> &phOverRs) {
  std::ifstream file(path);
  if (!file.is_open()) {
    return false;
  }
  std::string line;
  bool first = true;
  while (std::getline(file, line)) {
    if (first) {
      first = false;
      continue;
    }
    if (line.empty()) {
      continue;
    }
    std::size_t const comma1 = line.find(',');
    if (comma1 == std::string::npos) {
      continue;
    }
    std::size_t const comma2 = line.find(',', comma1 + 1);
    if (comma2 == std::string::npos) {
      continue;
    }
    const char *sStart = line.c_str();
    char *sEnd = nullptr;
    double const spinVal = std::strtod(sStart, &sEnd);
    if (sEnd == sStart) {
      continue;
    }
    const char *iscoStart = line.c_str() + comma1 + 1;
    char *iscoEnd = nullptr;
    double const iscoVal = std::strtod(iscoStart, &iscoEnd);
    if (iscoEnd == iscoStart) {
      continue;
    }
    const char *phStart = line.c_str() + comma2 + 1;
    char *phEnd = nullptr;
    double const phVal = std::strtod(phStart, &phEnd);
    if (phEnd == phStart) {
      continue;
    }
    spins.push_back(spinVal);
    iscoOverRs.push_back(iscoVal);
    phOverRs.push_back(phVal);
  }
  return !spins.empty() && spins.size() == iscoOverRs.size() && spins.size() == phOverRs.size();
}

int runTests() { // NOLINT(readability-function-cognitive-complexity) -- test harness, high complexity is acceptable
  int passed = 0;
  int failed = 0;

  std::cout << "=== Physics Library Validation Tests ===\n\n";

  // Test 1: Schwarzschild radius for 1 solar mass
  // r_s = 2GM/c^2 = 2 * 6.67430e-8 * 1.98841e33 / (2.99792458e10)^2
  // r_s = 2.95325e5 cm = 2.95325 km
  {
    double const mass = physics::M_SUN; // 1 solar mass in grams
    double const rS = physics::schwarzschildRadius(mass);
    double const expected = 2.9532500765e5; // cm (verified value)

    TestResult const r{.name = "Schwarzschild radius (1 M_sun)",
                       .expected = expected,
                       .actual = rS,
                       .passed = approxEqual(rS, expected, 1e-6)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 2: Schwarzschild radius for 4 million solar masses (Sgr A*)
  // This is the supermassive black hole at the center of our galaxy
  {
    double const mass = 4.0e6 * physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const expected = 1.1813e12; // cm (~0.08 AU)

    TestResult const r{.name = "Schwarzschild radius (4e6 M_sun, Sgr A*)",
                       .expected = expected,
                       .actual = rS,
                       .passed = approxEqual(rS, expected, 1e-4)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 3: Photon sphere radius = 1.5 * r_s
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const rPh = physics::photonSphereRadius(mass);
    double const expected = 1.5 * rS;

    TestResult const r{.name = "Photon sphere radius = 1.5 r_s",
                       .expected = expected,
                       .actual = rPh,
                       .passed = approxEqual(rPh, expected)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 4: ISCO radius = 3 * r_s (for Schwarzschild)
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const rIsco = physics::iscoRadius(mass);
    double const expected = 3.0 * rS;

    TestResult const r{.name = "ISCO radius = 3 r_s",
                       .expected = expected,
                       .actual = rIsco,
                       .passed = approxEqual(rIsco, expected)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 5: Gravitational redshift at r = 2 r_s (just above horizon)
  // z = 1/sqrt(1 - r_s/r) - 1 = 1/sqrt(1/2) - 1 = sqrt(2) - 1 ~ 0.414
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const r = 2.0 * rS;
    double const z = physics::gravitationalRedshift(r, mass);
    double const expected = std::numbers::sqrt2 - 1.0;

    TestResult const rTest{.name = "Gravitational redshift at r=2r_s",
                           .expected = expected,
                           .actual = z,
                           .passed = approxEqual(z, expected)};
    printResult(rTest);
    rTest.passed ? ++passed : ++failed;
  }

  // Test 6: Gravitational redshift at r = 10 r_s
  // z = 1/sqrt(1 - 0.1) - 1 = 1/sqrt(0.9) - 1 ~ 0.0541
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const r = 10.0 * rS;
    double const z = physics::gravitationalRedshift(r, mass);
    double const expected = (1.0 / std::sqrt(0.9)) - 1.0;

    TestResult const rTest{.name = "Gravitational redshift at r=10r_s",
                           .expected = expected,
                           .actual = z,
                           .passed = approxEqual(z, expected)};
    printResult(rTest);
    rTest.passed ? ++passed : ++failed;
  }

  // Test 7: Critical impact parameter for photon capture
  // b_crit = sqrt(27) * r_s / 2 ~ 2.598 * r_s
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const bCrit = physics::criticalImpactParameter(mass);
    double const expected = std::sqrt(27.0) * rS / 2.0;

    TestResult const r{.name = "Critical impact parameter",
                       .expected = expected,
                       .actual = bCrit,
                       .passed = approxEqual(bCrit, expected)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 8: Escape velocity at r = 2 r_s
  // v_esc = c * sqrt(r_s/r) = c * sqrt(1/2) ~ 0.707 c
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const r = 2.0 * rS;
    double const vEsc = physics::escapeVelocity(r, mass);
    double const expected = physics::C * std::sqrt(0.5);

    TestResult const rTest{.name = "Escape velocity at r=2r_s",
                           .expected = expected,
                           .actual = vEsc,
                           .passed = approxEqual(vEsc, expected)};
    printResult(rTest);
    rTest.passed ? ++passed : ++failed;
  }

  // Test 9: Light deflection angle for large impact parameter
  // delta_phi ~ 4GM/(b*c^2) for b >> r_s
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const b = 1000.0 * rS; // Far from black hole
    double const deltaPhi = physics::gravitationalDeflection(b, mass);
    double const expected = 2.0 * rS / b; // First-order approximation

    TestResult const r{.name = "Light deflection (weak field)",
                       .expected = expected,
                       .actual = deltaPhi,
                       .passed = approxEqual(deltaPhi, expected, 1e-3)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 10: Hubble parameter E(z=0) should equal 1
  {
    double const e = physics::hubbleE(0.0);
    double const expected = 1.0;

    TestResult const r{.name = "Hubble E(z=0) = 1",
                       .expected = expected,
                       .actual = e,
                       .passed = approxEqual(e, expected)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 11: Kerr ISCO reduces to Schwarzschild when a=0
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const a = 0.0;
    double const rIsco = physics::kerrIscoRadius(mass, a, true);
    double const expected = 3.0 * rS;

    TestResult const r{.name = "Kerr ISCO (a=0) == 3 r_s",
                       .expected = expected,
                       .actual = rIsco,
                       .passed = approxEqual(rIsco, expected, 1e-6)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 12: Kerr photon orbit reduces to Schwarzschild when a=0
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const a = 0.0;
    double const rPh = physics::kerrPhotonOrbitPrograde(mass, a);
    double const expected = 1.5 * rS;

    TestResult const r{.name = "Kerr photon orbit (a=0) == 1.5 r_s",
                       .expected = expected,
                       .actual = rPh,
                       .passed = approxEqual(rPh, expected, 1e-6)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 13: Extreme Kerr prograde ISCO at a*=1 -> r_ISCO = M (0.5 r_s)
  {
    double const mass = physics::M_SUN;
    double const mGeom = physics::G * mass / physics::C2;
    double const a = mGeom;
    double const rS = physics::schwarzschildRadius(mass);
    double const expected = 0.5 * rS;
    double const rIsco = physics::kerrIscoRadius(mass, a, true);

    TestResult const r{.name = "Kerr ISCO prograde (a*=1)",
                       .expected = expected,
                       .actual = rIsco,
                       .passed = approxEqual(rIsco, expected, 1e-4)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 14: Extreme Kerr retrograde ISCO at a*=1 -> r_ISCO = 9M (4.5 r_s)
  {
    double const mass = physics::M_SUN;
    double const mGeom = physics::G * mass / physics::C2;
    double const a = mGeom;
    double const rS = physics::schwarzschildRadius(mass);
    double const expected = 4.5 * rS;
    double const rIsco = physics::kerrIscoRadius(mass, a, false);

    TestResult const r{.name = "Kerr ISCO retrograde (a*=1)",
                       .expected = expected,
                       .actual = rIsco,
                       .passed = approxEqual(rIsco, expected, 1e-4)};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 15: Kerr horizons reduce to Schwarzschild when a=0
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    auto horizons = physics::kerrHorizons(mass, 0.0);
    bool const ok =
        approxEqual(horizons.first, rS, 1e-8) && approxEqual(horizons.second, 0.0, 1e-8);

    TestResult const r{
        .name = "Kerr horizons (a=0)", .expected = 1.0, .actual = ok ? 1.0 : 0.0, .passed = ok};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 16: Invalid spin returns NaN
  {
    double const mass = physics::M_SUN;
    double const mGeom = physics::G * mass / physics::C2;
    double const a = 1.2 * mGeom;
    double const rIsco = physics::kerrIscoRadius(mass, a, true);
    double const rPh = physics::kerrPhotonOrbitPrograde(mass, a);
    bool const ok = std::isnan(rIsco) && std::isnan(rPh);

    TestResult const r{.name = "Kerr invalid spin -> NaN",
                       .expected = 1.0,
                       .actual = ok ? 1.0 : 0.0,
                       .passed = ok};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 17: Kerr redshift at a=0 matches Schwarzschild in equatorial plane
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const radius = 10.0 * rS;
    double const zSchw = physics::gravitationalRedshift(radius, mass);
    double const zKerr = physics::kerrRedshift(radius, 0.5 * physics::PI, mass, 0.0);

    TestResult const result{.name = "Kerr redshift (a=0) == Schwarzschild",
                            .expected = zSchw,
                            .actual = zKerr,
                            .passed = approxEqual(zKerr, zSchw, 1e-6)};
    printResult(result);
    result.passed ? ++passed : ++failed;
  }

  // Test 18: Kerr photon orbit potentials vanish at a=0 photon sphere
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const mGeom = physics::G * mass / physics::C2;
    double const r = 1.5 * rS; // 3M
    double const a = 0.0;

    physics::KerrGeodesicConsts c{};
    c.e = 1.0;
    c.lz = 3.0 * std::numbers::sqrt3 * mGeom;
    c.q = 0.0;

    physics::KerrPotentials const pot = physics::kerrPotentials(r, 0.5 * physics::PI, mass, a, c);

    double const scaleR = mGeom * mGeom * mGeom * mGeom;
    double const scaleD = mGeom * mGeom * mGeom;
    bool const rOk = std::abs(pot.rPot) / scaleR < 1e-6;
    bool const dOk = std::abs(pot.dRdr) / scaleD < 1e-6;

    TestResult const rPot{.name = "Kerr R potential at photon orbit",
                          .expected = 0.0,
                          .actual = pot.rPot,
                          .passed = rOk};
    TestResult const dPot{
        .name = "Kerr dR/dr at photon orbit", .expected = 0.0, .actual = pot.dRdr, .passed = dOk};
    printResult(rPot);
    printResult(dPot);
    rPot.passed ? ++passed : ++failed;
    dPot.passed ? ++passed : ++failed;
  }

  // Test 19: Kerr turning point potential vanishes (a=0, equatorial)
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const mGeom = physics::G * mass / physics::C2;
    double const r = 4.0 * rS; // turning point radius
    double const a = 0.0;

    physics::KerrGeodesicConsts c{};
    c.e = 1.0;
    c.lz = std::sqrt((r * r * r) / (r - rS)); // Lz^2 = r^3 / (r - r_s)
    c.q = 0.0;

    physics::KerrPotentials const pot = physics::kerrPotentials(r, 0.5 * physics::PI, mass, a, c);

    double const scaleR = mGeom * mGeom * mGeom * mGeom;
    bool const ok = std::abs(pot.rPot) / scaleR < 1e-6;

    TestResult const rPot{
        .name = "Kerr turning point R=0", .expected = 0.0, .actual = pot.rPot, .passed = ok};
    printResult(rPot);
    rPot.passed ? ++passed : ++failed;
  }

  // Test 20: Kerr raytracer produces finite output (a=0)
  {
    double const mass = physics::M_SUN;
    double const rS = physics::schwarzschildRadius(mass);
    double const mGeom = physics::G * mass / physics::C2;
    double const a = 0.0;

    physics::KerrRaytracer const tracer(mass, a);
    double const impact = 3.0 * std::numbers::sqrt3 * mGeom;
    physics::KerrGeodesicConsts const c = physics::kerrEquatorialConsts(impact, 1.0);
    physics::KerrGeodesicState const state = physics::kerrEquatorialState(10.0 * rS, 0.0, -1.0);

    auto result = tracer.trace(state, c);
    // NOLINT(cppcoreguidelines-pro-bounds-avoid-unchecked-container-access): Vec3d subscripts
    bool const finite = std::isfinite(result.finalPosition[0]) && // NOLINT
                        std::isfinite(result.finalPosition[1]) && // NOLINT
                        std::isfinite(result.finalPosition[2]);   // NOLINT

    TestResult const r{.name = "Kerr raytracer finite output",
                       .expected = 1.0,
                       .actual = finite ? 1.0 : 0.0,
                       .passed = finite};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 21: Spin radii LUT matches Schwarzschild for spin=0
  {
    auto lut = physics::generateSpinRadiiLut(4, 1.0, 0.0, 0.0);
    bool const ok = !lut.spins.empty() && std::abs(lut.rIscoOverRs.front() - 3.0f) < 1e-4f &&
                    std::abs(lut.rPhOverRs.front() - 1.5f) < 1e-4f;

    TestResult const r{
        .name = "Spin radii LUT (a=0)", .expected = 1.0, .actual = ok ? 1.0 : 0.0, .passed = ok};
    printResult(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 22: LUT assets match CPU reference (emissivity + redshift)
  {
    std::vector<float> emissivity;
    std::vector<float> redshift;
    double massSolar = 0.0;
    double spin = 0.0;
    double mdot = 0.0;
    double rInOverRs = 0.0;
    double rOutOverRs = 0.0;

    bool const hasCsv = loadLutCsv("assets/luts/emissivity_lut.csv", emissivity) &&
                        loadLutCsv("assets/luts/redshift_lut.csv", redshift);
    bool const hasMeta = loadLutMeta(massSolar, spin, mdot, rInOverRs, rOutOverRs);
    bool const hasAssets = hasCsv && hasMeta && emissivity.size() == redshift.size();

    TestResult const assetsPresent{.name = "LUT assets present",
                                   .expected = 1.0,
                                   .actual = hasAssets ? 1.0 : 0.0,
                                   .passed = hasAssets};
    printResult(assetsPresent);
    assetsPresent.passed ? ++passed : ++failed;

    if (hasAssets) {
      const std::size_t count = emissivity.size();
      const double mass = massSolar * physics::M_SUN;
      const double rS = physics::schwarzschildRadius(mass);
      const double rG = physics::G * mass / physics::C2;
      const double a = spin * rG;
      const double rIn = rInOverRs * rS;
      const double rOut = rOutOverRs * rS;

      double const lEdd = 1.26e38 * massSolar;
      double const mdotEdd = lEdd / (0.1 * physics::C2);
      double mdotCgs = mdot * mdotEdd;
      auto emissivityModel = [&](double r) {
        if (r < rIn) {
          return 0.0;
        }
        double const prefactor = 3.0 * physics::G * mass * mdotCgs / (8.0 * physics::PI * r * r * r);
        double const basic = 1.0 - std::sqrt(rIn / r);
        double const spinFactor = 1.0 + (0.5 * spin * std::sqrt(rG / r));
        return prefactor * basic * spinFactor;
      };

      double maxFlux = 0.0;
      std::vector<double> fluxes(count, 0.0);
      for (std::size_t i = 0; i < count; ++i) {
        double const u = static_cast<double>(i) / static_cast<double>(count - 1);
        double const r = rIn + (u * (rOut - rIn));
        double flux = emissivityModel(r);
        if (!std::isfinite(flux) || flux < 0.0) {
          flux = 0.0;
        }
        fluxes.at(i) = flux;
        maxFlux = std::max(maxFlux, flux);
      }

      double maxEmissDiff = 0.0;
      double maxRedshiftDiff = 0.0;
      for (std::size_t i = 0; i < count; ++i) {
        double const expectedEmiss = (maxFlux > 0.0) ? fluxes.at(i) / maxFlux : 0.0;
        auto const actualEmiss = static_cast<double>(emissivity.at(i));
        maxEmissDiff = std::max(maxEmissDiff, std::abs(expectedEmiss - actualEmiss));

        double const u = static_cast<double>(i) / static_cast<double>(count - 1);
        double const r = rIn + (u * (rOut - rIn));
        double expectedRedshift = physics::kerrRedshift(r, 0.5 * physics::PI, mass, a);
        if (!std::isfinite(expectedRedshift) || expectedRedshift < 0.0) {
          expectedRedshift = 0.0;
        }
        expectedRedshift = std::min(expectedRedshift, 10.0);
        auto const actualRedshift = static_cast<double>(redshift.at(i));
        maxRedshiftDiff = std::max(maxRedshiftDiff, std::abs(expectedRedshift - actualRedshift));
      }

      TestResult const emissivityResult{.name = "LUT emissivity max abs diff",
                                        .expected = 0.0,
                                        .actual = maxEmissDiff,
                                        .passed = maxEmissDiff <= 2e-3};
      printResult(emissivityResult);
      emissivityResult.passed ? ++passed : ++failed;

      TestResult const redshiftResult{.name = "LUT redshift max abs diff",
                                      .expected = 0.0,
                                      .actual = maxRedshiftDiff,
                                      .passed = maxRedshiftDiff <= 2e-3};
      printResult(redshiftResult);
      redshiftResult.passed ? ++passed : ++failed;
    }
  }

  // Test 17: Validation curve assets (redshift)
  {
    double massSolar = 0.0;
    double spin = 0.0;
    double rS = 0.0;
    double rIco = 0.0;
    double rPh = 0.0;
    double rMinOverRs = 0.0;
    double rMaxOverRs = 0.0;
    std::string source;
    std::vector<double> rOverRs;
    std::vector<double> zValues;

    bool const hasMeta =
        loadValidationMeta(massSolar, spin, rS, rIco, rPh, rMinOverRs, rMaxOverRs, source);
    bool const hasCurve = loadCurveCsv("assets/validation/redshift_curve.csv", rOverRs, zValues);
    bool const hasAssets = hasMeta && hasCurve;

    TestResult const assetsPresent{.name = "Validation assets present",
                                   .expected = 1.0,
                                   .actual = hasAssets ? 1.0 : 0.0,
                                   .passed = hasAssets};
    printResult(assetsPresent);
    assetsPresent.passed ? ++passed : ++failed;

    if (hasAssets) {
      const double mass = massSolar * physics::M_SUN;
      const double expectedRs = physics::schwarzschildRadius(mass);
      const double rG = physics::G * mass / physics::C2;
      const double a = spin * rG;
      const bool prograde = spin >= 0.0;
      const double expectedIsco = physics::kerrIscoRadius(mass, a, prograde);
      const double expectedPh = prograde ? physics::kerrPhotonOrbitPrograde(mass, a)
                                         : physics::kerrPhotonOrbitRetrograde(mass, a);

      TestResult const rsResult{.name = "Validation r_s",
                                .expected = expectedRs,
                                .actual = rS,
                                .passed = approxEqual(rS, expectedRs, 1e-6)};
      printResult(rsResult);
      rsResult.passed ? ++passed : ++failed;

      TestResult const iscoResult{.name = "Validation r_isco",
                                  .expected = expectedIsco,
                                  .actual = rIco,
                                  .passed = approxEqual(rIco, expectedIsco, 1e-6)};
      printResult(iscoResult);
      iscoResult.passed ? ++passed : ++failed;

      TestResult const phResult{.name = "Validation r_ph",
                                .expected = expectedPh,
                                .actual = rPh,
                                .passed = approxEqual(rPh, expectedPh, 1e-6)};
      printResult(phResult);
      phResult.passed ? ++passed : ++failed;

      double maxRedshiftDiff = 0.0;
      for (std::size_t i = 0; i < rOverRs.size(); ++i) {
        double const r = rOverRs.at(i) * expectedRs;
        double expectedZ = physics::kerrRedshift(r, 0.5 * physics::PI, mass, a);
        if (!std::isfinite(expectedZ) || expectedZ < 0.0) {
          expectedZ = 0.0;
        }
        maxRedshiftDiff = std::max(maxRedshiftDiff, std::abs(expectedZ - zValues.at(i)));
      }

      TestResult const curveResult{.name = "Validation redshift curve max abs diff",
                                   .expected = 0.0,
                                   .actual = maxRedshiftDiff,
                                   .passed = maxRedshiftDiff <= 1e-6};
      printResult(curveResult);
      curveResult.passed ? ++passed : ++failed;
    }
  }

  // Test 18: Spin radii curve assets (r_isco/r_ph vs spin)
  {
    std::vector<double> spins;
    std::vector<double> iscoOverRs;
    std::vector<double> phOverRs;
    bool const hasCurve =
        loadSpinCurveCsv("assets/validation/spin_radii_curve.csv", spins, iscoOverRs, phOverRs);

    TestResult const assetsPresent{.name = "Spin curve assets present",
                                   .expected = 1.0,
                                   .actual = hasCurve ? 1.0 : 0.0,
                                   .passed = hasCurve};
    printResult(assetsPresent);
    assetsPresent.passed ? ++passed : ++failed;

    if (hasCurve) {
      const double mass = physics::M_SUN;
      const double rS = physics::schwarzschildRadius(mass);
      const double rG = physics::G * mass / physics::C2;

      double maxIscoDiff = 0.0;
      double maxPhDiff = 0.0;
      for (std::size_t i = 0; i < spins.size(); ++i) {
        double const spin = spins.at(i);
        double const a = spin * rG;
        bool const prograde = spin >= 0.0;
        double const expectedIsco = physics::kerrIscoRadius(mass, a, prograde) / rS;
        double const expectedPh = prograde ? physics::kerrPhotonOrbitPrograde(mass, a) / rS
                                           : physics::kerrPhotonOrbitRetrograde(mass, a) / rS;
        maxIscoDiff = std::max(maxIscoDiff, std::abs(expectedIsco - iscoOverRs.at(i)));
        maxPhDiff = std::max(maxPhDiff, std::abs(expectedPh - phOverRs.at(i)));
      }

      TestResult const iscoCurve{.name = "Spin curve r_isco max abs diff",
                                 .expected = 0.0,
                                 .actual = maxIscoDiff,
                                 .passed = maxIscoDiff <= 1e-6};
      printResult(iscoCurve);
      iscoCurve.passed ? ++passed : ++failed;

      TestResult const phCurve{.name = "Spin curve r_ph max abs diff",
                               .expected = 0.0,
                               .actual = maxPhDiff,
                               .passed = maxPhDiff <= 1e-6};
      printResult(phCurve);
      phCurve.passed ? ++passed : ++failed;
    }
  }

  // Summary
  std::cout << "=== Summary ===\n";
  std::cout << "Passed: " << passed << "/" << (passed + failed) << "\n";
  std::cout << "Failed: " << failed << "/" << (passed + failed) << "\n";

  return failed;
}

} // namespace

int main() {
  return runTests();
}
