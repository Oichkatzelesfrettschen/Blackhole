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

#include "constants.h"
#include "cosmology.h"
#include "geodesics.h"
#include "kerr.h"
#include "lut.h"
#include "raytracer.h"
#include "schwarzschild.h"
#include "thin_disk.h"

#include <cmath>
#include <cstdlib>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

namespace {

constexpr double TOLERANCE = 1e-10;

bool approx_equal(double a, double b, double tol = TOLERANCE) {
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

void print_result(const TestResult &r) {
  std::cout << (r.passed ? "[PASS]" : "[FAIL]") << " " << r.name << "\n"
            << "  Expected: " << std::scientific << std::setprecision(10)
            << r.expected << "\n"
            << "  Actual:   " << r.actual << "\n";
  if (!r.passed) {
    double rel_err = std::abs(r.actual - r.expected) / std::abs(r.expected);
    std::cout << "  Rel.Err:  " << rel_err << "\n";
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
  std::string needle = "\"" + key + "\"";
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
  std::string needle = "\"" + key + "\"";
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
  std::size_t end = text.find('"', pos + 1);
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
    std::size_t comma = line.find(',');
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
    std::size_t comma = line.find(',');
    if (comma == std::string::npos) {
      continue;
    }
    const char *rStart = line.c_str();
    char *rEnd = nullptr;
    double rVal = std::strtod(rStart, &rEnd);
    if (rEnd == rStart) {
      continue;
    }
    const char *vStart = line.c_str() + comma + 1;
    char *vEnd = nullptr;
    double vVal = std::strtod(vStart, &vEnd);
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
    std::size_t comma1 = line.find(',');
    if (comma1 == std::string::npos) {
      continue;
    }
    std::size_t comma2 = line.find(',', comma1 + 1);
    if (comma2 == std::string::npos) {
      continue;
    }
    const char *sStart = line.c_str();
    char *sEnd = nullptr;
    double spinVal = std::strtod(sStart, &sEnd);
    if (sEnd == sStart) {
      continue;
    }
    const char *iscoStart = line.c_str() + comma1 + 1;
    char *iscoEnd = nullptr;
    double iscoVal = std::strtod(iscoStart, &iscoEnd);
    if (iscoEnd == iscoStart) {
      continue;
    }
    const char *phStart = line.c_str() + comma2 + 1;
    char *phEnd = nullptr;
    double phVal = std::strtod(phStart, &phEnd);
    if (phEnd == phStart) {
      continue;
    }
    spins.push_back(spinVal);
    iscoOverRs.push_back(iscoVal);
    phOverRs.push_back(phVal);
  }
  return !spins.empty() && spins.size() == iscoOverRs.size() && spins.size() == phOverRs.size();
}

int run_tests() {
  int passed = 0;
  int failed = 0;

  std::cout << "=== Physics Library Validation Tests ===\n\n";

  // Test 1: Schwarzschild radius for 1 solar mass
  // r_s = 2GM/c^2 = 2 * 6.67430e-8 * 1.98841e33 / (2.99792458e10)^2
  // r_s = 2.95325e5 cm = 2.95325 km
  {
    double mass = physics::M_SUN; // 1 solar mass in grams
    double r_s = physics::schwarzschild_radius(mass);
    double expected = 2.9532500765e5; // cm (verified value)

    TestResult r{"Schwarzschild radius (1 M_sun)", expected, r_s,
                 approx_equal(r_s, expected, 1e-6)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 2: Schwarzschild radius for 4 million solar masses (Sgr A*)
  // This is the supermassive black hole at the center of our galaxy
  {
    double mass = 4.0e6 * physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double expected = 1.1813e12; // cm (~0.08 AU)

    TestResult r{"Schwarzschild radius (4e6 M_sun, Sgr A*)", expected, r_s,
                 approx_equal(r_s, expected, 1e-4)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 3: Photon sphere radius = 1.5 * r_s
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r_ph = physics::photon_sphere_radius(mass);
    double expected = 1.5 * r_s;

    TestResult r{"Photon sphere radius = 1.5 r_s", expected, r_ph,
                 approx_equal(r_ph, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 4: ISCO radius = 3 * r_s (for Schwarzschild)
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r_isco = physics::isco_radius(mass);
    double expected = 3.0 * r_s;

    TestResult r{"ISCO radius = 3 r_s", expected, r_isco,
                 approx_equal(r_isco, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 5: Gravitational redshift at r = 2 r_s (just above horizon)
  // z = 1/sqrt(1 - r_s/r) - 1 = 1/sqrt(1/2) - 1 = sqrt(2) - 1 ~ 0.414
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r = 2.0 * r_s;
    double z = physics::gravitational_redshift(r, mass);
    double expected = std::sqrt(2.0) - 1.0;

    TestResult r_test{"Gravitational redshift at r=2r_s", expected, z,
                      approx_equal(z, expected)};
    print_result(r_test);
    r_test.passed ? ++passed : ++failed;
  }

  // Test 6: Gravitational redshift at r = 10 r_s
  // z = 1/sqrt(1 - 0.1) - 1 = 1/sqrt(0.9) - 1 ~ 0.0541
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r = 10.0 * r_s;
    double z = physics::gravitational_redshift(r, mass);
    double expected = 1.0 / std::sqrt(0.9) - 1.0;

    TestResult r_test{"Gravitational redshift at r=10r_s", expected, z,
                      approx_equal(z, expected)};
    print_result(r_test);
    r_test.passed ? ++passed : ++failed;
  }

  // Test 7: Critical impact parameter for photon capture
  // b_crit = sqrt(27) * r_s / 2 ~ 2.598 * r_s
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double b_crit = physics::critical_impact_parameter(mass);
    double expected = std::sqrt(27.0) * r_s / 2.0;

    TestResult r{"Critical impact parameter", expected, b_crit,
                 approx_equal(b_crit, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 8: Escape velocity at r = 2 r_s
  // v_esc = c * sqrt(r_s/r) = c * sqrt(1/2) ~ 0.707 c
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double r = 2.0 * r_s;
    double v_esc = physics::escape_velocity(r, mass);
    double expected = physics::C * std::sqrt(0.5);

    TestResult r_test{"Escape velocity at r=2r_s", expected, v_esc,
                      approx_equal(v_esc, expected)};
    print_result(r_test);
    r_test.passed ? ++passed : ++failed;
  }

  // Test 9: Light deflection angle for large impact parameter
  // delta_phi ~ 4GM/(b*c^2) for b >> r_s
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double b = 1000.0 * r_s; // Far from black hole
    double delta_phi = physics::gravitational_deflection(b, mass);
    double expected = 2.0 * r_s / b; // First-order approximation

    TestResult r{"Light deflection (weak field)", expected, delta_phi,
                 approx_equal(delta_phi, expected, 1e-3)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 10: Hubble parameter E(z=0) should equal 1
  {
    double E = physics::hubble_E(0.0);
    double expected = 1.0;

    TestResult r{"Hubble E(z=0) = 1", expected, E, approx_equal(E, expected)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 11: Kerr ISCO reduces to Schwarzschild when a=0
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double a = 0.0;
    double r_isco = physics::kerr_isco_radius(mass, a, true);
    double expected = 3.0 * r_s;

    TestResult r{"Kerr ISCO (a=0) == 3 r_s", expected, r_isco,
                 approx_equal(r_isco, expected, 1e-6)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 12: Kerr photon orbit reduces to Schwarzschild when a=0
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double a = 0.0;
    double r_ph = physics::kerr_photon_orbit_prograde(mass, a);
    double expected = 1.5 * r_s;

    TestResult r{"Kerr photon orbit (a=0) == 1.5 r_s", expected, r_ph,
                 approx_equal(r_ph, expected, 1e-6)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 13: Extreme Kerr prograde ISCO at a*=1 -> r_ISCO = M (0.5 r_s)
  {
    double mass = physics::M_SUN;
    double M_geom = physics::G * mass / physics::C2;
    double a = M_geom;
    double r_s = physics::schwarzschild_radius(mass);
    double expected = 0.5 * r_s;
    double r_isco = physics::kerr_isco_radius(mass, a, true);

    TestResult r{"Kerr ISCO prograde (a*=1)", expected, r_isco,
                 approx_equal(r_isco, expected, 1e-4)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 14: Extreme Kerr retrograde ISCO at a*=1 -> r_ISCO = 9M (4.5 r_s)
  {
    double mass = physics::M_SUN;
    double M_geom = physics::G * mass / physics::C2;
    double a = M_geom;
    double r_s = physics::schwarzschild_radius(mass);
    double expected = 4.5 * r_s;
    double r_isco = physics::kerr_isco_radius(mass, a, false);

    TestResult r{"Kerr ISCO retrograde (a*=1)", expected, r_isco,
                 approx_equal(r_isco, expected, 1e-4)};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 15: Kerr horizons reduce to Schwarzschild when a=0
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    auto horizons = physics::kerr_horizons(mass, 0.0);
    bool ok = approx_equal(horizons.first, r_s, 1e-8) && approx_equal(horizons.second, 0.0, 1e-8);

    TestResult r{"Kerr horizons (a=0)", 1.0, ok ? 1.0 : 0.0, ok};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 16: Invalid spin returns NaN
  {
    double mass = physics::M_SUN;
    double M_geom = physics::G * mass / physics::C2;
    double a = 1.2 * M_geom;
    double r_isco = physics::kerr_isco_radius(mass, a, true);
    double r_ph = physics::kerr_photon_orbit_prograde(mass, a);
    bool ok = std::isnan(r_isco) && std::isnan(r_ph);

    TestResult r{"Kerr invalid spin -> NaN", 1.0, ok ? 1.0 : 0.0, ok};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 17: Kerr redshift at a=0 matches Schwarzschild in equatorial plane
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double radius = 10.0 * r_s;
    double z_schw = physics::gravitational_redshift(radius, mass);
    double z_kerr = physics::kerr_redshift(radius, 0.5 * physics::PI, mass, 0.0);

    TestResult result{"Kerr redshift (a=0) == Schwarzschild", z_schw, z_kerr,
                      approx_equal(z_kerr, z_schw, 1e-6)};
    print_result(result);
    result.passed ? ++passed : ++failed;
  }

  // Test 18: Kerr photon orbit potentials vanish at a=0 photon sphere
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double M_geom = physics::G * mass / physics::C2;
    double r = 1.5 * r_s; // 3M
    double a = 0.0;

    physics::KerrGeodesicConsts c{};
    c.E = 1.0;
    c.Lz = 3.0 * std::sqrt(3.0) * M_geom;
    c.Q = 0.0;

    physics::KerrPotentials pot =
        physics::kerr_potentials(r, 0.5 * physics::PI, mass, a, c);

    double scaleR = M_geom * M_geom * M_geom * M_geom;
    double scaleD = M_geom * M_geom * M_geom;
    bool r_ok = std::abs(pot.R) / scaleR < 1e-6;
    bool d_ok = std::abs(pot.dRdr) / scaleD < 1e-6;

    TestResult rPot{"Kerr R potential at photon orbit", 0.0, pot.R, r_ok};
    TestResult dPot{"Kerr dR/dr at photon orbit", 0.0, pot.dRdr, d_ok};
    print_result(rPot);
    print_result(dPot);
    rPot.passed ? ++passed : ++failed;
    dPot.passed ? ++passed : ++failed;
  }

  // Test 19: Kerr turning point potential vanishes (a=0, equatorial)
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double M_geom = physics::G * mass / physics::C2;
    double r = 4.0 * r_s; // turning point radius
    double a = 0.0;

    physics::KerrGeodesicConsts c{};
    c.E = 1.0;
    c.Lz = std::sqrt((r * r * r) / (r - r_s)); // Lz^2 = r^3 / (r - r_s)
    c.Q = 0.0;

    physics::KerrPotentials pot =
        physics::kerr_potentials(r, 0.5 * physics::PI, mass, a, c);

    double scaleR = M_geom * M_geom * M_geom * M_geom;
    bool ok = std::abs(pot.R) / scaleR < 1e-6;

    TestResult rPot{"Kerr turning point R=0", 0.0, pot.R, ok};
    print_result(rPot);
    rPot.passed ? ++passed : ++failed;
  }

  // Test 20: Kerr raytracer produces finite output (a=0)
  {
    double mass = physics::M_SUN;
    double r_s = physics::schwarzschild_radius(mass);
    double M_geom = physics::G * mass / physics::C2;
    double a = 0.0;

    physics::KerrRaytracer tracer(mass, a);
    double impact = 3.0 * std::sqrt(3.0) * M_geom;
    physics::KerrGeodesicConsts c = physics::kerr_equatorial_consts(impact, 1.0);
    physics::KerrGeodesicState state = physics::kerr_equatorial_state(10.0 * r_s, 0.0, -1.0);

    auto result = tracer.trace(state, c);
    bool finite =
        std::isfinite(result.final_position[0]) &&
        std::isfinite(result.final_position[1]) &&
        std::isfinite(result.final_position[2]);

    TestResult r{"Kerr raytracer finite output", 1.0, finite ? 1.0 : 0.0, finite};
    print_result(r);
    r.passed ? ++passed : ++failed;
  }

  // Test 21: Spin radii LUT matches Schwarzschild for spin=0
  {
    auto lut = physics::generate_spin_radii_lut(4, 1.0, 0.0, 0.0);
    bool ok = !lut.spins.empty() &&
              std::abs(lut.r_isco_over_rs.front() - 3.0f) < 1e-4f &&
              std::abs(lut.r_ph_over_rs.front() - 1.5f) < 1e-4f;

    TestResult r{"Spin radii LUT (a=0)", 1.0, ok ? 1.0 : 0.0, ok};
    print_result(r);
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

    bool hasCsv =
        loadLutCsv("assets/luts/emissivity_lut.csv", emissivity) &&
        loadLutCsv("assets/luts/redshift_lut.csv", redshift);
    bool hasMeta = loadLutMeta(massSolar, spin, mdot, rInOverRs, rOutOverRs);
    bool hasAssets = hasCsv && hasMeta && emissivity.size() == redshift.size();

    TestResult assetsPresent{"LUT assets present", 1.0, hasAssets ? 1.0 : 0.0, hasAssets};
    print_result(assetsPresent);
    assetsPresent.passed ? ++passed : ++failed;

    if (hasAssets) {
      const std::size_t count = emissivity.size();
      const double mass = massSolar * physics::M_SUN;
      const double r_s = physics::schwarzschild_radius(mass);
      const double r_g = physics::G * mass / physics::C2;
      const double a = spin * r_g;
      const double r_in = rInOverRs * r_s;
      const double r_out = rOutOverRs * r_s;

      double L_edd = 1.26e38 * massSolar;
      double mdotEdd = L_edd / (0.1 * physics::C2);
      double mdotCgs = mdot * mdotEdd;
      auto emissivityModel = [&](double r) {
        if (r < r_in) {
          return 0.0;
        }
        double prefactor = 3.0 * physics::G * mass * mdotCgs /
                           (8.0 * M_PI * r * r * r);
        double basic = 1.0 - std::sqrt(r_in / r);
        double spinFactor = 1.0 + 0.5 * spin * std::sqrt(r_g / r);
        return prefactor * basic * spinFactor;
      };

      double maxFlux = 0.0;
      std::vector<double> fluxes(count, 0.0);
      for (std::size_t i = 0; i < count; ++i) {
        double u = static_cast<double>(i) / static_cast<double>(count - 1);
        double r = r_in + u * (r_out - r_in);
        double flux = emissivityModel(r);
        if (!std::isfinite(flux) || flux < 0.0) {
          flux = 0.0;
        }
        fluxes[i] = flux;
        maxFlux = std::max(maxFlux, flux);
      }

      double maxEmissDiff = 0.0;
      double maxRedshiftDiff = 0.0;
      for (std::size_t i = 0; i < count; ++i) {
        double expectedEmiss = (maxFlux > 0.0) ? fluxes[i] / maxFlux : 0.0;
        double actualEmiss = emissivity[i];
        maxEmissDiff = std::max(maxEmissDiff, std::abs(expectedEmiss - actualEmiss));

        double u = static_cast<double>(i) / static_cast<double>(count - 1);
        double r = r_in + u * (r_out - r_in);
        double expectedRedshift = physics::kerr_redshift(r, 0.5 * physics::PI, mass, a);
        if (!std::isfinite(expectedRedshift) || expectedRedshift < 0.0) {
          expectedRedshift = 0.0;
        }
        expectedRedshift = std::min(expectedRedshift, 10.0);
        double actualRedshift = redshift[i];
        maxRedshiftDiff = std::max(maxRedshiftDiff, std::abs(expectedRedshift - actualRedshift));
      }

      TestResult emissivityResult{"LUT emissivity max abs diff", 0.0, maxEmissDiff,
                                  maxEmissDiff <= 2e-3};
      print_result(emissivityResult);
      emissivityResult.passed ? ++passed : ++failed;

      TestResult redshiftResult{"LUT redshift max abs diff", 0.0, maxRedshiftDiff,
                                maxRedshiftDiff <= 2e-3};
      print_result(redshiftResult);
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

    bool hasMeta =
        loadValidationMeta(massSolar, spin, rS, rIco, rPh, rMinOverRs, rMaxOverRs, source);
    bool hasCurve = loadCurveCsv("assets/validation/redshift_curve.csv", rOverRs, zValues);
    bool hasAssets = hasMeta && hasCurve;

    TestResult assetsPresent{"Validation assets present", 1.0, hasAssets ? 1.0 : 0.0,
                             hasAssets};
    print_result(assetsPresent);
    assetsPresent.passed ? ++passed : ++failed;

    if (hasAssets) {
      const double mass = massSolar * physics::M_SUN;
      const double expectedRs = physics::schwarzschild_radius(mass);
      const double r_g = physics::G * mass / physics::C2;
      const double a = spin * r_g;
      const bool prograde = spin >= 0.0;
      const double expectedIsco = physics::kerr_isco_radius(mass, a, prograde);
      const double expectedPh = prograde ? physics::kerr_photon_orbit_prograde(mass, a)
                                         : physics::kerr_photon_orbit_retrograde(mass, a);

      TestResult rsResult{"Validation r_s", expectedRs, rS,
                          approx_equal(rS, expectedRs, 1e-6)};
      print_result(rsResult);
      rsResult.passed ? ++passed : ++failed;

      TestResult iscoResult{"Validation r_isco", expectedIsco, rIco,
                            approx_equal(rIco, expectedIsco, 1e-6)};
      print_result(iscoResult);
      iscoResult.passed ? ++passed : ++failed;

      TestResult phResult{"Validation r_ph", expectedPh, rPh,
                          approx_equal(rPh, expectedPh, 1e-6)};
      print_result(phResult);
      phResult.passed ? ++passed : ++failed;

      double maxRedshiftDiff = 0.0;
      for (std::size_t i = 0; i < rOverRs.size(); ++i) {
        double r = rOverRs[i] * expectedRs;
        double expectedZ = physics::kerr_redshift(r, 0.5 * physics::PI, mass, a);
        if (!std::isfinite(expectedZ) || expectedZ < 0.0) {
          expectedZ = 0.0;
        }
        maxRedshiftDiff = std::max(maxRedshiftDiff, std::abs(expectedZ - zValues[i]));
      }

      TestResult curveResult{"Validation redshift curve max abs diff", 0.0, maxRedshiftDiff,
                             maxRedshiftDiff <= 1e-6};
      print_result(curveResult);
      curveResult.passed ? ++passed : ++failed;
    }
  }

  // Test 18: Spin radii curve assets (r_isco/r_ph vs spin)
  {
    std::vector<double> spins;
    std::vector<double> iscoOverRs;
    std::vector<double> phOverRs;
    bool hasCurve =
        loadSpinCurveCsv("assets/validation/spin_radii_curve.csv", spins, iscoOverRs, phOverRs);

    TestResult assetsPresent{"Spin curve assets present", 1.0, hasCurve ? 1.0 : 0.0, hasCurve};
    print_result(assetsPresent);
    assetsPresent.passed ? ++passed : ++failed;

    if (hasCurve) {
      const double mass = physics::M_SUN;
      const double r_s = physics::schwarzschild_radius(mass);
      const double r_g = physics::G * mass / physics::C2;

      double maxIscoDiff = 0.0;
      double maxPhDiff = 0.0;
      for (std::size_t i = 0; i < spins.size(); ++i) {
        double spin = spins[i];
        double a = spin * r_g;
        bool prograde = spin >= 0.0;
        double expectedIsco = physics::kerr_isco_radius(mass, a, prograde) / r_s;
        double expectedPh = prograde ? physics::kerr_photon_orbit_prograde(mass, a) / r_s
                                     : physics::kerr_photon_orbit_retrograde(mass, a) / r_s;
        maxIscoDiff = std::max(maxIscoDiff, std::abs(expectedIsco - iscoOverRs[i]));
        maxPhDiff = std::max(maxPhDiff, std::abs(expectedPh - phOverRs[i]));
      }

      TestResult iscoCurve{"Spin curve r_isco max abs diff", 0.0, maxIscoDiff,
                           maxIscoDiff <= 1e-6};
      print_result(iscoCurve);
      iscoCurve.passed ? ++passed : ++failed;

      TestResult phCurve{"Spin curve r_ph max abs diff", 0.0, maxPhDiff,
                         maxPhDiff <= 1e-6};
      print_result(phCurve);
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

int main() { return run_tests(); }
