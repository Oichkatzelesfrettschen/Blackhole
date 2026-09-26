/**
 * @file tests/analytic_geodesic_reproducibility_test.cpp
 * @brief Validation tests for analytic_kerr_geodesic.h and reproducibility.h.
 *
 * Photon-sphere identities and manifest round trips guard numerical and metadata contracts.
 *   analytic_kerr_geodesic.h provides O(1) Kerr null-geodesic evaluation via
 *   Jacobi elliptic functions (vs. O(N) numerical RK4). Its photon-sphere
 *   limits are analytic and exact.
 *   reproducibility.h records build and physics metadata for scientific outputs.
 *
 * Tests (15):
 *   Photon sphere (radialPotential + criticalImpactParams) (1-4):
 *   1.  radialPotential(r=3, a=0, xi=0, eta=27) == 0  (Schwarzschild photon sphere)
 *   2.  criticalImpactParams(r=3, a=0) == {xi=0, eta=27}
 *   3.  R(r_ph, a, xi_c, eta_c) == 0 for a=0.5 (Kerr self-consistency)
 *   4.  radialPotential positive away from photon sphere (xi=0, eta=27, r != 3)
 *   Photon orbit radii (5-9):
 *   5.  progradePhotonOrbit(0.0) == 3.0  (Schwarzschild)
 *   6.  retrogradePhotonOrbit(0.0) == 3.0  (Schwarzschild)
 *   7.  progradePhotonOrbit(1.0) == 1.0  (extremal Kerr prograde)
 *   8.  retrogradePhotonOrbit(1.0) == 4.0  (extremal Kerr retrograde)
 *   9.  progradePhotonOrbit monotonically decreasing, retrograde increasing
 *   Reproducibility manifest (10-15):
 *  10.  buildManifest() returns non-empty manifest
 *  11.  get("code") == "Blackhole"
 *  12.  get("build_type") is "Release" or "Debug"  (non-empty, valid)
 *  13.  add(key, double) / get() round-trip with setprecision(15)
 *  14.  add(key, int) / get() round-trip
 *  15.  addPhysicsParams() populates mass and spin via get()
 *   Boost double-precision policy (16-17), against values computed under
 *   Boost's default long-double promotion:
 *  16.  radialHalfPeriod within 2e-15 relative, scaled by the condition number
 *       of K(k) in k (up to 7e3 at m = 0.99998)
 *  17.  rAnalytic within 2e-15 of max(|r|, |dr/dsn|): a 2e-15 error in sn
 *       propagated through r(sn^2)
 */

#include <algorithm>
#include <array>
#include <cmath>
#include <cstddef>
#include <cstdio>
#include <exception>
#include <format>
#include <iostream>
#include <numbers>
#include <string>
#include <string_view>

#include <boost/math/special_functions/ellint_1.hpp>
#include <boost/math/special_functions/ellint_2.hpp>

#include "../src/physics/analytic_kerr_geodesic.h"
#include "../src/physics/reproducibility.h"

static_assert(PHYSICS_HAS_BOOST_JACOBI == 1, "Validation requires the Boost numerical path");

using namespace physics;

namespace {

bool gAllPass = true;

void check(bool cond, const char *label, std::string_view detail = {}) {
  if (cond) {
    std::cout << "  [PASS] " << label << "\n";
  } else {
    std::cout << "  [FAIL] " << label;
    if (!detail.empty()) {
      std::cout << "  -- " << detail;
    }
    std::cout << "\n";
    gAllPass = false;
  }
}

// ============================================================================
// Tests 1-4: Radial potential at the photon sphere
// ============================================================================

void testRadialPotentialSchwarzschildPhotonSphere() {
  std::cout << "Test 1: radialPotential(r=3, a=0, xi=0, eta=27) == 0  (photon sphere)\n";

  // For Schwarzschild (a=0, M=1), the photon sphere at r=3 satisfies R(3) = 0.
  // Convention: xi=L/E=0 (equatorial, azimuthal symmetry broken) + eta=b^2=27
  // => R(3) = (9)^2 - (9-6)*(27) = 81 - 81 = 0.
  const double rVal = radialPotential(3.0, 0.0, 0.0, 27.0);
  const std::string detailBuffer = std::format("R(3, 0, 0, 27) = {:.6e} (expected 0)", rVal);
  check(std::abs(rVal) < 1.0e-10, "R(r_ph, a=0, xi=0, eta=27) = 0", detailBuffer);
}

void testCriticalImpactParamsSchwarzschild() {
  std::cout << "Test 2: criticalImpactParams(r=3, a=0) == {xi=0, eta=27}\n";

  const ImpactParams ip = criticalImpactParams(3.0, 0.0);
  const std::string detailBuffer =
      std::format("xi={:.4f}, eta={:.4f}  (expected xi=0, eta=27)", ip.xi, ip.eta);
  check(std::abs(ip.xi) < 1.0e-12 && std::abs(ip.eta - 27.0) < 1.0e-10,
        "criticalImpactParams(r=3, a=0) = {0, 27}", detailBuffer);
}

void testCriticalImpactParamsKerrSelfConsistency() {
  std::cout << "Test 3: R(r_ph, a, xi_c, eta_c) == 0 for a=0.5  (self-consistency)\n";

  // Get prograde photon orbit radius for a=0.5, then verify R=0 there.
  const double a = 0.5;
  const double rPh = progradePhotonOrbit(a);
  const ImpactParams ip = criticalImpactParams(rPh, a);
  const double rVal = radialPotential(rPh, a, ip.xi, ip.eta);

  const std::string detailBuffer = std::format("r_ph={:.6f}, R(r_ph)={:.4e}", rPh, rVal);
  check(std::abs(rVal) < 1.0e-8, "R(r_ph, a=0.5, xi_c, eta_c) = 0  (self-consistency)",
        detailBuffer);
}

void testRadialPotentialPositiveOffPhotonSphere() {
  std::cout << "Test 4: radialPotential(r != 3, a=0, xi=0, eta=27) > 0  (no turning pt)\n";

  // For Schwarzschild, R(r) = r(r-3)^2(r+6) >= 0 for r>0.  Check r=2 and r=5.
  const double rIn = radialPotential(2.0, 0.0, 0.0, 27.0);
  const double rOut = radialPotential(5.0, 0.0, 0.0, 27.0);
  const std::string detailBuffer =
      std::format("R(2)={:.4f}, R(5)={:.4f}  (both expected > 0)", rIn, rOut);
  check(rIn > 0.0 && rOut > 0.0, "R(2) > 0 and R(5) > 0 for Schwarzschild critical orbit",
        detailBuffer);
}

// ============================================================================
// Tests 5-9: Photon orbit radii
// ============================================================================

void testProgradePhotonOrbitSchwarzschild() {
  std::cout << "Test 5: progradePhotonOrbit(0.0) == 3.0  (Schwarzschild limit)\n";

  const double r = progradePhotonOrbit(0.0);
  const std::string detailBuffer = std::format("r_ph(a=0) = {:.12f}  (expected 3.0)", r);
  check(std::abs(r - 3.0) < 1.0e-12, "progradePhotonOrbit(0) = 3", detailBuffer);
}

void testRetrogradePhotonOrbitSchwarzschild() {
  std::cout << "Test 6: retrogradePhotonOrbit(0.0) == 3.0  (Schwarzschild limit)\n";

  const double r = retrogradePhotonOrbit(0.0);
  const std::string detailBuffer = std::format("r_ph_retro(a=0) = {:.12f}  (expected 3.0)", r);
  check(std::abs(r - 3.0) < 1.0e-12, "retrogradePhotonOrbit(0) = 3", detailBuffer);
}

void testProgradePhotonOrbitExtremal() {
  std::cout << "Test 7: progradePhotonOrbit(1.0) == 1.0  (extremal Kerr)\n";

  // r_ph = 2*(1 + cos(2/3*acos(-1))) = 2*(1 + cos(2pi/3)) = 2*(1 - 1/2) = 1
  const double r = progradePhotonOrbit(1.0);
  const std::string detailBuffer = std::format("r_ph(a=1) = {:.12f}  (expected 1.0)", r);
  check(std::abs(r - 1.0) < 1.0e-12, "progradePhotonOrbit(1) = 1", detailBuffer);
}

void testRetrogradePhotonOrbitExtremal() {
  std::cout << "Test 8: retrogradePhotonOrbit(1.0) == 4.0  (extremal Kerr)\n";

  // r_ph = 2*(1 + cos(2/3*acos(1))) = 2*(1 + cos(0)) = 2*(1 + 1) = 4
  const double r = retrogradePhotonOrbit(1.0);
  const std::string detailBuffer = std::format("r_ph_retro(a=1) = {:.12f}  (expected 4.0)", r);
  check(std::abs(r - 4.0) < 1.0e-12, "retrogradePhotonOrbit(1) = 4", detailBuffer);
}

void testPhotonOrbitMonotonicity() {
  std::cout << "Test 9: progradePhotonOrbit decreasing, retrograde increasing with spin\n";

  // Prograde: 3 > r_ph(0.5) > 1  (orbit tightens with prograde spin)
  // Retrograde: 3 < r_ph_retro(0.5) < 4  (orbit widens with retrograde spin)
  const double rPro0 = progradePhotonOrbit(0.0);
  const double rPro5 = progradePhotonOrbit(0.5);
  const double rPro1 = progradePhotonOrbit(1.0);
  const double rRet0 = retrogradePhotonOrbit(0.0);
  const double rRet5 = retrogradePhotonOrbit(0.5);
  const double rRet1 = retrogradePhotonOrbit(1.0);
  const bool proDecr = (rPro0 > rPro5) && (rPro5 > rPro1);
  const bool retIncr = (rRet0 < rRet5) && (rRet5 < rRet1);
  const std::string detailBuffer =
      std::format("pro: {:.3f}>{:.3f}>{:.3f}  retro: {:.3f}<{:.3f}<{:.3f}", rPro0, rPro5, rPro1,
                  rRet0, rRet5, rRet1);
  check(proDecr && retIncr, "prograde decreasing, retrograde increasing with spin", detailBuffer);
}

// ============================================================================
// Tests 10-15: Reproducibility manifest
// ============================================================================

void testManifestNonEmpty() {
  std::cout << "Test 10: buildManifest() returns non-empty manifest\n";

  const ReproducibilityManifest m = buildManifest();
  check(!m.entries.empty(), "buildManifest().entries is non-empty");
}

void testManifestCodeKey() {
  std::cout << "Test 11: get(\"code\") == \"Blackhole\"\n";

  const ReproducibilityManifest m = buildManifest();
  const std::string code = m.get("code");
  const std::string detailBuffer = std::format(R"(code="{}" (expected "Blackhole"))", code);
  check(code == "Blackhole", R"(get("code") = "Blackhole")", detailBuffer);
}

void testManifestBuildType() {
  std::cout << "Test 12: get(\"build_type\") is \"Release\" or \"Debug\"\n";

  const ReproducibilityManifest m = buildManifest();
  const std::string bt = m.get("build_type");
  const bool valid = (bt == "Release") || (bt == "Debug");
  const std::string detailBuffer = std::format("build_type=\"{}\"", bt);
  check(valid, "build_type is Release or Debug", detailBuffer);
}

void testManifestAddDoubleRoundTrip() {
  std::cout << "Test 13: add(key, double) / get() round-trip (setprecision(15))\n";

  ReproducibilityManifest m;
  const double val = std::numbers::pi;
  m.add("pi_test", val);
  const std::string stored = m.get("pi_test");
  // setprecision(15) gives ~15 significant digits; reconstruct and compare.
  const double recovered = std::stod(stored);
  const std::string detailBuffer =
      std::format("stored=\"{}\", recovered={:.15f}", stored, recovered);
  check(std::abs(recovered - val) / val < 1.0e-14, "add/get double round-trip to within 1e-14",
        detailBuffer);
}

void testManifestAddIntRoundTrip() {
  std::cout << "Test 14: add(key, int) / get() round-trip\n";

  ReproducibilityManifest m;
  m.add("nx_test", 1920);
  const std::string stored = m.get("nx_test");
  const int recovered = std::stoi(stored);
  const std::string detailBuffer = std::format("stored=\"{}\" -> {:d}", stored, recovered);
  check(recovered == 1920, "add/get int round-trip for 1920", detailBuffer);
}

void testManifestAddPhysicsParams() {
  std::cout << "Test 15: addPhysicsParams() populates bh_mass_msun and bh_spin\n";

  ReproducibilityManifest m;
  addPhysicsParams(m, 6.5e9, 0.9375, 17.0, 230.0e9, 1024, 1024, 160.0);
  const double mass = std::stod(m.get("bh_mass_msun"));
  const double spin = std::stod(m.get("bh_spin"));
  const std::string detailBuffer = std::format("mass={:.4e}, spin={:.4f}", mass, spin);
  check(std::abs(mass - 6.5e9) / 6.5e9 < 1.0e-12 && std::abs(spin - 0.9375) < 1.0e-12,
        "addPhysicsParams: mass=6.5e9 Msun, spin=0.9375 recovered", detailBuffer);
}

} // namespace

// ============================================================================
// Tests 16-17: Boost double-precision policy against the promoted baseline
// ============================================================================

namespace {

struct PromotedBaseline {
  std::array<double, 4> roots{};
  double halfPeriod = 0.0;
  std::array<double, 6> radius{};
};

constexpr std::array<double, 6> BASELINE_LAMBDAS = {0.05, 0.3, 0.77, 1.4, 2.9, 5.5};

// radialHalfPeriod and rAnalytic at BASELINE_LAMBDAS under Boost's default
// policy (double promoted to x87 long double), Boost 1.90, identical from GCC 14
// and clang 22 at SSE2; FMA contraction under -march=native moves the rational
// r(sn^2) by a few ulp, inside the conditioning-scaled gate.
constexpr std::array<PromotedBaseline, 5> PROMOTED_BASELINE = {{
    {{6.0, 4.0, 1.5, -0.5},
     1.005712135322484,
     {1.51754419464537, 2.1508108244567414, 5.2424198713594707, 4.1406906849427028,
      5.8027115696326197, 3.5667920713680066}},
    {{10.0, 3.2, 1.2, -2.0},
     0.55446930510281112,
     {1.2675469048771157, 4.1410935891713878, 5.0956195492487169, 3.9435006213367698,
      7.6455422692112709, 1.2538997132245817}},
    {{5.0, 4.9, 1.1, -0.1},
     1.7827286825912783,
     {1.1111973726874729, 1.5159247029873903, 3.5442691805223259, 4.9100210053229159,
      3.0574897053701866, 4.9881372305718967}},
    {{12.0, 2.5, 2.4, -3.0},
     0.43546816806693006,
     {2.5151693508309685, 7.8117227817140353, 2.8835213766312568, 9.5779807409420119,
      7.2953022818511464, 6.8021975157299064}},
    {{8.0, 7.999, 0.2, -1.5},
     1.5631491451978374,
     {0.26509183889487031, 2.8196249068504207, 7.7758590261575629, 7.9994203913227855,
      1.6620922622925269, 7.7406573454932213}},
}};

// Accuracy the double-precision policy keeps relative to the promoted values.
constexpr double POLICY_TOL = 2.0e-15;

RadialRoots transitRoots(const std::array<double, 4> &r) {
  RadialRoots roots;
  roots.nReal = 4;
  roots.type = RadialMotionType::Transit;
  for (std::size_t i = 0; i < r.size(); ++i) {
    roots.roots.at(i) = {r.at(i), 0.0};
  }
  return roots;
}

void testDoublePolicyHalfPeriod() {
  std::cout << "Test 16: radialHalfPeriod under promote_double<false> vs promoted baseline\n";

  double worstRatio = 0.0;
  double worstRel = 0.0;
  for (const PromotedBaseline &row : PROMOTED_BASELINE) {
    const auto &[r1, r2, r3, r4] = row.roots;
    const double m = ((r2 - r3) * (r1 - r4)) / ((r1 - r3) * (r2 - r4));
    const double k = std::sqrt(m);
    // kappa = (k / K) dK/dk = E / ((1 - k^2) K) - 1.
    const double kappa =
        (boost::math::ellint_2(k) / ((1.0 - m) * boost::math::ellint_1(k))) - 1.0;
    const double rel =
        std::abs(radialHalfPeriod(transitRoots(row.roots)) - row.halfPeriod) / row.halfPeriod;
    worstRel = std::max(worstRel, rel);
    worstRatio = std::max(worstRatio, rel / (POLICY_TOL * std::max(1.0, kappa)));
  }
  const std::string detailBuffer = std::format(
      "max rel diff {:.3e}, max (rel diff)/(2e-15 max(1, kappa)) {:.3f}", worstRel, worstRatio);
  std::cout << "  " << detailBuffer << "\n";
  check(worstRatio <= 1.0, "half period within 2e-15 x condition number of the promoted value",
        detailBuffer);
}

void testDoublePolicyRadius() {
  std::cout << "Test 17: rAnalytic under promote_double<false> vs promoted baseline\n";

  double worstRatio = 0.0;
  double worstRel = 0.0;
  for (const PromotedBaseline &row : PROMOTED_BASELINE) {
    const RadialRoots roots = transitRoots(row.roots);
    const auto &[r1, r2, r3, r4] = row.roots;
    // r(s) = (A - B s) / (C - D s) with s = sn^2.
    const double aa = r3 * (r1 - r4);
    const double bb = r4 * (r1 - r3);
    const double cc = r1 - r4;
    const double dd = r1 - r3;
    for (std::size_t i = 0; i < BASELINE_LAMBDAS.size(); ++i) {
      const double ref = row.radius.at(i);
      const double sn2 = (aa - (ref * cc)) / (bb - (ref * dd));
      const double denom = cc - (dd * sn2);
      const double drdSn = 2.0 * std::sqrt(std::max(sn2, 0.0)) * ((aa * dd) - (bb * cc)) /
                           (denom * denom);
      const double diff = std::abs(rAnalytic(BASELINE_LAMBDAS.at(i), roots) - ref);
      worstRel = std::max(worstRel, diff / std::abs(ref));
      worstRatio =
          std::max(worstRatio, diff / (POLICY_TOL * std::max(std::abs(ref), std::abs(drdSn))));
    }
  }
  const std::string detailBuffer = std::format(
      "max rel diff {:.3e}, max diff/(2e-15 max(|r|, |dr/dsn|)) {:.3f}", worstRel, worstRatio);
  std::cout << "  " << detailBuffer << "\n";
  check(worstRatio <= 1.0, "r(lambda) within a 2e-15 sn error of the promoted value",
        detailBuffer);
}

} // namespace

int main() try {
  std::cout << "\n================================================\n"
            << "ANALYTIC KERR GEODESIC + REPRODUCIBILITY VALIDATION\n"
            << "analytic_kerr_geodesic.h + reproducibility.h\n"
            << "================================================\n\n";

  testRadialPotentialSchwarzschildPhotonSphere();
  std::cout << "\n";
  testCriticalImpactParamsSchwarzschild();
  std::cout << "\n";
  testCriticalImpactParamsKerrSelfConsistency();
  std::cout << "\n";
  testRadialPotentialPositiveOffPhotonSphere();
  std::cout << "\n";
  testProgradePhotonOrbitSchwarzschild();
  std::cout << "\n";
  testRetrogradePhotonOrbitSchwarzschild();
  std::cout << "\n";
  testProgradePhotonOrbitExtremal();
  std::cout << "\n";
  testRetrogradePhotonOrbitExtremal();
  std::cout << "\n";
  testPhotonOrbitMonotonicity();
  std::cout << "\n";
  testManifestNonEmpty();
  std::cout << "\n";
  testManifestCodeKey();
  std::cout << "\n";
  testManifestBuildType();
  std::cout << "\n";
  testManifestAddDoubleRoundTrip();
  std::cout << "\n";
  testManifestAddIntRoundTrip();
  std::cout << "\n";
  testManifestAddPhysicsParams();
  std::cout << "\n";
  testDoublePolicyHalfPeriod();
  std::cout << "\n";
  testDoublePolicyRadius();
  std::cout << "\n";

  std::cout << "================================================\n"
            << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
            << "================================================\n\n";

  return gAllPass ? 0 : 1;
} catch (const std::exception &error) {
  return std::fprintf(stderr, "[FAIL] Unexpected exception: %s\n", error.what()) < 0 ? 2 : 1;
} catch (...) {
  return std::fprintf(stderr, "[FAIL] Unexpected nonstandard exception\n") < 0 ? 2 : 1;
}
