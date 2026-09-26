/**
 * @file tests/elliptic_integrals_test.cpp
 * @brief Validation tests for elliptic_integrals.h.
 *
 * WHY: Carlson symmetric forms, complete/incomplete elliptic integrals, and
 *      Jacobi functions are used for analytic Kerr geodesics and gravitational
 *      lensing.  Their exact limits at degenerate arguments are the fastest
 *      catch-all for coding errors in the iterative algorithms.
 *
 * Tests (12):
 *   Carlson forms (1-2):
 *   1.  carlsonRf(1,1,1) = 1  (Rf(x,x,x) = 1/sqrt(x) at x=1).
 *   2.  carlsonRc(1,1)   = 1  (Rc(x,x)   = 1/sqrt(x) at x=1).
 *   Complete elliptic integrals (3-6):
 *   3.  ellipticK(0) = pi/2  (degenerate k=0 limit).
 *   4.  ellipticE(0) = pi/2  (degenerate k=0 limit).
 *   5.  ellipticE(1) = 1     (extremal k=1 limit).
 *   6.  ellipticK monotonically increases: K(0) < K(0.5) < K(0.9).
 *   Incomplete elliptic integrals (7):
 *   7.  ellipticF(phi, 0) = phi  (k=0: reduces to arc length).
 *   Jacobi elliptic functions (8-11):
 *   8.  jacobiSn(0, k) = 0  (zero at origin).
 *   9.  jacobiCn(0, k) = 1  (unit at origin).
 *  10.  jacobiDn(0, k) = 1  (unit at origin).
 *  11.  sn^2(u,k) + cn^2(u,k) = 1  (Pythagorean identity).
 *  12.  dn^2(u,k) + k^2*sn^2(u,k) = 1  (second Pythagorean identity).
 *   Gravitational lensing (13):
 *  13.  deflectionAngleSchwarzschild(b <= b_crit) = infinity (captured photon).
 *   Carlson forms against mpmath (14-15), tests/carlson_reference.inc from
 *   scripts/gen_carlson_reference.py:
 *  14.  carlsonRf, carlsonRd, carlsonRj within 1e-15 relative on generic,
 *       complete, incomplete, nearly equal and one-zero arguments.
 *  15.  carlsonRc within 1e-15 relative for x < y, x > y, x = y, x = 0.
 *   Kerr equatorial photon orbits (16):
 *  16.  criticalImpactParameterKerr = 3 sqrt(3) M at a = 0, and the Bardeen
 *       value 3 sqrt(M r_ph) -+ a (= xi of criticalImpactParams at eta = 0)
 *       at a = 0.9 M and a = M, prograde and retrograde.
 */

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <exception>
#include <format>
#include <iostream>
#include <iterator>
#include <numbers>
#include <numeric>
#include <string>
#include <string_view>

#include "../src/physics/analytic_kerr_geodesic.h"
#include "../src/physics/elliptic_integrals.h"

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
// Tests 1-2: Carlson symmetric forms at degenerate arguments
// ============================================================================

bool testCarlsonRfEqual() {
  std::cout << "Test 1: carlsonRf(1,1,1) = 1  (Rf(x,x,x) = 1/sqrt(x))\n";

  const double rf = carlsonRf(1.0, 1.0, 1.0);
  const double expected = 1.0;
  const std::string buf = std::format("Rf(1,1,1) = {:.12f} (expected 1.0)", rf);
  check(std::abs(rf - expected) < 1.0e-10, "carlsonRf(1,1,1) = 1", buf);
  return true;
}

bool testCarlsonRcEqual() {
  std::cout << "Test 2: carlsonRc(1,1) = 1  (Rc(x,x) = 1/sqrt(x))\n";

  const double rc = carlsonRc(1.0, 1.0);
  const double expected = 1.0;
  const std::string buf = std::format("Rc(1,1) = {:.12f} (expected 1.0)", rc);
  check(std::abs(rc - expected) < 1.0e-10, "carlsonRc(1,1) = 1", buf);
  return true;
}

// ============================================================================
// Tests 3-6: Complete elliptic integrals
// ============================================================================

bool testEllipticKZero() {
  std::cout << "Test 3: ellipticK(0) = pi/2\n";

  const double kVal = ellipticK(0.0);
  const double expected = std::numbers::pi / 2.0;
  const std::string buf = std::format("K(0) = {:.12f}, pi/2 = {:.12f}", kVal, expected);
  check(std::abs(kVal - expected) < 1.0e-10, "ellipticK(0) = pi/2", buf);
  return true;
}

bool testEllipticEZero() {
  std::cout << "Test 4: ellipticE(0) = pi/2\n";

  const double eVal = ellipticE(0.0);
  const double expected = std::numbers::pi / 2.0;
  const std::string buf = std::format("E(0) = {:.12f}, pi/2 = {:.12f}", eVal, expected);
  check(std::abs(eVal - expected) < 1.0e-10, "ellipticE(0) = pi/2", buf);
  return true;
}

bool testEllipticEOne() {
  std::cout << "Test 5: ellipticE(1) = 1  (extremal limit)\n";

  const double eVal = ellipticE(1.0);
  const std::string buf = std::format("E(1) = {:.12f} (expected 1.0)", eVal);
  check(std::abs(eVal - 1.0) < 1.0e-14, "ellipticE(1) = 1 exactly", buf);
  return true;
}

bool testEllipticKMonotone() {
  std::cout << "Test 6: ellipticK(0) < ellipticK(0.5) < ellipticK(0.9)\n";

  const double k0 = ellipticK(0.0);
  const double k5 = ellipticK(0.5);
  const double k9 = ellipticK(0.9);
  const std::string buf = std::format("K(0)={:.4f}, K(0.5)={:.4f}, K(0.9)={:.4f}", k0, k5, k9);
  check(k0 < k5 && k5 < k9, "K(k) monotonically increasing with k", buf);
  return true;
}

// ============================================================================
// Test 7: Incomplete elliptic integral degenerate case
// ============================================================================

bool testEllipticFKZero() {
  std::cout << "Test 7: ellipticF(phi, 0) = phi  (k=0: F reduces to angle)\n";

  // For k=0: F(phi, 0) = integral_0^phi d-theta / sqrt(1-0) = phi.
  // Tests four representative angles.
  bool allOk = true;
  const double angles[] = {0.3, 0.7, 1.1, std::numbers::pi / 4.0};
  for (const double phi : angles) {
    const double fVal = ellipticF(phi, 0.0);
    if (std::abs(fVal - phi) > 1.0e-12) {
      allOk = false;
    }
  }
  check(allOk, "ellipticF(phi, 0) = phi for phi in {0.3, 0.7, 1.1, pi/4}");
  return true;
}

// ============================================================================
// Tests 8-12: Jacobi elliptic functions
// ============================================================================

bool testJacobiSnZero() {
  std::cout << "Test 8: jacobiSn(0, k) = 0  (odd function, zero at origin)\n";

  bool allOk = true;
  for (const double kMod : {0.0, 0.3, 0.5, 0.9}) {
    if (std::abs(jacobiSn(0.0, kMod)) > 1.0e-14) {
      allOk = false;
    }
  }
  check(allOk, "jacobiSn(0, k) = 0 for k in {0, 0.3, 0.5, 0.9}");
  return true;
}

bool testJacobiCnZero() {
  std::cout << "Test 9: jacobiCn(0, k) = 1  (unit at origin)\n";

  bool allOk = true;
  for (const double kMod : {0.0, 0.3, 0.5, 0.9}) {
    if (std::abs(jacobiCn(0.0, kMod) - 1.0) > 1.0e-14) {
      allOk = false;
    }
  }
  check(allOk, "jacobiCn(0, k) = 1 for k in {0, 0.3, 0.5, 0.9}");
  return true;
}

bool testJacobiDnZero() {
  std::cout << "Test 10: jacobiDn(0, k) = 1  (unit at origin)\n";

  bool allOk = true;
  for (const double kMod : {0.0, 0.3, 0.5, 0.9}) {
    if (std::abs(jacobiDn(0.0, kMod) - 1.0) > 1.0e-14) {
      allOk = false;
    }
  }
  check(allOk, "jacobiDn(0, k) = 1 for k in {0, 0.3, 0.5, 0.9}");
  return true;
}

bool testJacobiPythagorean1() {
  std::cout << "Test 11: sn^2(u,k) + cn^2(u,k) = 1  (Pythagorean identity)\n";

  // Verify at several (u, k) pairs.
  bool allOk = true;
  const double uVals[] = {0.5, 1.0, 1.5};
  const double kVals[] = {0.3, 0.7, 0.99};
  double worstErr = 0.0;
  for (const double uVal : uVals) {
    for (const double kMod : kVals) {
      const double sn = jacobiSn(uVal, kMod);
      const double cn = jacobiCn(uVal, kMod);
      const double err = std::abs((sn * sn) + (cn * cn) - 1.0);
      worstErr = std::max(worstErr, err);
      if (err > 1.0e-12) {
        allOk = false;
      }
    }
  }
  const std::string buf = std::format("max |sn^2+cn^2-1| = {:.4e}", worstErr);
  check(allOk, "sn^2 + cn^2 = 1 for (u,k) in {0.5,1,1.5} x {0.3,0.7,0.99}", buf);
  return true;
}

bool testJacobiPythagorean2() {
  std::cout << "Test 12: dn^2(u,k) + k^2*sn^2(u,k) = 1  (second identity)\n";

  bool allOk = true;
  const double uVals[] = {0.5, 1.0, 1.5};
  const double kVals[] = {0.3, 0.7, 0.99};
  double worstErr = 0.0;
  for (const double uVal : uVals) {
    for (const double kMod : kVals) {
      const double sn = jacobiSn(uVal, kMod);
      const double dn = jacobiDn(uVal, kMod);
      const double err = std::abs((dn * dn) + (kMod * kMod * sn * sn) - 1.0);
      worstErr = std::max(worstErr, err);
      if (err > 1.0e-12) {
        allOk = false;
      }
    }
  }
  const std::string buf = std::format("max |dn^2+k^2*sn^2-1| = {:.4e}", worstErr);
  check(allOk, "dn^2 + k^2*sn^2 = 1 for (u,k) in {0.5,1,1.5} x {0.3,0.7,0.99}", buf);
  return true;
}

// ============================================================================
// Test 13: Gravitational lensing -- captured photon
// ============================================================================

bool testDeflectionCaptured() {
  std::cout << "Test 13: deflectionAngleSchwarzschild(b <= b_crit) = infinity\n";

  // Critical impact parameter: b_crit = (3*sqrt(3)/2) * rS ~ 2.598 * rS
  const double rS = 3.0e5; // 1 km in cm (representative)
  const double bCrit = (3.0 * std::numbers::sqrt3 / 2.0) * rS;

  // Below critical: captured, deflection is infinite
  const double alpha = deflectionAngleSchwarzschild(0.9 * bCrit, rS);
  // Use large-value sentinel instead of std::isinf (avoids -ffinite-math-only).
  const bool captured = (alpha > 1.0e100) || (alpha != alpha);
  const std::string buf =
      std::format("alpha(b=0.9*b_crit) = {} (expected inf)", captured ? "inf" : "finite");
  check(captured, "photon captured when b < b_crit -> alpha = infinity", buf);
  return true;
}

// ============================================================================
// Tests 14-15: Carlson forms against the mpmath referee
// ============================================================================

struct CarlsonRow {
  std::string_view group;
  double x = 0.0;
  double y = 0.0;
  double z = 0.0;
  double p = 0.0;
  double rf = 0.0;
  double rd = 0.0;
  double rj = 0.0;
};

struct CarlsonRcRow {
  double x = 0.0;
  double y = 0.0;
  double rc = 0.0;
};

#include "carlson_reference.inc"

// Relative accuracy of the duplication plus DLMF 19.36 series at CARLSON_REL_TOL.
constexpr double CARLSON_TOL = 1.0e-15;

double relDiff(double got, double ref) { return std::abs(got - ref) / std::abs(ref); }

bool testCarlsonReference() {
  std::cout << "Test 14: carlsonRf/Rd/Rj vs mpmath (40 digits), max relative error\n";

  double worst = 0.0;
  for (const std::string_view group : {"gen", "Kk", "inc", "near", "zero"}) {
    double wf = 0.0;
    double wd = 0.0;
    double wj = 0.0;
    for (const CarlsonRow &row : CARLSON_ROWS) {
      if (row.group != group) {
        continue;
      }
      wf = std::max(wf, relDiff(carlsonRf(row.x, row.y, row.z), row.rf));
      wd = std::max(wd, relDiff(carlsonRd(row.x, row.y, row.z), row.rd));
      wj = std::max(wj, relDiff(carlsonRj(row.x, row.y, row.z, row.p), row.rj));
    }
    std::cout << std::format("  {:<5} R_F {:.3e}  R_D {:.3e}  R_J {:.3e}\n", group, wf, wd, wj);
    worst = std::max({worst, wf, wd, wj});
  }
  check(worst <= CARLSON_TOL, "R_F, R_D, R_J within 1e-15 of the referee",
        std::format("max {:.3e}", worst));
  return true;
}

bool testCarlsonRcReference() {
  std::cout << "Test 15: carlsonRc closed form vs mpmath, max relative error\n";

  const double worst = std::accumulate(std::begin(CARLSON_RC_ROWS), std::end(CARLSON_RC_ROWS), 0.0,
                                       [](double w, const CarlsonRcRow &row) {
                                         return std::max(w, relDiff(carlsonRc(row.x, row.y), row.rc));
                                       });
  std::cout << std::format("  R_C {:.3e}\n", worst);
  check(worst <= CARLSON_TOL, "R_C within 1e-15 of the referee", std::format("max {:.3e}", worst));
  return true;
}

// ============================================================================
// Test 16: Kerr equatorial critical impact parameter
// ============================================================================

bool testCriticalImpactParameterKerr() {
  std::cout << "Test 16: criticalImpactParameterKerr vs Bardeen / criticalImpactParams\n";

  const double rS = 2.0; // M = 1
  const double b0 = criticalImpactParameterKerr(rS, 0.0, true);
  bool ok = relDiff(b0, 3.0 * std::numbers::sqrt3) < 1.0e-15 &&
            relDiff(criticalImpactParameterKerr(rS, 0.0, false), 3.0 * std::numbers::sqrt3) <
                1.0e-15;
  ok = ok && relDiff(criticalImpactParameterKerr(rS, 1.0, true), 2.0) < 1.0e-14 &&
       relDiff(criticalImpactParameterKerr(rS, 1.0, false), 7.0) < 1.0e-14;
  double worst = 0.0;
  for (const double a : {0.5, 0.9, 0.998}) {
    // Chandrasekhar closed form b = -a +- 6 cos(acos(-+a)/3), M = 1.
    const double pro = -a + (6.0 * std::cos(std::acos(-a) / 3.0));
    const double retro = a + (6.0 * std::cos(std::acos(a) / 3.0));
    const double xiPro = criticalImpactParams(progradePhotonOrbit(a), a).xi;
    const double xiRetro = criticalImpactParams(retrogradePhotonOrbit(a), a).xi;
    worst = std::max({worst, relDiff(criticalImpactParameterKerr(rS, a, true), pro),
                      relDiff(criticalImpactParameterKerr(rS, a, false), retro),
                      relDiff(criticalImpactParameterKerr(rS, a, true), xiPro),
                      relDiff(criticalImpactParameterKerr(rS, a, false), -xiRetro)});
  }
  const std::string detail =
      std::format("b(a=0) = {:.15f} (3 sqrt 3 = {:.15f}); a in {{0.5, 0.9, 0.998}} max rel {:.3e}",
                  b0, 3.0 * std::numbers::sqrt3, worst);
  std::cout << "  " << detail << "\n";
  check(ok && worst < 1.0e-13, "b_c = 3 sqrt(M r_ph) -+ a, prograde and retrograde", detail);
  return true;
}

} // namespace

int main() try {
  std::cout << "\n================================================\n"
            << "ELLIPTIC INTEGRALS VALIDATION\n"
            << "Algorithms: Carlson (1995), DLMF Ch.19, Bozza (2002)\n"
            << "================================================\n\n";

  testCarlsonRfEqual();
  std::cout << "\n";
  testCarlsonRcEqual();
  std::cout << "\n";
  testEllipticKZero();
  std::cout << "\n";
  testEllipticEZero();
  std::cout << "\n";
  testEllipticEOne();
  std::cout << "\n";
  testEllipticKMonotone();
  std::cout << "\n";
  testEllipticFKZero();
  std::cout << "\n";
  testJacobiSnZero();
  std::cout << "\n";
  testJacobiCnZero();
  std::cout << "\n";
  testJacobiDnZero();
  std::cout << "\n";
  testJacobiPythagorean1();
  std::cout << "\n";
  testJacobiPythagorean2();
  std::cout << "\n";
  testDeflectionCaptured();
  std::cout << "\n";
  testCarlsonReference();
  std::cout << "\n";
  testCarlsonRcReference();
  std::cout << "\n";
  testCriticalImpactParameterKerr();
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
