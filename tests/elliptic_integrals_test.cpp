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
 */

#include <algorithm>
#include <cmath>
#include <cstdio>
#include <iostream>
#include <numbers>

#include "../src/physics/elliptic_integrals.h"

using namespace physics;

namespace {

bool gAllPass = true;

void check(bool cond, const char *label, const char *detail = "") {
    if (cond) {
        std::cout << "  [PASS] " << label << "\n";
    } else {
        std::cout << "  [FAIL] " << label;
        if (detail[0] != '\0') {
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

    const double rf       = carlsonRf(1.0, 1.0, 1.0);
    const double expected = 1.0;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "Rf(1,1,1) = %.12f (expected 1.0)", rf); // NOLINT(cert-err33-c)
    check(std::abs(rf - expected) < 1.0e-10, "carlsonRf(1,1,1) = 1", buf);
    return true;
}

bool testCarlsonRcEqual() {
    std::cout << "Test 2: carlsonRc(1,1) = 1  (Rc(x,x) = 1/sqrt(x))\n";

    const double rc       = carlsonRc(1.0, 1.0);
    const double expected = 1.0;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "Rc(1,1) = %.12f (expected 1.0)", rc); // NOLINT(cert-err33-c)
    check(std::abs(rc - expected) < 1.0e-10, "carlsonRc(1,1) = 1", buf);
    return true;
}

// ============================================================================
// Tests 3-6: Complete elliptic integrals
// ============================================================================

bool testEllipticKZero() {
    std::cout << "Test 3: ellipticK(0) = pi/2\n";

    const double kVal     = ellipticK(0.0);
    const double expected = std::numbers::pi / 2.0;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "K(0) = %.12f, pi/2 = %.12f", kVal, expected); // NOLINT(cert-err33-c)
    check(std::abs(kVal - expected) < 1.0e-10, "ellipticK(0) = pi/2", buf);
    return true;
}

bool testEllipticEZero() {
    std::cout << "Test 4: ellipticE(0) = pi/2\n";

    const double eVal     = ellipticE(0.0);
    const double expected = std::numbers::pi / 2.0;
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "E(0) = %.12f, pi/2 = %.12f", eVal, expected); // NOLINT(cert-err33-c)
    check(std::abs(eVal - expected) < 1.0e-10, "ellipticE(0) = pi/2", buf);
    return true;
}

bool testEllipticEOne() {
    std::cout << "Test 5: ellipticE(1) = 1  (extremal limit)\n";

    const double eVal = ellipticE(1.0);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "E(1) = %.12f (expected 1.0)", eVal); // NOLINT(cert-err33-c)
    check(std::abs(eVal - 1.0) < 1.0e-14, "ellipticE(1) = 1 exactly", buf);
    return true;
}

bool testEllipticKMonotone() {
    std::cout << "Test 6: ellipticK(0) < ellipticK(0.5) < ellipticK(0.9)\n";

    const double k0 = ellipticK(0.0);
    const double k5 = ellipticK(0.5);
    const double k9 = ellipticK(0.9);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "K(0)=%.4f, K(0.5)=%.4f, K(0.9)=%.4f", k0, k5, k9); // NOLINT(cert-err33-c)
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
    char buf[128];
    double worstErr = 0.0;
    for (const double uVal : uVals) {
        for (const double kMod : kVals) {
            const double sn  = jacobiSn(uVal, kMod);
            const double cn  = jacobiCn(uVal, kMod);
            const double err = std::abs((sn * sn) + (cn * cn) - 1.0);
            worstErr = std::max(worstErr, err);
            if (err > 1.0e-12) {
                allOk = false;
            }
        }
    }
    (void)std::snprintf(buf, sizeof(buf), "max |sn^2+cn^2-1| = %.4e", worstErr); // NOLINT(cert-err33-c)
    check(allOk, "sn^2 + cn^2 = 1 for (u,k) in {0.5,1,1.5} x {0.3,0.7,0.99}", buf);
    return true;
}

bool testJacobiPythagorean2() {
    std::cout << "Test 12: dn^2(u,k) + k^2*sn^2(u,k) = 1  (second identity)\n";

    bool allOk = true;
    const double uVals[] = {0.5, 1.0, 1.5};
    const double kVals[] = {0.3, 0.7, 0.99};
    char buf[128];
    double worstErr = 0.0;
    for (const double uVal : uVals) {
        for (const double kMod : kVals) {
            const double sn  = jacobiSn(uVal, kMod);
            const double dn  = jacobiDn(uVal, kMod);
            const double err = std::abs((dn * dn) + (kMod * kMod * sn * sn) - 1.0);
            worstErr = std::max(worstErr, err);
            if (err > 1.0e-12) {
                allOk = false;
            }
        }
    }
    (void)std::snprintf(buf, sizeof(buf), "max |dn^2+k^2*sn^2-1| = %.4e", worstErr); // NOLINT(cert-err33-c)
    check(allOk, "dn^2 + k^2*sn^2 = 1 for (u,k) in {0.5,1,1.5} x {0.3,0.7,0.99}", buf);
    return true;
}

// ============================================================================
// Test 13: Gravitational lensing -- captured photon
// ============================================================================

bool testDeflectionCaptured() {
    std::cout << "Test 13: deflectionAngleSchwarzschild(b <= b_crit) = infinity\n";

    // Critical impact parameter: b_crit = (3*sqrt(3)/2) * rS ~ 2.598 * rS
    const double rS   = 3.0e5; // 1 km in cm (representative)
    const double bCrit = (3.0 * std::numbers::sqrt3 / 2.0) * rS;

    // Below critical: captured, deflection is infinite
    const double alpha  = deflectionAngleSchwarzschild(0.9 * bCrit, rS);
    // Use large-value sentinel instead of std::isinf (avoids -ffinite-math-only).
    const bool captured = (alpha > 1.0e100) || (alpha != alpha);
    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "alpha(b=0.9*b_crit) = %s (expected inf)", // NOLINT(cert-err33-c)
                        captured ? "inf" : "finite");
    check(captured, "photon captured when b < b_crit -> alpha = infinity", buf);
    return true;
}

} // namespace

// NOLINTNEXTLINE(bugprone-exception-escape) -- test binary; exceptions propagate to crash
int main() {
    std::cout << "\n================================================\n"
              << "ELLIPTIC INTEGRALS VALIDATION\n"
              << "Algorithms: Carlson (1977), DLMF Ch.19, Bozza (2002)\n"
              << "================================================\n\n";

    testCarlsonRfEqual();         std::cout << "\n";
    testCarlsonRcEqual();         std::cout << "\n";
    testEllipticKZero();          std::cout << "\n";
    testEllipticEZero();          std::cout << "\n";
    testEllipticEOne();           std::cout << "\n";
    testEllipticKMonotone();      std::cout << "\n";
    testEllipticFKZero();         std::cout << "\n";
    testJacobiSnZero();           std::cout << "\n";
    testJacobiCnZero();           std::cout << "\n";
    testJacobiDnZero();           std::cout << "\n";
    testJacobiPythagorean1();     std::cout << "\n";
    testJacobiPythagorean2();     std::cout << "\n";
    testDeflectionCaptured();     std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
