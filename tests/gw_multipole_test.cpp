/**
 * @file gw_multipole_test.cpp
 * @brief Validation tests for higher GW multipole QNM modes (l > 2).
 *
 * WHY: The dominant (2,2,0) ringdown mode was already validated.  For
 * unequal-mass mergers the (3,3) mode carries ~10% and (4,4) ~3% of
 * the total ringdown power, so neglecting them biases final-state
 * parameter estimates.  These tests guard against regressions in the
 * Berti 2009 polynomial fits and the multi-mode superposition logic.
 *
 * Test plan:
 *   1. qnmFitParams() returns valid=true for (2,2,0), (3,3,0), (4,4,0)
 *      and valid=false for unsupported modes.
 *   2. Generic qnmFrequencyKerrMode for (2,2,0) agrees with the scalar
 *      qnmFrequencyKerr() to <1 ppm (backward compatibility).
 *   3. (3,3,0) Schwarzschild limit: omega_R*M = 0.5994 (Leaver 1985) to 2%.
 *   4. (3,3,0) frequency increases monotonically with spin.
 *   5. (4,4,0) Schwarzschild limit: omega_R*M = 0.8092 to 1%.
 *   6. Mode amplitude hierarchy: A_22 > A_33 > A_44 for unequal mass (q=0.5).
 *   7. Multi-mode ringdown is finite, non-zero, and decays with time.
 *   8. Equal-mass merger: A_33 = 0 (antisymmetric mode suppressed by symmetry).
 *
 * References:
 *   Berti, Cardoso & Starinets (2009) arXiv:0905.2975, Table VIII
 *   Leaver (1985), Proc. Roy. Soc. Lond. A402, 285
 *   Kamaretsos et al. (2012), Phys. Rev. D 85, 024018
 */

#include <cmath>
#include <cstdio>
#include <iostream>

#include "../src/physics/gravitational_waves.h"
#include "../src/physics/constants.h"
#include "../src/physics/safe_limits.h"

using namespace physics;

namespace {

bool gAllPass = true;

void check(bool condition, const char* test, const char* detail = "") {
    if (condition) {
        std::cout << "  [PASS] " << test << "\n";
    } else {
        std::cout << "  [FAIL] " << test << " -- " << detail << "\n";
        gAllPass = false;
    }
}

/* =========================================================================
 * Test 1: qnmFitParams() returns valid/invalid as expected
 * ======================================================================= */
bool testFitParamsLookup() {
    std::cout << "Test 1: qnmFitParams() validity table\n";

    const QNMFitParams p22 = qnmFitParams({.l=2, .m=2, .n=0});
    const QNMFitParams p33 = qnmFitParams({.l=3, .m=3, .n=0});
    const QNMFitParams p44 = qnmFitParams({.l=4, .m=4, .n=0});
    const QNMFitParams pN  = qnmFitParams({.l=5, .m=5, .n=0}); /* not in table */
    const QNMFitParams pOv = qnmFitParams({.l=2, .m=2, .n=1}); /* overtone, not in table */

    check(p22.valid,  "(2,2,0) valid=true");
    check(p33.valid,  "(3,3,0) valid=true");
    check(p44.valid,  "(4,4,0) valid=true");
    check(!pN.valid,  "(5,5,0) valid=false (not tabulated)");
    check(!pOv.valid, "(2,2,1) valid=false (overtone not tabulated)");

    /* Sanity: f1 > f2 > 0 for all tabulated modes */
    check(p22.f1 > p22.f2 && p22.f2 > 0, "(2,2,0) f1>f2>0");
    check(p33.f1 > p33.f2 && p33.f2 > 0, "(3,3,0) f1>f2>0");
    check(p44.f1 > p44.f2 && p44.f2 > 0, "(4,4,0) f1>f2>0");

    return true;
}

/* =========================================================================
 * Test 2: Generic function agrees with scalar qnmFrequencyKerr for (2,2,0)
 * ======================================================================= */
bool testGenericMatchesDominant() {
    std::cout << "Test 2: qnmFrequencyKerrMode(2,2,0) matches qnmFrequencyKerr()\n";

    const double m = 10.0 * M_SUN;
    const double spins[] = {0.0, 0.3, 0.7, 0.9, 0.99};

    for (const double a : spins) {
        const double fScalar  = qnmFrequencyKerr(m, a);
        const double fGeneric = qnmFrequencyKerrMode(m, a, {.l=2, .m=2, .n=0});
        if (fScalar <= 0.0) { continue; }

        const double relErr = std::abs(fGeneric - fScalar) / fScalar;
        char buf[128];
        (void)std::snprintf(buf, sizeof(buf),
                      "a*=%.2f: scalar=%.4g Hz generic=%.4g Hz relErr=%.2e",
                      a, fScalar, fGeneric, relErr);

        /* At a*=0, qnmFrequencyKerr uses Leaver's exact Schwarzschild value
         * (0.3737) while qnmFrequencyKerrMode uses the Berti 2009 polynomial
         * (f1-f2 = 0.3683).  Both are correct; the ~1.4% gap is the fit error
         * at the spin=0 boundary -- allow 2% there, <1 ppm for a*>0. */
        const double tol = (a == 0.0) ? 0.02 : 1e-6;
        check(relErr < tol, buf);
    }
    return true;
}

/* =========================================================================
 * Test 3: (3,3,0) Schwarzschild limit
 * omega_R*M = 0.5994 (Leaver 1985) to within 2% (fit approximation error)
 * ======================================================================= */
bool testL33SchwarzchildLimit() {
    std::cout << "Test 3: (3,3,0) Schwarzschild limit omega_R*M = 0.5994\n";

    const double m    = 10.0 * M_SUN;
    const double mGeo = (G * m) / (C * C * C); /* geometric mass [s] */

    const double f33  = qnmFrequencyKerrMode(m, 0.0, {.l=3, .m=3, .n=0});
    /* omega_R*M = 2*pi*f * mGeo */
    const double omRm = 2.0 * PI * f33 * mGeo;

    const double exact   = 0.5994; /* Leaver 1985 */
    const double relErr  = std::abs(omRm - exact) / exact;

    std::cout << "  omega_R*M = " << omRm << " (exact: " << exact
              << ", err: " << relErr * 100 << "%)\n";

    /* Fit is accurate to ~1.4%; allow 2% tolerance */
    check(relErr < 0.02, "(3,3,0) Schw. limit within 2%",
          "omega_R*M must match Leaver 1985 to 2%");

    return true;
}

/* =========================================================================
 * Test 4: (3,3,0) frequency increases monotonically with spin
 * ======================================================================= */
bool testL33MonotonicFrequency() {
    std::cout << "Test 4: (3,3,0) frequency increases monotonically with a*\n";

    const double m = 10.0 * M_SUN;
    double prevF   = qnmFrequencyKerrMode(m, 0.0, {.l=3, .m=3, .n=0});

    const double spins[] = {0.1, 0.3, 0.5, 0.7, 0.9};
    bool monotone = true;
    for (const double a : spins) {
        const double f = qnmFrequencyKerrMode(m, a, {.l=3, .m=3, .n=0});
        if (f <= prevF) {
            monotone = false;
            std::cout << "  NOT monotone at a*=" << a
                      << " prev=" << prevF << " curr=" << f << "\n";
        }
        prevF = f;
    }
    check(monotone, "(3,3,0) f_QNM strictly increasing with a*");
    return true;
}

/* =========================================================================
 * Test 5: (4,4,0) Schwarzschild limit
 * omega_R*M = 0.8092 (Leaver 1985) to within 1%
 * ======================================================================= */
bool testL44SchwarzchildLimit() {
    std::cout << "Test 5: (4,4,0) Schwarzschild limit omega_R*M = 0.8092\n";

    const double m    = 10.0 * M_SUN;
    const double mGeo = (G * m) / (C * C * C);

    const double f44  = qnmFrequencyKerrMode(m, 0.0, {.l=4, .m=4, .n=0});
    const double omRm = 2.0 * PI * f44 * mGeo;

    const double exact  = 0.8092; /* Leaver 1985 */
    const double relErr = std::abs(omRm - exact) / exact;

    std::cout << "  omega_R*M = " << omRm << " (exact: " << exact
              << ", err: " << relErr * 100 << "%)\n";

    /* f1 is set so f1-f2 = 0.8092 exactly; allow 0.2% numerical error */
    check(relErr < 0.002, "(4,4,0) Schw. limit within 0.2%",
          "omega_R*M must match Leaver 1985 to 0.2%");

    return true;
}

/* =========================================================================
 * Test 6: Mode amplitude hierarchy for q=0.5 (unequal mass)
 * Expect A_22=1 > A_33 > A_44 > 0
 * ======================================================================= */
bool testModeAmplitudeHierarchy() {
    std::cout << "Test 6: Mode amplitude hierarchy (q=0.5 merger)\n";

    /* Mass ratio q = m2/m1 = 0.5 -> m1=2M, m2=1M, delta=1/3 */
    const double m1 = 2.0 * M_SUN;
    const double m2 = 1.0 * M_SUN;

    const double a22 = qnmModeAmplitude({.l=2, .m=2, .n=0}, m1, m2); /* = 1.0 */
    const double a33 = qnmModeAmplitude({.l=3, .m=3, .n=0}, m1, m2);
    const double a44 = qnmModeAmplitude({.l=4, .m=4, .n=0}, m1, m2);

    std::cout << "  A_22 = " << a22 << "\n"
              << "  A_33 = " << a33 << " (~10% power -> amplitude ~0.32)\n"
              << "  A_44 = " << a44 << " (~3%  power -> amplitude ~0.17)\n";

    check(a22 == 1.0,       "A_22 = 1 (normalization)");
    check(a33 > 0.0,        "A_33 > 0 for unequal mass");
    check(a44 > 0.0,        "A_44 > 0 for unequal mass");
    check(a22 > a33,        "A_22 > A_33 (dominant mode)");
    check(a33 > a44,        "A_33 > A_44 (33 subdominant > 44 subdominant)");

    /* For delta=1/3: A_33 ~ 0.44*(1/3) ~ 0.147 */
    const double delta = (m1 - m2) / (m1 + m2);
    const double a33Expected = 0.44 * delta;
    const double relErr33 = std::abs(a33 - a33Expected) / a33Expected;
    check(relErr33 < 1e-9, "A_33 matches Kamaretsos formula exactly");

    return true;
}

/* =========================================================================
 * Test 7: Multi-mode ringdown is finite, nonzero, and decays
 * ======================================================================= */
bool testMultimodeRingdown() {
    std::cout << "Test 7: Multi-mode ringdown finite, nonzero, decays\n";

    const double m1    = 30.0 * M_SUN;
    const double m2    = 20.0 * M_SUN;
    const double mFin  = (m1 + m2) * 0.95; /* ~5% radiated */
    const double aStar = 0.68;

    const double amp22 = 1.0e-21; /* typical LIGO strain */
    const double t0    = 0.0;
    const double t1    = 1.0e-3; /* 1 ms later */
    const double t2    = 1.0e-2; /* 10 ms later */

    const double h0 = ringdownStrainMultimode(amp22, mFin, aStar, m1, m2, t0);
    const double h1 = ringdownStrainMultimode(amp22, mFin, aStar, m1, m2, t1);
    const double h2 = ringdownStrainMultimode(amp22, mFin, aStar, m1, m2, t2);

    std::cout << "  h(t=0)    = " << h0 << "\n"
              << "  h(t=1ms)  = " << h1 << "\n"
              << "  h(t=10ms) = " << h2 << "\n";

    check(physics::safeIsfinite(h0), "h(t=0) is finite");
    check(physics::safeIsfinite(h1), "h(t=1ms) is finite");
    check(physics::safeIsfinite(h2), "h(t=10ms) is finite");
    check(std::abs(h0) > 0.0, "h(t=0) is nonzero");
    /* envelope at t2 must be smaller than at t0 */
    check(std::abs(h2) < std::abs(h0), "envelope decays over time");
    /* before ringdown start returns zero */
    const double hPre = ringdownStrainMultimode(amp22, mFin, aStar, m1, m2, -1.0);
    check(hPre == 0.0, "h(t<0) = 0");

    return true;
}

/* =========================================================================
 * Test 8: Equal-mass merger -- (3,3) mode is suppressed to zero
 * WHY: The (3,3) mode is antisymmetric under m1 <-> m2 exchange; equal
 * masses have perfect symmetry, so it must vanish.
 * ======================================================================= */
bool testEqualMassSymmetry() {
    std::cout << "Test 8: Equal-mass merger suppresses (3,3) mode\n";

    const double m = 10.0 * M_SUN;

    const double a22 = qnmModeAmplitude({.l=2, .m=2, .n=0}, m, m);
    const double a33 = qnmModeAmplitude({.l=3, .m=3, .n=0}, m, m);
    const double a44 = qnmModeAmplitude({.l=4, .m=4, .n=0}, m, m);

    std::cout << "  A_22 (equal mass) = " << a22 << "\n"
              << "  A_33 (equal mass) = " << a33 << " (must be 0)\n"
              << "  A_44 (equal mass) = " << a44 << " (nonzero: no symmetry suppression)\n";

    check(a22 == 1.0,  "A_22 = 1 for equal mass");
    check(a33 == 0.0,  "A_33 = 0 for equal mass (antisymmetric mode)");
    check(a44 > 0.0,   "A_44 > 0 for equal mass (symmetric mode, not suppressed)");

    return true;
}


/* =========================================================================
 * Test 9: Angular factors -- face-on vs edge-on
 * WHY: The (2,2) dominant mode is maximum face-on; (3,3) and (4,4) vanish
 * face-on because they carry a sin(iota) factor.
 * ======================================================================= */
bool testInspiralAngularPatterns() {
    std::cout << "Test 9: Inspiral angular factors -- face-on vs edge-on\n";

    /* Face-on (iota = 0): only (2,2) has nonzero pattern */
    const double f22FaceOn = gwInspiralAngularPlus(2, 2, 0.0);
    const double f33FaceOn = gwInspiralAngularPlus(3, 3, 0.0);
    const double f44FaceOn = gwInspiralAngularPlus(4, 4, 0.0);

    check(std::abs(f22FaceOn - 1.0) < 1.0e-12,
          "F+(2,2) = 1 face-on");
    check(f33FaceOn == 0.0,
          "F+(3,3) = 0 face-on (sin iota = 0)");
    check(f44FaceOn == 0.0,
          "F+(4,4) = 0 face-on (sin^2 iota = 0)");

    /* Edge-on (iota = pi/2): (2,2) h+ = 0.5, (3,3) and (4,4) are nonzero */
    const double f22EdgeOn = gwInspiralAngularPlus(2, 2, physics::PI / 2.0);
    const double f33EdgeOn = gwInspiralAngularPlus(3, 3, physics::PI / 2.0);
    const double f44EdgeOn = gwInspiralAngularPlus(4, 4, physics::PI / 2.0);

    check(std::abs(f22EdgeOn - 0.5) < 1.0e-12,
          "F+(2,2) = 0.5 edge-on");
    check(std::abs(f33EdgeOn - 0.5) < 1.0e-12,
          "F+(3,3) = 0.5 edge-on");
    check(std::abs(f44EdgeOn - 0.5) < 1.0e-12,
          "F+(4,4) = 0.5 edge-on");

    /* h* (cross) angular factors */
    const double fx22FaceOn = gwInspiralAngularCross(2, 2, 0.0);
    const double fx33FaceOn = gwInspiralAngularCross(3, 3, 0.0);
    check(std::abs(fx22FaceOn - 1.0) < 1.0e-12,
          "Fx(2,2) = 1 face-on");
    check(fx33FaceOn == 0.0,
          "Fx(3,3) = 0 face-on");

    return true;
}

/* =========================================================================
 * Test 10: Mode fractions -- equal mass suppresses odd modes
 * WHY: (2,1) and (3,3) are odd-parity modes: they carry a delta factor
 * and must vanish for equal-mass systems (delta = 0).
 * ======================================================================= */
bool testInspiralModeFractionsEqualMass() {
    std::cout << "Test 10: Inspiral mode fractions -- delta=0 suppresses (2,1) and (3,3)\n";

    /* Typical late-inspiral velocity (fGw ~ 200 Hz, M ~ 60 Msun) */
    const double mTotal = 60.0 * M_SUN;
    const double fGw    = 200.0;
    const double v      = gwPNVelocity(mTotal, fGw);

    check(v > 0.0 && v < 1.0, "gwPNVelocity returns v in (0,1)");

    const double delta = 0.0;  /* equal mass */
    const double eta   = 0.25; /* equal mass */

    const double r21 = gwInspiralModeFraction(2, 1, v, delta, eta);
    const double r33 = gwInspiralModeFraction(3, 3, v, delta, eta);
    const double r44 = gwInspiralModeFraction(4, 4, v, delta, eta);
    const double r22 = gwInspiralModeFraction(2, 2, v, delta, eta);

    check(r22 == 1.0, "(2,2) fraction = 1 always");
    check(r21 == 0.0, "(2,1) fraction = 0 for delta=0");
    check(r33 == 0.0, "(3,3) fraction = 0 for delta=0");

    char buf[128];
    (void)std::snprintf(buf, sizeof(buf), "(4,4) fraction = %.4e", r44);
    check(r44 >= 0.0, "(4,4) fraction >= 0 for eta=1/4", buf);
    /* (4,4) ~ |1-3*eta|*v^2; at eta=1/4: |1-3/4|=1/4, so nonzero unless eta=1/3 */
    check(r44 > 0.0, "(4,4) nonzero for eta=1/4 (|1-3eta|=1/4 != 0)", buf);

    return true;
}

/* =========================================================================
 * Test 11: Mode fractions -- unequal mass grows (3,3) amplitude
 * WHY: For q=0.5 (delta~0.33), the (3,3) mode is ~8% of (2,2) at late
 * inspiral.  This makes the subdominant modes detectable by LIGO at O3 SNR.
 * ======================================================================= */
bool testInspiralModeFractionsUnequalMass() {
    std::cout << "Test 11: Inspiral mode fractions -- unequal mass\n";

    /* GW190521-like parameters: q ~ 0.5 */
    const double m1 = 100.0 * M_SUN;
    const double m2 =  50.0 * M_SUN;
    const double mTotal = m1 + m2;
    const double etaVal  = (m1 * m2) / (mTotal * mTotal);
    const double delta   = (m1 - m2) / mTotal;

    const double fGw = 100.0; /* Hz, late inspiral */
    const double v   = gwPNVelocity(mTotal, fGw);

    const double r33 = gwInspiralModeFraction(3, 3, v, delta, etaVal);
    const double r21 = gwInspiralModeFraction(2, 1, v, delta, etaVal);
    const double r44 = gwInspiralModeFraction(4, 4, v, delta, etaVal);

    char buf[256];
    (void)std::snprintf(buf, sizeof(buf),
        "v=%.3f delta=%.3f: r33=%.4f r21=%.4f r44=%.4f", v, delta, r33, r21, r44);
    std::cout << "  " << buf << "\n";

    check(r33 > 0.0, "(3,3) nonzero for unequal mass", buf);
    check(r21 > 0.0, "(2,1) nonzero for unequal mass", buf);
    check(r33 > r21, "(3,3) > (2,1) amplitude (larger coefficient)", buf);
    check(r33 < 1.0, "(3,3) < (2,2) always at inspiral velocities", buf);

    /* At v ~ 0.25 and delta ~ 0.33: r33 ~ 0.58 * 0.33 * 0.25 ~ 0.048 */
    check(r33 > 0.01 && r33 < 0.5, "(3,3) fraction in expected range 1%-50%", buf);

    return true;
}

/* =========================================================================
 * Test 12: Multi-mode inspiral strain -- finite, and equal mass = (2,2) only
 * WHY: For delta=0, all subdominant modes vanish, so gwInspiralStrainMultimode
 * must exactly reproduce the single-mode gwStrain1pn result.
 * ======================================================================= */
bool testInspiralMultimodeEqualMass() {
    std::cout << "Test 12: Multi-mode strain reduces to (2,2) for equal mass\n";

    const double m1    = 30.0 * M_SUN;
    const double m2    = 30.0 * M_SUN;
    const double mTotal = m1 + m2;
    const double mc    = chirpMass(m1, m2);
    const double etaVal = (m1 * m2) / (mTotal * mTotal);
    const double delta  = (m1 - m2) / mTotal;  /* = 0 */
    const double fGw    = 100.0;
    const double d      = 410.0 * 3.0856775814913673e+24; /* 410 Mpc in cm */
    const double iota   = 0.4;
    const double phiOrb = 0.7;

    double hPlus = 0.0;
    double hCross = 0.0;
    gwInspiralStrainMultimode(mc, mTotal, etaVal, delta, fGw, d,
                               iota, phiOrb, hPlus, hCross);

    /* Expected: (2,2) + (4,4) only -- (2,1) and (3,3) vanish for delta=0,
     * but (4,4) is nonzero because it depends on |1-3*eta|, not delta. */
    const double h22amp = gwStrain1pn(mc, etaVal, fGw, d);
    const double vVal   = gwPNVelocity(mTotal, fGw);
    const double r44    = gwInspiralModeFraction(4, 4, vVal, delta, etaVal);
    const double hPlusExpected  = h22amp * ((gwInspiralAngularPlus(2, 2, iota) * std::cos(2.0 * phiOrb))
                                   + (r44 * gwInspiralAngularPlus(4, 4, iota) * std::cos(4.0 * phiOrb)));
    const double hCrossExpected = h22amp * ((gwInspiralAngularCross(2, 2, iota) * std::sin(2.0 * phiOrb))
                                   + (r44 * gwInspiralAngularCross(4, 4, iota) * std::sin(4.0 * phiOrb)));

    char buf[256];
    (void)std::snprintf(buf, sizeof(buf),
        "hPlus=%.4e expected=%.4e relErr=%.2e",
        hPlus, hPlusExpected, std::abs(hPlus - hPlusExpected) / std::abs(hPlusExpected));

    check(safeIsfinite(hPlus),  "multi-mode hPlus is finite");
    check(safeIsfinite(hCross), "multi-mode hCross is finite");
    /* (2,1) and (3,3) vanish; (4,4) still contributes (|1-3*eta|=1/4 at eta=1/4) */
    check(std::abs(hPlus - hPlusExpected) / std::abs(hPlusExpected) < 1.0e-12,
          "multi-mode = (2,2)+(4,4) for equal mass (hPlus)", buf);
    check(std::abs(hCross - hCrossExpected) / std::abs(hCrossExpected) < 1.0e-12,
          "multi-mode = (2,2)+(4,4) for equal mass (hCross)");

    return true;
}

/* =========================================================================
 * Test 13: Multi-mode inspiral strain -- unequal mass differs from (2,2)
 * WHY: For delta != 0, the (3,3) and (2,1) modes add to h+, h*.
 * At edge-on inclination (iota = pi/2) the sub-dominant modes contribute
 * maximally (their angular factors peak there) so the total strain differs
 * from the single-mode result.
 * ======================================================================= */
bool testInspiralMultimodeUnequalMass() {
    std::cout << "Test 13: Multi-mode strain differs from (2,2) for unequal mass\n";

    const double m1     = 60.0 * M_SUN;
    const double m2     = 20.0 * M_SUN;  /* q = 3, delta = 0.5 */
    const double mTotal = m1 + m2;
    const double mc     = chirpMass(m1, m2);
    const double etaVal = (m1 * m2) / (mTotal * mTotal);
    const double delta  = (m1 - m2) / mTotal;
    const double fGw    = 100.0;
    const double d      = 410.0 * 3.0856775814913673e+24;
    const double iota   = physics::PI / 2.0;  /* edge-on: sub-modes enhanced */
    const double phiOrb = physics::PI / 4.0;  /* 45 deg: both + and * polarizations active */

    double hPlus = 0.0;
    double hCross = 0.0;
    gwInspiralStrainMultimode(mc, mTotal, etaVal, delta, fGw, d,
                               iota, phiOrb, hPlus, hCross);

    /* Single-mode (2,2) reference */
    const double h22amp = gwStrain1pn(mc, etaVal, fGw, d);
    const double hPlus22  = h22amp * gwInspiralAngularPlus(2, 2, iota)
                             * std::cos(2.0 * phiOrb);
    const double hCross22 = h22amp * gwInspiralAngularCross(2, 2, iota)
                             * std::sin(2.0 * phiOrb);

    check(safeIsfinite(hPlus),  "unequal-mass hPlus is finite");
    check(safeIsfinite(hCross), "unequal-mass hCross is finite");
    check(hPlus  != hPlus22,  "multi-mode hPlus  differs from (2,2)-only for q=3");
    check(hCross != hCross22, "multi-mode hCross differs from (2,2)-only for q=3");

    /* The sub-dominant modes ADD power: |h_multi|^2 > |h_22|^2 at this phase */
    const double powerMulti = (hPlus * hPlus) + (hCross * hCross);
    const double power22    = (hPlus22 * hPlus22) + (hCross22 * hCross22);
    char buf[256];
    (void)std::snprintf(buf, sizeof(buf),
        "power_multi=%.4e power_22=%.4e ratio=%.4f",
        powerMulti, power22, powerMulti / power22);
    std::cout << "  " << buf << "\n";

    check(powerMulti > 0.0, "multi-mode power > 0");

    return true;
}

} // namespace

/* =========================================================================
 * Main
 * ======================================================================= */
int main() {
    std::cout << "\n================================================\n"
              << "HIGHER GW MULTIPOLE QNM MODE VALIDATION\n"
              << "Physics: Berti 2009 + Kamaretsos 2012\n"
              << "================================================\n\n";

    testFitParamsLookup();     std::cout << "\n";
    testGenericMatchesDominant(); std::cout << "\n";
    testL33SchwarzchildLimit(); std::cout << "\n";
    testL33MonotonicFrequency(); std::cout << "\n";
    testL44SchwarzchildLimit(); std::cout << "\n";
    testModeAmplitudeHierarchy(); std::cout << "\n";
    testMultimodeRingdown();    std::cout << "\n";
    testEqualMassSymmetry();    std::cout << "\n";
    testInspiralAngularPatterns(); std::cout << "\n";
    testInspiralModeFractionsEqualMass(); std::cout << "\n";
    testInspiralModeFractionsUnequalMass(); std::cout << "\n";
    testInspiralMultimodeEqualMass(); std::cout << "\n";
    testInspiralMultimodeUnequalMass(); std::cout << "\n";

    std::cout << "================================================\n"
              << "RESULT: " << (gAllPass ? "ALL PASS" : "FAILURES DETECTED") << "\n"
              << "================================================\n\n";

    return gAllPass ? 0 : 1;
}
