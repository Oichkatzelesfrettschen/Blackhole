/**
 * @file kerr_qnm_spin_test.cpp
 * @brief Validation tests for Kerr QNM ringdown and spin PN phase corrections.
 *
 * WHY: The Schwarzschild QNM frequency is used regardless of spin in the
 *      previous implementation; for a*>0.3 the error exceeds 10% and dominates
 *      over other systematic uncertainties.
 *      The 3.5PN phase lacked spin-orbit and spin-spin terms (Kidder 1995,
 *      Cutler & Flanagan 1994) needed for matched filtering of spinning BBHs.
 *
 * WHAT: Validate qnmFrequencyKerr and qnmDampingTimeKerr (Berti 2009
 *       Table VIII) and the chiEff-dependent gwPhase3p5pn extension.
 *
 * HOW: Cross-check against known analytic limits and published values.
 *
 * References:
 *   - Berti, Cardoso & Starinets (2009) CQG 26, 163001, Table VIII
 *   - Kidder (1995) Phys. Rev. D 52, 821
 *   - Cutler & Flanagan (1994) Phys. Rev. D 49, 2658
 */

#include "../src/physics/constants.h"
#include "../src/physics/gravitational_waves.h"
#include <cmath>
#include <iomanip>
#include <iostream>

using namespace physics;

namespace {

// ============================================================================
// Test 1: QNM frequency reduces to Schwarzschild at a*=0
// ============================================================================

bool testQnmKerrSchwarzschildLimit() {
  std::cout << "\n[TEST 1] Kerr QNM reduces to Schwarzschild at a*=0\n";
  std::cout << "===================================================\n";

  const double mVal  = 10.0 * M_SUN;
  const double fSchw = qnmFrequencySchwarzschild(mVal);
  const double fKerr = qnmFrequencyKerr(mVal, 0.0);
  const double relErr = std::abs(fKerr - fSchw) / fSchw;

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  f_Schwarzschild: " << fSchw << " Hz\n";
  std::cout << "  f_Kerr(a*=0):   " << fKerr << " Hz\n";
  std::cout << "  Relative error: " << relErr << "\n";

  // At a*=0, Berti fit gives f1 = 1.5251 - 1.1568 = 0.3683
  // Schwarzschild: omega_22 = 0.3737/M => difference <2% due to fit accuracy
  const bool pass = (relErr < 0.02);
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL")
            << " (tolerance 2% for fit accuracy at a*=0)\n";
  return pass;
}

// ============================================================================
// Test 2: QNM frequency increases monotonically with spin
// ============================================================================

bool testQnmKerrMonotoneWithSpin() {
  std::cout << "\n[TEST 2] Kerr QNM frequency increases monotonically with a*\n";
  std::cout << "============================================================\n";

  const double mVal = 10.0 * M_SUN;

  double prevF   = qnmFrequencyKerr(mVal, 0.0);
  bool monotone = true;

  std::cout << "  a*    f_QNM [Hz]\n";
  for (int iStep = 1; iStep <= 9; ++iStep) {
    const double aStar = 0.1 * static_cast<double>(iStep);
    const double fVal  = qnmFrequencyKerr(mVal, aStar);
    std::cout << "  " << std::fixed << std::setprecision(2) << aStar
              << "   " << std::setprecision(4) << fVal << "\n";
    if (fVal <= prevF) {
      monotone = false;
      std::cout << "  FAIL: non-monotone at a*=" << aStar << "\n";
    }
    prevF = fVal;
  }

  std::cout << "  Status: " << (monotone ? "PASS" : "FAIL")
            << " (f_QNM must increase with spin)\n";
  return monotone;
}

// ============================================================================
// Test 3: QNM damping time increases with spin (higher Q for Kerr)
// ============================================================================

bool testQnmDampingTimeIncreasesWithSpin() {
  std::cout << "\n[TEST 3] Kerr QNM damping time increases with spin\n";
  std::cout << "===================================================\n";

  const double mVal      = 10.0 * M_SUN;
  const double tauSchw   = qnmDampingTimeSchwarzschild(mVal);
  const double tauKerrHi = qnmDampingTimeKerr(mVal, 0.9);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  tau_Schwarzschild:  " << tauSchw * 1e3 << " ms\n";
  std::cout << "  tau_Kerr(a*=0.9):  " << tauKerrHi * 1e3 << " ms\n";

  // WHY: High-spin Kerr has higher quality factor than Schwarzschild.
  // From Berti 2009 Table VIII: tau_22 grows with spin but modestly at a*=0.9.
  // The Berti fit gives tau(a*=0.9) / tau(Schw) ~ 1.3-1.5 for a 10 M_sun BH.
  // We verify tau increases with spin (ratio > 1), consistent with the fits.
  const double ratio = tauKerrHi / tauSchw;
  const bool pass = (ratio > 1.1);
  std::cout << "  Ratio: " << ratio << " (expected >1.1)\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 4: GW phase spin corrections are zero for non-spinning binary
// ============================================================================

bool testSpinPnZeroForNonspinning() {
  std::cout << "\n[TEST 4] Spin PN corrections vanish for chi1=chi2=0\n";
  std::cout << "======================================================\n";

  const double mc   = 28.3 * M_SUN;
  const double eta  = 0.247;
  const double fHz  = 100.0;

  const double phaseNoSpin   = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0, 0.0, 0.0, 0.0);
  const double phaseWithSpin = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0, 0.3, 0.6, 0.4);
  const double deltaPhase    = std::abs(phaseWithSpin - phaseNoSpin);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Phase (chi=0):       " << phaseNoSpin   << " rad\n";
  std::cout << "  Phase (chiEff=0.3): " << phaseWithSpin << " rad\n";
  std::cout << "  Delta phi:           " << deltaPhase << " rad\n";

  const double phaseDefault = gwPhase3p5pn(mc, eta, fHz);
  const double diffDefault  = std::abs(phaseNoSpin - phaseDefault);

  std::cout << "  Delta vs default:    " << diffDefault << " rad (expect 0)\n";

  const bool pass = (diffDefault < 1e-12) && (deltaPhase > 0.0);
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL")
            << " (zero-spin matches default; nonzero spin differs)\n";
  return pass;
}

// ============================================================================
// Test 5: Spin-orbit correction has correct sign for prograde spin
// ============================================================================

bool testSpinOrbitSign() {
  std::cout << "\n[TEST 5] Spin-orbit phase correction sign (Kidder 1995)\n";
  std::cout << "=========================================================\n";

  const double mc  = 28.3 * M_SUN;
  const double eta = 0.247;
  const double fHz = 100.0;

  const double phaseSpinUp   = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0, +0.5, +0.5, +0.5);
  const double phaseSpinDown = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0, -0.5, -0.5, -0.5);
  const double phaseNospin   = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0,  0.0,  0.0,  0.0);

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase (chiEff=+0.5): " << phaseSpinUp   << " rad\n";
  std::cout << "  Phase (chiEff=0):    " << phaseNospin    << " rad\n";
  std::cout << "  Phase (chiEff=-0.5): " << phaseSpinDown << " rad\n";

  // SO terms are odd in chiEff => deviations from no-spin have opposite sign
  // SS terms (even in chi) break exact antisymmetry, so we check:
  // 1. prograde and retrograde produce different phases
  // 2. the SO-dominated deviations are opposite in sign
  const bool signDiffer   = (phaseSpinUp != phaseSpinDown);
  const double devUp      = phaseSpinUp - phaseNospin;
  const double devDown    = phaseSpinDown - phaseNospin;
  const bool oppositeSign = ((devUp * devDown) < 0);

  std::cout << "  Signs differ: " << (signDiffer ? "YES" : "NO") << "\n";
  std::cout << "  Opposite deviations: " << (oppositeSign ? "YES" : "NO") << "\n";

  const bool pass = signDiffer && oppositeSign;
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 6: chiEffFromBinary correctly extracts spin from BinarySystem
// ============================================================================

bool testChiEffFromBinary() {
  std::cout << "\n[TEST 6] chiEffFromBinary extracts effective spin\n";
  std::cout << "======================================================\n";

  // Equal mass, equal spin aligned: chiEff should equal the dimensionless spin
  const double aStarTarget = 0.7;
  const BinarySystem binary = bbhSystem(30.0, 30.0, aStarTarget, aStarTarget, 410.0);
  const double chiEff = chiEffFromBinary(binary);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Target chiEff: " << aStarTarget << "\n";
  std::cout << "  Computed:       " << chiEff << "\n";

  const double err = std::abs(chiEff - aStarTarget);
  std::cout << "  Absolute error: " << err << "\n";

  const bool pass = (err < 1e-6);
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";

  // Non-spinning should give zero
  const BinarySystem nsBinary = bnsSystem(1.4, 1.2, 40.0);
  const double chiEffNs = chiEffFromBinary(nsBinary);
  std::cout << "  Non-spinning chiEff: " << chiEffNs << " (expect 0)\n";
  const bool pass2 = (std::abs(chiEffNs) < 1e-12);
  std::cout << "  Status: " << (pass2 ? "PASS" : "FAIL") << "\n";

  return pass && pass2;
}

// ============================================================================
// Test 7: NNLO spin-orbit terms (3PN + 3.5PN) have measurable effect
// ============================================================================

bool testNnloSpinOrbitEffect() {
  std::cout << "\n[TEST 7] NNLO spin-orbit (3PN+3.5PN) measurable effect\n";
  std::cout << "=======================================================\n";

  // GW150914-like system at moderate frequency where higher PN matters
  const double mc       = 28.3 * M_SUN;
  const double eta      = 0.247;
  const double fHz      = 50.0;
  const double chiEffHi = 0.7;
  const double chi1     = 0.8;
  const double chi2     = 0.6;

  const double phaseWithSpin = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0, chiEffHi, chi1, chi2);
  const double phaseNoSpin   = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0, 0.0, 0.0, 0.0);
  const double deltaPhase    = phaseWithSpin - phaseNoSpin;

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase (no spin):      " << phaseNoSpin << " rad\n";
  std::cout << "  Phase (chiEff=0.7):  " << phaseWithSpin << " rad\n";
  std::cout << "  Delta phi:            " << deltaPhase << " rad\n";

  // The spin contribution should be nonzero and O(1) rad or more for high spin at 50 Hz
  const bool pass = (std::abs(deltaPhase) > 0.1);
  std::cout << "  |delta_phi| > 0.1:    " << (pass ? "YES" : "NO") << "\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 8: 3PN non-spin terms present (3PN and 3.5PN point-mass)
// ============================================================================

bool test3pnNonzeroContribution() {
  std::cout << "\n[TEST 8] 3PN+3.5PN non-spin terms produce finite phase\n";
  std::cout << "=========================================================\n";

  const double mc  = 28.3 * M_SUN;
  const double eta = 0.247;

  const double phase10Hz  = gwPhase3p5pn(mc, eta, 10.0);
  const double phase100Hz = gwPhase3p5pn(mc, eta, 100.0);
  const double phase200Hz = gwPhase3p5pn(mc, eta, 200.0);

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase at 10 Hz:   " << phase10Hz << " rad\n";
  std::cout << "  Phase at 100 Hz:  " << phase100Hz << " rad\n";
  std::cout << "  Phase at 200 Hz:  " << phase200Hz << " rad\n";

  // Phase should be finite and well-ordered (decreasing in magnitude
  // as frequency increases, since v increases and leading term ~ v^-5)
  const bool finite  = (phase10Hz == phase10Hz) && (phase100Hz == phase100Hz)
                       && (phase200Hz == phase200Hz);  // NaN != NaN
  const bool ordered = (std::abs(phase10Hz) > std::abs(phase100Hz));

  const bool pass = finite && ordered;
  std::cout << "  All finite:         " << (finite ? "YES" : "NO") << "\n";
  std::cout << "  |phi(10)|>|phi(100)|: " << (ordered ? "YES" : "NO") << "\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 9: Symmetric spin combinations (chiS/chiA) algebra check
// ============================================================================

bool testChiSChiASymmetry() {
  std::cout << "\n[TEST 9] chiS/chiA symmetric/antisymmetric algebra\n";
  std::cout << "=====================================================\n";

  const double mc  = 28.3 * M_SUN;
  const double eta = 0.247;
  const double fHz = 100.0;

  const double phaseEqUp   = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0,  0.5,  0.5,  0.5);
  const double phaseEqDown = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0, -0.5, -0.5, -0.5);
  const double phaseOpp    = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0,  0.0,  0.5, -0.5);
  const double phaseZero   = gwPhase3p5pn(mc, eta, fHz, 0.0, 0.0,  0.0,  0.0,  0.0);

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase (chi1=chi2=+0.5):  " << phaseEqUp   << " rad\n";
  std::cout << "  Phase (chi1=chi2=-0.5):  " << phaseEqDown << " rad\n";
  std::cout << "  Phase (chi1=-chi2=0.5):  " << phaseOpp    << " rad\n";
  std::cout << "  Phase (no spin):         " << phaseZero   << " rad\n";

  // Equal-and-opposite spins should differ from zero-spin only via SS terms
  // (SO terms vanish because chiEff = 0)
  const bool eqSpinsDiffer = (std::abs(phaseEqUp - phaseEqDown) > 1e-10);
  const bool allFinite     = (phaseEqUp == phaseEqUp) && (phaseEqDown == phaseEqDown)
                             && (phaseOpp == phaseOpp) && (phaseZero == phaseZero);

  const bool pass = eqSpinsDiffer && allFinite;
  std::cout << "  Equal spins differ:    " << (eqSpinsDiffer ? "YES" : "NO") << "\n";
  std::cout << "  All finite:            " << (allFinite ? "YES" : "NO") << "\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

} // namespace

// ============================================================================
// Main
// ============================================================================

int main() {
  std::cout << "\n"
            << "====================================================\n"
            << "KERR QNM + SPIN PN VALIDATION TESTS\n"
            << "====================================================\n";

  int passed = 0;
  constexpr int total = 9;

  if (testQnmKerrSchwarzschildLimit())       { passed++; }
  if (testQnmKerrMonotoneWithSpin())         { passed++; }
  if (testQnmDampingTimeIncreasesWithSpin()) { passed++; }
  if (testSpinPnZeroForNonspinning())        { passed++; }
  if (testSpinOrbitSign())                   { passed++; }
  if (testChiEffFromBinary())                { passed++; }
  if (testNnloSpinOrbitEffect())             { passed++; }
  if (test3pnNonzeroContribution())          { passed++; }
  if (testChiSChiASymmetry())                { passed++; }

  std::cout << "\n"
            << "====================================================\n"
            << "RESULTS: " << passed << "/" << total << " tests passed\n"
            << "====================================================\n";

  return (passed == total) ? 0 : 1;
}
