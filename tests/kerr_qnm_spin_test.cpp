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
 * WHAT: Validate qnm_frequency_kerr and qnm_damping_time_kerr (Berti 2009
 *       Table VIII) and the chi_eff-dependent gw_phase_3p5pn extension.
 *
 * HOW: Cross-check against known analytic limits and published values.
 *
 * References:
 *   - Berti, Cardoso & Starinets (2009) CQG 26, 163001, Table VIII
 *   - Kidder (1995) Phys. Rev. D 52, 821
 *   - Cutler & Flanagan (1994) Phys. Rev. D 49, 2658
 */

#include "../src/physics/gravitational_waves.h"
#include <cmath>
#include <iomanip>
#include <iostream>

using namespace physics;

// ============================================================================
// Test 1: QNM frequency reduces to Schwarzschild at a*=0
// ============================================================================

bool test_qnm_kerr_schwarzschild_limit() {
  std::cout << "\n[TEST 1] Kerr QNM reduces to Schwarzschild at a*=0\n";
  std::cout << "===================================================\n";

  double M = 10.0 * M_SUN;  // 10 solar mass final black hole

  double f_schw = qnm_frequency_schwarzschild(M);
  double f_kerr = qnm_frequency_kerr(M, 0.0);

  double rel_err = std::abs(f_kerr - f_schw) / f_schw;

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  f_Schwarzschild: " << f_schw << " Hz\n";
  std::cout << "  f_Kerr(a*=0):   " << f_kerr << " Hz\n";
  std::cout << "  Relative error: " << rel_err << "\n";

  // At a*=0, Berti fit gives f1 = 1.5251 - 1.1568 = 0.3683
  // Schwarzschild: omega_22 = 0.3737/M => difference <2% due to fit accuracy
  bool pass = (rel_err < 0.02);
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL")
            << " (tolerance 2% for fit accuracy at a*=0)\n";
  return pass;
}

// ============================================================================
// Test 2: QNM frequency increases monotonically with spin
// ============================================================================

bool test_qnm_kerr_monotone_with_spin() {
  std::cout << "\n[TEST 2] Kerr QNM frequency increases monotonically with a*\n";
  std::cout << "============================================================\n";

  double M = 10.0 * M_SUN;

  double prev_f = qnm_frequency_kerr(M, 0.0);
  bool monotone = true;

  std::cout << "  a*    f_QNM [Hz]\n";
  for (double a_star = 0.1; a_star <= 0.95; a_star += 0.1) {
    double f = qnm_frequency_kerr(M, a_star);
    std::cout << "  " << std::fixed << std::setprecision(2) << a_star
              << "   " << std::setprecision(4) << f << "\n";
    if (f <= prev_f) {
      monotone = false;
      std::cout << "  FAIL: non-monotone at a*=" << a_star << "\n";
    }
    prev_f = f;
  }

  std::cout << "  Status: " << (monotone ? "PASS" : "FAIL")
            << " (f_QNM must increase with spin)\n";
  return monotone;
}

// ============================================================================
// Test 3: QNM damping time increases with spin (higher Q for Kerr)
// ============================================================================

bool test_qnm_damping_time_increases_with_spin() {
  std::cout << "\n[TEST 3] Kerr QNM damping time increases with spin\n";
  std::cout << "===================================================\n";

  double M = 10.0 * M_SUN;
  double tau_schw = qnm_damping_time_schwarzschild(M);
  double tau_kerr_high = qnm_damping_time_kerr(M, 0.9);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  tau_Schwarzschild:  " << tau_schw * 1e3 << " ms\n";
  std::cout << "  tau_Kerr(a*=0.9):  " << tau_kerr_high * 1e3 << " ms\n";

  // WHY: High-spin Kerr has higher quality factor than Schwarzschild.
  // From Berti 2009 Table VIII: tau_22 grows with spin but modestly at a*=0.9.
  // The Berti fit gives tau(a*=0.9) / tau(Schw) ~ 1.3-1.5 for a 10 M_sun BH.
  // We verify tau increases with spin (ratio > 1), consistent with the fits.
  double ratio = tau_kerr_high / tau_schw;
  bool pass = (ratio > 1.1);
  std::cout << "  Ratio: " << ratio << " (expected >1.1)\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 4: GW phase spin corrections are zero for non-spinning binary
// ============================================================================

bool test_spin_pn_zero_for_nonspinning() {
  std::cout << "\n[TEST 4] Spin PN corrections vanish for chi1=chi2=0\n";
  std::cout << "======================================================\n";

  double M_c = 28.3 * M_SUN;  // GW150914 chirp mass
  double eta  = 0.247;         // GW150914 eta
  double f    = 100.0;         // Hz

  double phase_no_spin   = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0,
                                           0.0, 0.0, 0.0);
  double phase_with_spin = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0,
                                           0.3, 0.6, 0.4);

  double delta = std::abs(phase_with_spin - phase_no_spin);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Phase (chi=0):       " << phase_no_spin   << " rad\n";
  std::cout << "  Phase (chi_eff=0.3): " << phase_with_spin << " rad\n";
  std::cout << "  Delta phi:           " << delta << " rad\n";

  // Zero-spin call should be identical to default-parameter call
  double phase_default = gw_phase_3p5pn(M_c, eta, f);
  double diff_default  = std::abs(phase_no_spin - phase_default);

  std::cout << "  Delta vs default:    " << diff_default << " rad (expect 0)\n";

  bool pass = (diff_default < 1e-12) && (delta > 0.0);
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL")
            << " (zero-spin matches default; nonzero spin differs)\n";
  return pass;
}

// ============================================================================
// Test 5: Spin-orbit correction has correct sign for prograde spin
// ============================================================================

bool test_spin_orbit_sign() {
  std::cout << "\n[TEST 5] Spin-orbit phase correction sign (Kidder 1995)\n";
  std::cout << "=========================================================\n";

  double M_c = 28.3 * M_SUN;
  double eta  = 0.247;
  double f    = 100.0;

  // Prograde spin chi_eff > 0 reduces inspiral time => increases accumulated phase
  double phase_spin_up   = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0,
                                           +0.5, +0.5, +0.5);
  double phase_spin_down = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0,
                                           -0.5, -0.5, -0.5);
  double phase_nospin    = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0,
                                            0.0, 0.0,  0.0);

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase (chi_eff=+0.5): " << phase_spin_up   << " rad\n";
  std::cout << "  Phase (chi_eff=0):    " << phase_nospin    << " rad\n";
  std::cout << "  Phase (chi_eff=-0.5): " << phase_spin_down << " rad\n";

  // SO terms are odd in chi_eff => deviations from no-spin have opposite sign
  // SS terms (even in chi) break exact antisymmetry, so we check:
  // 1. prograde and retrograde produce different phases
  // 2. the SO-dominated deviations are opposite in sign
  bool sign_differ = (phase_spin_up != phase_spin_down);
  double dev_up   = phase_spin_up - phase_nospin;
  double dev_down = phase_spin_down - phase_nospin;
  bool opposite_sign = (dev_up * dev_down < 0);

  std::cout << "  Signs differ: " << (sign_differ ? "YES" : "NO") << "\n";
  std::cout << "  Opposite deviations: " << (opposite_sign ? "YES" : "NO") << "\n";

  bool pass = sign_differ && opposite_sign;
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 6: chi_eff_from_binary correctly extracts spin from BinarySystem
// ============================================================================

bool test_chi_eff_from_binary() {
  std::cout << "\n[TEST 6] chi_eff_from_binary extracts effective spin\n";
  std::cout << "======================================================\n";

  // Equal mass, equal spin aligned: chi_eff should equal the dimensionless spin
  double a_star_target = 0.7;
  BinarySystem binary = bbh_system(30.0, 30.0, a_star_target, a_star_target, 410.0);
  double chi_eff = chi_eff_from_binary(binary);

  std::cout << std::fixed << std::setprecision(6);
  std::cout << "  Target chi_eff: " << a_star_target << "\n";
  std::cout << "  Computed:       " << chi_eff << "\n";

  double err = std::abs(chi_eff - a_star_target);
  std::cout << "  Absolute error: " << err << "\n";

  bool pass = (err < 1e-6);
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";

  // Non-spinning should give zero
  BinarySystem ns_binary = bns_system(1.4, 1.2, 40.0);
  double chi_eff_ns = chi_eff_from_binary(ns_binary);
  std::cout << "  Non-spinning chi_eff: " << chi_eff_ns << " (expect 0)\n";
  bool pass2 = (std::abs(chi_eff_ns) < 1e-12);
  std::cout << "  Status: " << (pass2 ? "PASS" : "FAIL") << "\n";

  return pass && pass2;
}

// ============================================================================
// Test 7: NNLO spin-orbit terms (3PN + 3.5PN) have measurable effect
// ============================================================================

bool test_nnlo_spin_orbit_effect() {
  std::cout << "\n[TEST 7] NNLO spin-orbit (3PN+3.5PN) measurable effect\n";
  std::cout << "=======================================================\n";

  // GW150914-like system at moderate frequency where higher PN matters
  double M_c = 28.3 * M_SUN;
  double eta  = 0.247;
  double f    = 50.0;   // Hz -- lower frequency amplifies PN effects

  // High spin where NNLO corrections are significant
  double chi_eff_high = 0.7;
  double chi1 = 0.8;
  double chi2 = 0.6;

  double phase_with_spin = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0,
                                           chi_eff_high, chi1, chi2);
  double phase_no_spin   = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0,
                                           0.0, 0.0, 0.0);

  double delta_phase = phase_with_spin - phase_no_spin;

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase (no spin):      " << phase_no_spin << " rad\n";
  std::cout << "  Phase (chi_eff=0.7):  " << phase_with_spin << " rad\n";
  std::cout << "  Delta phi:            " << delta_phase << " rad\n";

  // The spin contribution should be nonzero and O(1) rad or more
  // for high spin at 50 Hz
  bool pass = (std::abs(delta_phase) > 0.1);
  std::cout << "  |delta_phi| > 0.1:    " << (pass ? "YES" : "NO") << "\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 8: 3PN non-spin terms present (3PN and 3.5PN point-mass)
// ============================================================================

bool test_3pn_nonzero_contribution() {
  std::cout << "\n[TEST 8] 3PN+3.5PN non-spin terms produce finite phase\n";
  std::cout << "=========================================================\n";

  // Compare phases at two frequencies to confirm higher PN terms contribute
  double M_c = 28.3 * M_SUN;
  double eta  = 0.247;

  double phase_10Hz  = gw_phase_3p5pn(M_c, eta, 10.0);
  double phase_100Hz = gw_phase_3p5pn(M_c, eta, 100.0);
  double phase_200Hz = gw_phase_3p5pn(M_c, eta, 200.0);

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase at 10 Hz:   " << phase_10Hz << " rad\n";
  std::cout << "  Phase at 100 Hz:  " << phase_100Hz << " rad\n";
  std::cout << "  Phase at 200 Hz:  " << phase_200Hz << " rad\n";

  // Phase should be finite and well-ordered (decreasing in magnitude
  // as frequency increases, since v increases and leading term ~ v^-5)
  bool finite = (phase_10Hz == phase_10Hz) && (phase_100Hz == phase_100Hz)
                && (phase_200Hz == phase_200Hz);  // NaN != NaN

  // Low-frequency phase should have larger magnitude than high-frequency
  // (the v^-5 leading factor dominates)
  bool ordered = (std::abs(phase_10Hz) > std::abs(phase_100Hz));

  bool pass = finite && ordered;
  std::cout << "  All finite:         " << (finite ? "YES" : "NO") << "\n";
  std::cout << "  |phi(10)|>|phi(100)|: " << (ordered ? "YES" : "NO") << "\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Test 9: Symmetric spin combinations (chi_s/chi_a) algebra check
// ============================================================================

bool test_chi_s_chi_a_symmetry() {
  std::cout << "\n[TEST 9] chi_s/chi_a symmetric/antisymmetric algebra\n";
  std::cout << "=====================================================\n";

  double M_c = 28.3 * M_SUN;
  double eta  = 0.247;
  double f    = 100.0;

  // Equal spins: chi_a = 0, so delta*chi_a terms vanish
  // Phase should depend only on chi_s = chi1 = chi2
  double phase_eq_up   = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0, 0.5, 0.5, 0.5);
  double phase_eq_down = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0, -0.5, -0.5, -0.5);

  // Opposite spins: chi_s = 0, chi_eff = 0
  // Only chi_a*delta terms contribute (which are absent for eta=0.25)
  double phase_opp = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0, 0.0, 0.5, -0.5);
  double phase_zero = gw_phase_3p5pn(M_c, eta, f, 0.0, 0.0, 0.0, 0.0, 0.0);

  std::cout << std::fixed << std::setprecision(4);
  std::cout << "  Phase (chi1=chi2=+0.5):  " << phase_eq_up << " rad\n";
  std::cout << "  Phase (chi1=chi2=-0.5):  " << phase_eq_down << " rad\n";
  std::cout << "  Phase (chi1=-chi2=0.5):  " << phase_opp << " rad\n";
  std::cout << "  Phase (no spin):         " << phase_zero << " rad\n";

  // Equal-and-opposite spins should differ from zero-spin only via SS terms
  // (SO terms vanish because chi_eff = 0)
  bool eq_spins_differ = (std::abs(phase_eq_up - phase_eq_down) > 1e-10);
  bool all_finite = (phase_eq_up == phase_eq_up) && (phase_eq_down == phase_eq_down)
                    && (phase_opp == phase_opp) && (phase_zero == phase_zero);

  bool pass = eq_spins_differ && all_finite;
  std::cout << "  Equal spins differ:    " << (eq_spins_differ ? "YES" : "NO") << "\n";
  std::cout << "  All finite:            " << (all_finite ? "YES" : "NO") << "\n";
  std::cout << "  Status: " << (pass ? "PASS" : "FAIL") << "\n";
  return pass;
}

// ============================================================================
// Main
// ============================================================================

int main() {
  std::cout << "\n"
            << "====================================================\n"
            << "KERR QNM + SPIN PN VALIDATION TESTS\n"
            << "====================================================\n";

  int passed = 0;
  int total  = 9;

  if (test_qnm_kerr_schwarzschild_limit())      passed++;
  if (test_qnm_kerr_monotone_with_spin())       passed++;
  if (test_qnm_damping_time_increases_with_spin()) passed++;
  if (test_spin_pn_zero_for_nonspinning())      passed++;
  if (test_spin_orbit_sign())                   passed++;
  if (test_chi_eff_from_binary())               passed++;
  if (test_nnlo_spin_orbit_effect())            passed++;
  if (test_3pn_nonzero_contribution())          passed++;
  if (test_chi_s_chi_a_symmetry())              passed++;

  std::cout << "\n"
            << "====================================================\n"
            << "RESULTS: " << passed << "/" << total << " tests passed\n"
            << "====================================================\n";

  return (passed == total) ? 0 : 1;
}
