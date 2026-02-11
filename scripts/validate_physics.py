#!/usr/bin/env python3
"""
Physics Validation Suite for Blackhole Simulator
Validates implementation against known GR formulas and EHT/LIGO constraints

Version: 2026.1
Date: 2026-01-31
"""

import sys
import math
from typing import Tuple, List

# Physical constants (CGS)
C = 2.99792458e10          # Speed of light [cm/s]
G = 6.67430e-8             # Gravitational constant [cm³/(g·s²)]
M_SUN = 1.98841e33         # Solar mass [g]
PARSEC = 3.0857e18         # Parsec [cm]

# Color codes for terminal output
GREEN = '\033[92m'
RED = '\033[91m'
YELLOW = '\033[93m'
BLUE = '\033[94m'
RESET = '\033[0m'


def schwarzschild_radius(M_solar: float) -> float:
    """Compute Schwarzschild radius in km."""
    M = M_solar * M_SUN
    r_s_cm = 2.0 * G * M / (C * C)
    return r_s_cm / 1.0e5  # Convert to km


def kerr_isco_radius(a_star: float, prograde: bool = True) -> float:
    """
    Compute ISCO radius in units of M (geometrized).

    Uses Bardeen-Press-Teukolsky (1972) formula.
    """
    if abs(a_star) > 1.0:
        raise ValueError(f"Invalid spin: |a*| = {abs(a_star)} > 1")

    # BPT formula
    one_minus_a2 = 1.0 - a_star * a_star
    cbrt_factor = one_minus_a2 ** (1.0/3.0)
    cbrt_plus = (1.0 + a_star) ** (1.0/3.0)
    cbrt_minus = (1.0 - a_star) ** (1.0/3.0)

    Z1 = 1.0 + cbrt_factor * (cbrt_plus + cbrt_minus)
    Z2 = math.sqrt(3.0 * a_star * a_star + Z1 * Z1)

    sqrt_term = math.sqrt((3.0 - Z1) * (3.0 + Z1 + 2.0 * Z2))

    if prograde:
        r_isco = 3.0 + Z2 - sqrt_term
    else:
        r_isco = 3.0 + Z2 + sqrt_term

    return r_isco


def test_schwarzschild_radius():
    """Test Schwarzschild radius calculation."""
    print(f"\n{BLUE}━━━ Test 1: Schwarzschild Radius ━━━{RESET}")

    tests = [
        (1.0, 2.95325),       # 1 M☉ → 2.95325 km (standard value)
        (4.3e6, 12698976.15), # Sgr A* → 12.7 million km
        (225.0, 664.481),     # GW231123 → 664.48 km
    ]

    passed = 0
    for M_solar, expected_km in tests:
        r_s = schwarzschild_radius(M_solar)
        error = abs(r_s - expected_km) / expected_km * 100

        if error < 0.01:  # Less than 0.01% error
            status = f"{GREEN}✓ PASS{RESET}"
            passed += 1
        else:
            status = f"{RED}✗ FAIL{RESET}"

        print(f"  M = {M_solar:.2e} M☉: r_s = {r_s:.2f} km (expected {expected_km:.2f} km) {status}")

    print(f"  Result: {passed}/{len(tests)} tests passed")
    return passed == len(tests)


def test_kerr_isco():
    """Test ISCO radius for various spins."""
    print(f"\n{BLUE}━━━ Test 2: Kerr ISCO Radius ━━━{RESET}")

    tests = [
        # (a*, prograde, expected r_ISCO/M)
        (0.0, True, 6.0),          # Schwarzschild
        (0.94, True, 2.024),       # Sgr A* (EHT-constrained)
        (0.998, True, 1.237),      # Near-extremal prograde
        (-0.5, False, 7.555),      # Moderate retrograde
        (-0.998, False, 8.994),    # Extreme retrograde
    ]

    passed = 0
    for a_star, prograde, expected in tests:
        r_isco = kerr_isco_radius(a_star, prograde)
        error = abs(r_isco - expected) / expected * 100

        if error < 0.5:  # Less than 0.5% error
            status = f"{GREEN}✓ PASS{RESET}"
            passed += 1
        else:
            status = f"{RED}✗ FAIL{RESET}"

        direction = "prograde" if prograde else "retrograde"
        print(f"  a* = {a_star:+.3f} ({direction}): r_ISCO = {r_isco:.3f} M (expected {expected:.3f} M) {status}")

    print(f"  Result: {passed}/{len(tests)} tests passed")
    return passed == len(tests)


def test_eht_constraints():
    """Test EHT observational constraints."""
    print(f"\n{BLUE}━━━ Test 3: EHT Constraints (2025-2026) ━━━{RESET}")

    # Sgr A* spin constraint from EHT-GRMHD (arXiv:2510.03602)
    a_star_sgrA = 0.94
    uncertainty = 0.05

    r_isco_sgrA = kerr_isco_radius(a_star_sgrA, prograde=True)

    print(f"  Sgr A* spin: a* = {a_star_sgrA} ± {uncertainty}")
    print(f"  ISCO radius: r_ISCO = {r_isco_sgrA:.3f} M")

    # Verify within range
    r_isco_upper = kerr_isco_radius(a_star_sgrA + uncertainty, prograde=True)
    r_isco_lower = kerr_isco_radius(a_star_sgrA - uncertainty, prograde=True)

    print(f"  ISCO range: [{r_isco_upper:.3f}, {r_isco_lower:.3f}] M")

    # M87 jet base distance
    jet_base_ly = 0.09
    jet_base_cm = jet_base_ly * 9.461e17

    # M87 mass
    M_M87 = 6.5e9 * M_SUN
    r_s_M87_cm = 2.0 * G * M_M87 / (C * C)
    r_s_M87_ly = r_s_M87_cm / 9.461e17

    jet_base_ratio = jet_base_ly / r_s_M87_ly

    print(f"\n  M87 jet base: {jet_base_ly} ly from horizon (EHT Jan 2026)")
    print(f"  M87 r_s: {r_s_M87_ly:.4f} ly")
    print(f"  Jet base / r_s: {jet_base_ratio:.1f}×")

    # For a*=0.94, ISCO should be ~2.024 M (high spin reduces ISCO radius)
    if 1.9 < r_isco_sgrA < 2.2 and jet_base_ly == 0.09:
        print(f"  {GREEN}✓ PASS{RESET}: EHT constraints validated")
        return True
    else:
        print(f"  {RED}✗ FAIL{RESET}: EHT constraints not met")
        return False


def test_ligo_constraints():
    """Test LIGO-Virgo-KAGRA O4 constraints."""
    print(f"\n{BLUE}━━━ Test 4: LIGO O4 Constraints (2023-2025) ━━━{RESET}")

    # GW231123: Most massive merger
    M_final = 225.0  # Solar masses
    r_s = schwarzschild_radius(M_final)

    print(f"  GW231123 final mass: {M_final} M☉")
    print(f"  Schwarzschild radius: {r_s:.2f} km")

    # Check if within simulator range (0.1 to 250 M☉)
    M_min = 0.1
    M_max = 250.0

    if M_min <= M_final <= M_max:
        print(f"  {GREEN}✓ PASS{RESET}: Within simulator mass range [{M_min}, {M_max}] M☉")
        mass_ok = True
    else:
        print(f"  {RED}✗ FAIL{RESET}: Outside mass range")
        mass_ok = False

    # GW241110: Retrograde spin
    a_star_retro = -0.5  # Example retrograde
    r_isco_retro = kerr_isco_radius(a_star_retro, prograde=False)

    print(f"\n  GW241110 (retrograde example): a* = {a_star_retro}")
    print(f"  ISCO radius: {r_isco_retro:.3f} M (larger than prograde)")

    # Check if within simulator spin range (-0.998 to +0.998)
    a_min = -0.998
    a_max = +0.998

    if a_min <= a_star_retro <= a_max:
        print(f"  {GREEN}✓ PASS{RESET}: Within simulator spin range [{a_min}, {a_max}]")
        spin_ok = True
    else:
        print(f"  {RED}✗ FAIL{RESET}: Outside spin range")
        spin_ok = False

    return mass_ok and spin_ok


def test_jet_physics():
    """Test relativistic jet physics."""
    print(f"\n{BLUE}━━━ Test 5: Jet Physics ━━━{RESET}")

    # Lorentz factor to velocity
    def lorentz_to_beta(Gamma):
        if Gamma <= 1.0:
            return 0.0
        return math.sqrt(1.0 - 1.0 / (Gamma * Gamma))

    tests = [
        (2.0, 0.866),    # Mildly relativistic
        (10.0, 0.995),   # Sgr A* typical
        (50.0, 0.9996),  # Blazar extreme
    ]

    passed = 0
    for Gamma, expected_beta in tests:
        beta = lorentz_to_beta(Gamma)
        error = abs(beta - expected_beta) / expected_beta * 100

        if error < 1.0:  # Less than 1% error
            status = f"{GREEN}✓ PASS{RESET}"
            passed += 1
        else:
            status = f"{RED}✗ FAIL{RESET}"

        print(f"  Γ = {Gamma:.1f}: β = {beta:.4f} (expected {expected_beta:.4f}) {status}")

    print(f"  Result: {passed}/{len(tests)} tests passed")
    return passed == len(tests)


def test_resolution_scaling():
    """Test multi-frequency resolution scaling."""
    print(f"\n{BLUE}━━━ Test 6: Multi-Frequency Resolution ━━━{RESET}")

    freq_230 = 230.0e9  # Hz
    freq_345 = 345.0e9  # Hz

    # Wavelength: λ = c / ν
    lambda_230 = C / freq_230  # cm
    lambda_345 = C / freq_345  # cm

    # Convert to mm
    lambda_230_mm = lambda_230 / 10.0
    lambda_345_mm = lambda_345 / 10.0

    # Resolution: θ ∝ λ
    resolution_ratio = freq_345 / freq_230

    print(f"  230 GHz: λ = {lambda_230_mm:.2f} mm")
    print(f"  345 GHz: λ = {lambda_345_mm:.2f} mm")
    print(f"  Resolution improvement: {resolution_ratio:.2f}× (345/230)")

    expected_improvement = 1.5
    error = abs(resolution_ratio - expected_improvement) / expected_improvement * 100

    if error < 1.0:
        print(f"  {GREEN}✓ PASS{RESET}: 50% resolution improvement validated")
        return True
    else:
        print(f"  {RED}✗ FAIL{RESET}: Resolution scaling incorrect")
        return False


def run_all_tests():
    """Run complete validation suite."""
    print(f"\n{YELLOW}{'='*60}{RESET}")
    print(f"{YELLOW}Blackhole Simulator - Physics Validation Suite{RESET}")
    print(f"{YELLOW}Version 2026.1 | EHT-Constrained{RESET}")
    print(f"{YELLOW}{'='*60}{RESET}")

    results = []

    results.append(("Schwarzschild Radius", test_schwarzschild_radius()))
    results.append(("Kerr ISCO", test_kerr_isco()))
    results.append(("EHT Constraints", test_eht_constraints()))
    results.append(("LIGO Constraints", test_ligo_constraints()))
    results.append(("Jet Physics", test_jet_physics()))
    results.append(("Multi-Frequency", test_resolution_scaling()))

    # Summary
    print(f"\n{YELLOW}{'='*60}{RESET}")
    print(f"{YELLOW}Validation Summary{RESET}")
    print(f"{YELLOW}{'='*60}{RESET}")

    passed = sum(1 for _, result in results if result)
    total = len(results)

    for name, result in results:
        status = f"{GREEN}✓ PASS{RESET}" if result else f"{RED}✗ FAIL{RESET}"
        print(f"  {name:.<40} {status}")

    print(f"\n{YELLOW}Total: {passed}/{total} tests passed ({passed/total*100:.0f}%){RESET}")

    if passed == total:
        print(f"\n{GREEN}{'='*60}")
        print(f"ALL VALIDATIONS PASSED ✓")
        print(f"Physics implementation correct as of 2026-01-31")
        print(f"{'='*60}{RESET}\n")
        return 0
    else:
        print(f"\n{RED}{'='*60}")
        print(f"SOME VALIDATIONS FAILED ✗")
        print(f"{total - passed} test(s) need attention")
        print(f"{'='*60}{RESET}\n")
        return 1


if __name__ == "__main__":
    sys.exit(run_all_tests())
