#!/usr/bin/env python3
"""Reference segment solutions of the polarized transfer equation dS/ds = J - K S.

For each row the exact constant-coefficient solution is the matrix exponential
of the augmented 5x5 generator

    A = | -K ds   J ds |
        |   0      0   |,     (S(ds), 1) = expm(A) (S0, 1),

evaluated with mpmath at 50 significant digits and confirmed at 70 digits.
K is the full propagation matrix of src/physics/stokes_exact.h, including the
alpha_U and rho_U entries. Inputs are written as C++ hexadecimal floating
literals, so the C++ test reads the exact doubles mpmath used; outputs carry
25 significant digits.

Groups:
  generic  - general eta, rho directions, Faraday depth 0.01..1000
  aligned  - alpha_U = rho_U = 0 (the FaradayPropagation frame)
  thin     - alpha_I ds in {1e-3, 1e-6, 1e-9} with Faraday depth 10 and 1000
  split    - alpha_I ds in {0.1, 0.3, 1} with Faraday depth 10 and 1000
  gain     - alpha_I ds in {-0.1, -1, -10} (stimulated emission) with Faraday
             depth 0, 1, 100 and dichroism, plus pure gain and |alpha_I ds| = 40
  deepgain - alpha_I ds from -650 to -715, past exp's overflow, with representable
             solutions
  nearnull - |eta| ~ |rho| up to 1e8, nearly perpendicular: w.w cancels
  faraday  - Faraday depth 1e6..1e15 along one axis, and at 1e12 beside a small eta
  faraday3d - Faraday depth 1e9..1e15 along a general axis
  limit    - zero K, pure Faraday, pure dichroism, eta || rho, w.w = 0,
             alpha_I = |eta|, optically thick, and scaled-unit twins

Usage: $PYTHON scripts/gen_stokes_reference.py > tests/stokes_exact_reference.inc
"""

from __future__ import annotations

import argparse
import math
import random
from collections.abc import Sequence

import mpmath as mp

WORK_DPS = 50
CHECK_DPS = 70

# (group, [aI, aQ, aU, aV, rQ, rU, rV], ds, [jI, jQ, jU, jV], [I0, Q0, U0, V0])
Row = tuple[str, list[float], float, list[float], list[float]]


def unit_vector(rng: random.Random) -> list[float]:
    """Uniform direction on the sphere."""
    z = rng.uniform(-1.0, 1.0)
    phi = rng.uniform(0.0, 2.0 * math.pi)
    s = math.sqrt(1.0 - z * z)
    return [s * math.cos(phi), s * math.sin(phi), z]


def physical_vectors(rng: random.Random) -> tuple[list[float], list[float]]:
    """Emission and initial Stokes vectors with I >= |P|."""
    j_i = rng.uniform(0.1, 1.0)
    jn = unit_vector(rng)
    jp = j_i * rng.uniform(0.0, 0.7)
    s_i = rng.uniform(0.5, 1.0)
    sn = unit_vector(rng)
    sp = s_i * rng.uniform(0.0, 0.9)
    return [j_i] + [jp * c for c in jn], [s_i] + [sp * c for c in sn]


def random_row(rng: random.Random, group: str, tau_a: float, tau_f: float, frame3d: bool) -> Row:
    """One segment at absorption depth tau_a and Faraday depth ~tau_f with |eta| <= |aI|."""
    ds = 1.0
    a_i = tau_a
    eta_n = unit_vector(rng)
    rho_n = unit_vector(rng)
    if not frame3d:
        eta_n[1] = 0.0
        rho_n[1] = 0.0
    frac = rng.uniform(0.0, 0.9)
    rho = rng.uniform(0.5, 1.0) * tau_f
    eta = [a_i * frac * c for c in eta_n]
    rhov = [rho * c for c in rho_n]
    k = [a_i, eta[0], eta[1], eta[2], rhov[0], rhov[1], rhov[2]]
    j, s0 = physical_vectors(rng)
    return group, k, ds, j, s0


def limit_rows() -> list[Row]:
    """Hand-built degenerate and boundary segments."""
    j = [0.8, 0.2, -0.1, 0.05]
    s0 = [1.0, 0.3, -0.2, 0.1]
    third = 1.0 / 3.0
    n = [third, 2.0 * third, 2.0 * third]
    rows: list[Row] = [
        ("limit", [0.0] * 7, 1.0, j, s0),
        ("limit", [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, 5.0], 1.0, j, s0),
        ("limit", [0.0, 0.0, 0.0, 0.0, 300.0, -400.0, 1200.0], 1.0, j, s0),
        ("limit", [1.0, 0.5, 0.2, -0.3, 0.0, 0.0, 0.0], 1.0, j, s0),
        ("limit", [1.0, 0.6, 0.0, 0.8, 0.0, 0.0, 3.0], 1.0, j, s0),
        ("limit", [1.0] + [0.4 * c for c in n] + [50.0 * c for c in n], 1.0, j, s0),
        ("limit", [1.0] + [0.4 * c for c in n] + [-50.0 * c for c in n], 1.0, j, s0),
        ("limit", [0.5, 0.5, 0.0, 0.0, 0.0, 0.5, 0.0], 1.0, j, s0),
        ("limit", [3.0, 3.0, 0.0, 0.0, 0.0, 0.0, 3.0], 1.0, j, s0),
        ("limit", [2.5, 2.0, 0.0, 0.0, 1.0e-6, 0.0, 2.000000002], 1.0, j, s0),
        ("limit", [800.0, 1.0, 0.0, 2.0, 0.0, 0.0, 30.0], 1.0, j, s0),
        ("limit", [50.0, 0.001, 0.0, 0.002, 0.0, 0.0, 0.05], 1.0, j, s0),
        ("limit", [5.0, 1.0e-4, 0.0, 0.0, 0.0, 0.0, 1.0e-3], 1.0, j, s0),
        ("limit", [40.0, 30.0, 0.0, 0.0, 0.0, 0.0, 5.0], 1.0, j, s0),
        ("limit", [3.0, 2.5, 0.0, 0.0, 0.0, 0.0, 0.5], 1.0, j, s0),
    ]
    # Same optical depths in scaled units: coefficients per 1e20 cm over 1e20 cm, and
    # per 1e-12 cm over 1e-12 cm.
    base_k = [1.0] + [0.4 * c for c in n] + [50.0 * c for c in n]
    for scale in (1.0e-20, 1.0e12):
        k = [c * scale for c in base_k]
        rows.append(("limit", k, 1.0 / scale, [c * scale for c in j], s0))
    return rows


def build_rows() -> list[Row]:
    rng = random.Random(20260925)
    rows: list[Row] = []
    for tau_f in (0.01, 1.0, 10.0, 100.0, 1000.0):
        for _ in range(4):
            rows.append(random_row(rng, "generic", rng.uniform(0.01, 2.0), tau_f, True))
    for tau_f in (1.0, 100.0, 1000.0):
        for _ in range(2):
            rows.append(random_row(rng, "aligned", rng.uniform(0.01, 2.0), tau_f, False))
    for tau_a in (1.0e-3, 1.0e-6, 1.0e-9):
        for tau_f in (10.0, 1000.0):
            for _ in range(2):
                rows.append(random_row(rng, "thin", tau_a, tau_f, True))
    for tau_a in (0.1, 0.3, 1.0):
        for tau_f in (10.0, 1000.0):
            for _ in range(2):
                rows.append(random_row(rng, "split", tau_a, tau_f, True))
    for tau_a in (-0.1, -1.0, -10.0):
        for tau_f in (0.0, 1.0, 100.0):
            for _ in range(2):
                rows.append(random_row(rng, "gain", tau_a, tau_f, True))
    j = [0.8, 0.2, -0.1, 0.05]
    s0 = [1.0, 0.3, -0.2, 0.1]
    rows.append(("gain", [-10.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0], 1.0, j, s0))
    rows.append(("gain", [-1.0e-9, 0.0, 0.0, 0.0, 0.0, 0.0, 3.0], 1.0, j, s0))
    rows.append(("gain", [-40.0, 0.001, 0.0, 0.002, 0.0, 0.0, 0.05], 1.0, j, s0))
    # Gain past exp's overflow at 709.8 with a representable solution: the
    # source reaches e^g / g, so S0 is kept small or zero.
    tiny = [1.0e-300, 3.0e-301, -2.0e-301, 1.0e-301]
    zero = [0.0] * 4
    rows.append(("deepgain", [-650.0, 0.3, 0.0, 0.2, 0.0, 0.0, 1.0], 1.0, j, s0))
    rows.append(("deepgain", [-700.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0], 1.0, j, tiny))
    rows.append(
        ("deepgain", [-710.0, 0.0, 0.0, 0.0, 0.0, 0.0, 0.0], 1.0, [1.0, 0.0, 0.0, 0.0], zero)
    )
    rows.append(("deepgain", [-710.0, 0.01, 0.0, 0.005, 0.0, 0.0, 3.0], 1.0, j, zero))
    rows.append(("deepgain", [-715.0, 0.0, 0.0, 0.0, 0.0, 0.0, 1.0e6], 1.0, j, zero))
    rows.extend(near_null_rows())
    rows.extend(faraday_rows())
    rows.extend(limit_rows())
    return rows


def near_null_rows() -> list[Row]:
    """|eta| and |rho| large and nearly equal with eta nearly perpendicular to rho,
    so w.w cancels in |eta|^2 - |rho|^2 and in eta.rho. One-ulp changes of these
    inputs move the solution by up to 0.35 relative (scale 1e8, 5-ulp gap)."""
    j = [0.8, 0.2, -0.1, 0.05]
    s0 = [1.0, 0.3, -0.2, 0.1]
    rows: list[Row] = []
    rows.append(
        (
            "nearnull",
            [0.0, 1.0e8, 0.0, 0.0, 0.0, 1.0e8 * (1 + 1.1102230246251565e-15), 0.0],
            1.0,
            [0.0] * 4,
            [1.0, 0.0, 0.0, 0.0],
        )
    )
    # The tilt makes eta.rho nonzero; it shrinks with scale so x1 = eta.rho / x2
    # keeps e^{x1} representable.
    for scale, tilted in ((1.0e4, 1.0e-9), (1.0e8, 1.0e-13)):
        for gap in (1.1102230246251565e-15, 1.0e-9, 1.0e-6):
            for tilt in (0.0, tilted):
                k = [0.0, scale, 0.0, 0.0, tilt * scale, scale * (1.0 + gap), 0.0]
                rows.append(("nearnull", k, 1.0, j, s0))
    return rows


def faraday_rows() -> list[Row]:
    """Faraday depth 1e6..1e15: rho along one axis (the double angle is |rho| ds
    exactly), along a general axis (|rho| carries ~1 ulp, eps x2 of angle), and
    with a small eta off the perpendicular (x1 = 1e-3 beside x2 = 1e12)."""
    j = [0.8, 0.2, -0.1, 0.05]
    s0 = [1.0, 0.3, -0.2, 0.1]
    rows: list[Row] = []
    for depth in (1.0e6, 1.0e9, 1.0e12, 1.0e15):
        rows.append(("faraday", [0.0, 0.0, 0.0, 0.0, 0.0, 0.0, depth], 1.0, [0.0] * 4, s0))
        rows.append(("faraday", [0.5, 0.0, 0.0, 0.0, 0.0, 0.0, -depth], 1.0, j, s0))
        rows.append(("faraday", [0.5, 0.0, 0.0, 0.0, depth, 0.0, 0.0], 1.0, j, s0))
    rows.append(("faraday", [0.5, 1.0e-3, 0.0, 1.0e-3, 0.0, 0.0, 1.0e12], 1.0, j, s0))
    rows.append(("faraday", [0.5, 0.3, 0.0, 0.0, 0.0, 0.0, 1.0e12], 1.0, j, s0))
    for depth in (1.0e9, 1.0e12, 1.0e15):
        axis = [0.3 / 1.3, -0.4 / 1.3, 1.2 / 1.3]
        rows.append(("faraday3d", [0.5, 0.0, 0.0, 0.0] + [depth * c for c in axis], 1.0, j, s0))
        rows.append(
            ("faraday3d", [0.0, 0.0, 0.0, 0.0] + [depth * c for c in axis], 1.0, [0.0] * 4, s0)
        )
    return rows


def propagate(k: Sequence[float], ds: float, j: Sequence[float], s0: Sequence[float]) -> list:
    """Exact segment solution at the current mpmath precision."""
    a_i, a_q, a_u, a_v, r_q, r_u, r_v = (mp.mpf(c) for c in k)
    kmat = mp.matrix(
        [
            [a_i, a_q, a_u, a_v],
            [a_q, a_i, r_v, -r_u],
            [a_u, -r_v, a_i, r_q],
            [a_v, r_u, -r_q, a_i],
        ]
    )
    dsm = mp.mpf(ds)
    aug = mp.zeros(5, 5)
    for i in range(4):
        for col in range(4):
            aug[i, col] = -kmat[i, col] * dsm
        aug[i, 4] = mp.mpf(j[i]) * dsm
    x = mp.matrix([mp.mpf(c) for c in s0] + [1])
    y = mp.expm(aug) * x
    return [y[i] for i in range(4)]


def hexlist(values: Sequence[float]) -> str:
    return ", ".join(float(v).hex() for v in values)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.parse_args()
    rows = build_rows()
    print("// Generated by scripts/gen_stokes_reference.py; do not edit by hand.")
    print(f"// mpmath {mp.__version__}, {WORK_DPS} digits, confirmed at {CHECK_DPS} digits.")
    print("// {group, {aI, aQ, aU, aV, rQ, rU, rV}, ds, {jI, jQ, jU, jV}, {I0, Q0, U0, V0},")
    print("//  {I, Q, U, V} at ds}")
    for group, k, ds, j, s0 in rows:
        mp.mp.dps = CHECK_DPS
        check = propagate(k, ds, j, s0)
        mp.mp.dps = WORK_DPS
        ref = propagate(k, ds, j, s0)
        scale = max(abs(c) for c in check)
        for a, b in zip(ref, check, strict=True):
            if abs(a - b) > mp.mpf("1e-40") * scale:
                raise SystemExit(
                    f"referee disagrees with itself at {WORK_DPS} vs {CHECK_DPS} digits"
                )
        print(f'{{"{group}", {{{hexlist(k)}}}, {float(ds).hex()},')
        print(f"  {{{hexlist(j)}}}, {{{hexlist(s0)}}},")
        print(f"  {{{', '.join(mp.nstr(v, 25, strip_zeros=False) for v in ref)}}}}},")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
