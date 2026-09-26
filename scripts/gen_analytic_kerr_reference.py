#!/usr/bin/env python3
"""Reference half periods and radii of the analytic Kerr radial solution.

For four real roots r1 > r2 > r3 > r4 of the radial quartic,
src/physics/analytic_kerr_geodesic.h evaluates

    radialHalfPeriod = K(m) / s,   s = sqrt((r1 - r3)(r2 - r4)) / 2,
    rAnalytic(lambda) = r3 + (r3 - r4)(r1 - r3) sn^2 / ((r3 - r4) + (r1 - r3) cn^2),
    sn = sn(s lambda | m),   m = (r2 - r3)(r1 - r4) / ((r1 - r3)(r2 - r4)).

Rows (7, 3, 1 + g, 1) put 1 - m = g/3 from 3e-4 down to 3e-10, and
(6, nextafter(6, 0), 1.5, -0.5) puts it at 6.1e-17, below the rounding of a
double modulus near 1 (the separatrix).

Half period: m comes exactly from the double roots, with
1 - m = (r1 - r2)(r3 - r4) / ((r1 - r3)(r2 - r4)), so the rows with 1 - m down
to 1e-10 test the evaluation of K, not the rounding of m.

Radius: the reference takes the exact m of the double roots and the argument
u = s lambda formed in IEEE double as the C++ forms it (Python floats are IEEE
doubles). Each radius row also carries the first-order error bound
|r3| + |r - r3| + |dr/dsn| (|sn| + |u sn'|) + |dr/dcn| (|cn| + |u cn'|)
+ |dr/dm| s_m in units of the rounding error, s_m = k'^2 where the C++ runs the
Landen transformation on 1 - m from the roots and s_m = m where it passes a
double modulus to Boost: sn and cn backward-stable in u, with an absolute
floor, the nonnegative sum, and the elliptic parameter err by a few ulp times
it.

mpmath at 40 digits, confirmed at 60.

Usage: $PYTHON scripts/gen_analytic_kerr_reference.py > tests/analytic_kerr_reference.inc
"""

from __future__ import annotations

import argparse
import math
from collections.abc import Callable

import mpmath as mp

WORK_DPS = 40
CHECK_DPS = 60

LAMBDAS = (0.05, 0.3, 0.77, 1.4, 2.9, 5.5)

# ANALYTIC_KERR_PROMOTE_BELOW in src/physics/analytic_kerr_geodesic.h.
PROMOTE_BELOW = 1.0e-4


def near_one_roots(one_minus_m: float) -> tuple[float, float, float, float]:
    """Roots (6, 6 - d, 1.5, -0.5) with 1 - m close to the target."""
    d = one_minus_m * 4.5 * 6.5 / 2.0
    return 6.0, 6.0 - d, 1.5, -0.5


ROOT_SETS: list[tuple[float, float, float, float]] = [
    (6.0, 4.0, 1.5, -0.5),
    (10.0, 3.2, 1.2, -2.0),
    (5.0, 4.9, 1.1, -0.1),
    (12.0, 2.5, 2.4, -3.0),
    (8.0, 7.999, 0.2, -1.5),
    near_one_roots(1.0e-6),
    near_one_roots(1.0e-8),
    near_one_roots(1.0e-10),
    (7.0, 3.0, 1.0 + 1.0e-3, 1.0),
    (7.0, 3.0, 1.0 + 3.0e-4, 1.0),
    (7.0, 3.0, 1.0 + 1.0e-5, 1.0),
    (7.0, 3.0, 1.0 + 1.0e-9, 1.0),
    (7.0, 3.0 + 1.0e-9, 3.0, 1.0),
    (6.0, math.nextafter(6.0, 0.0), 1.5, -0.5),
]


def half_period(roots: tuple[float, float, float, float]) -> mp.mpf:
    r1, r2, r3, r4 = (mp.mpf(r) for r in roots)
    one_minus_m = (r1 - r2) * (r3 - r4) / ((r1 - r3) * (r2 - r4))
    scale = mp.sqrt((r1 - r3) * (r2 - r4)) / 2
    # K from the complement, pi / (2 agm(1, k')), which mp.ellipk would form as 1 - m.
    return mp.pi / (2 * mp.agm(1, mp.sqrt(one_minus_m))) / scale


def radius_at(roots: tuple[float, float, float, float], u: mp.mpf, m: mp.mpf) -> tuple:
    """r, sn, cn, dn at argument u and parameter m."""
    sn = mp.ellipfun("sn", u, m=m)
    cn = mp.ellipfun("cn", u, m=m)
    dn = mp.ellipfun("dn", u, m=m)
    a1, _, a3, a4 = (mp.mpf(v) for v in roots)
    denom = (a3 - a4) + (a1 - a3) * cn * cn
    return a3 + (a3 - a4) * (a1 - a3) * sn * sn / denom, sn, cn, dn


def radius(roots: tuple[float, float, float, float], lam: float) -> tuple[mp.mpf, mp.mpf]:
    """r(lambda) at the exact m of the double roots and the u the C++ forms in
    double, and the first-order error bound of r in units of the rounding error."""
    r1, r2, r3, r4 = roots
    scale = math.sqrt(abs((r1 - r3) * (r2 - r4))) / 2.0
    u = mp.mpf(scale * lam)
    a1, a2, a3, a4 = (mp.mpf(v) for v in roots)
    kp2 = (a1 - a2) * (a3 - a4) / ((a1 - a3) * (a2 - a4))
    m = 1 - kp2
    r, sn, cn, dn = radius_at(roots, u, m)
    big_a = (a3 - a4) * (a1 - a3)
    denom = (a3 - a4) + (a1 - a3) * cn * cn
    corr = r - a3
    # sn and cn each err by a few ulp of |f| + |u f'| (backward-stable in u
    # with an absolute floor), and the nonnegative sum r3 + corr by a few ulp
    # of |r3| + |corr|. The elliptic parameter errs through dr/dm by a few ulp
    # of k'^2 where the C++ runs the Landen transformation on 1 - m from the
    # roots (1 - m < PROMOTE_BELOW) and by a few ulp of m where it passes a
    # double modulus k = sqrt(m) to Boost.
    dr_dsn = 2 * sn * big_a / denom
    dr_dcn = -2 * cn * big_a * sn * sn * (a1 - a3) / (denom * denom)
    # Central difference with a step inside 1 - m, so m + h stays below 1.
    step = kp2 * mp.mpf("1e-10")
    dr_dm = (
        (radius_at(roots, u, m + step)[0] - radius_at(roots, u, m - step)[0]) / (2 * step)
        if kp2 > 0
        else mp.mpf(0)
    )
    kp2_double = ((r1 - r2) * (r3 - r4)) / ((r1 - r3) * (r2 - r4))
    parameter_scale = kp2 if kp2_double < PROMOTE_BELOW else m
    cond = (
        abs(a3)
        + abs(corr)
        + abs(dr_dsn) * (abs(sn) + abs(u * cn * dn))
        + abs(dr_dcn) * (abs(cn) + abs(u * sn * dn))
        + abs(dr_dm) * parameter_scale
    )
    return r, cond


def confirmed(fn: Callable[..., list], *args: object) -> list:
    """fn(*args) at WORK_DPS after agreeing with CHECK_DPS to 1e-30 relative."""
    mp.mp.dps = CHECK_DPS
    check = fn(*args)
    mp.mp.dps = WORK_DPS
    work = fn(*args)
    for a, b in zip(work, check, strict=True):
        if abs(a - b) > mp.mpf("1e-30") * abs(b):
            raise SystemExit(f"referee disagrees with itself at {WORK_DPS} vs {CHECK_DPS} digits")
    return work


def num(v: mp.mpf) -> str:
    return mp.nstr(v, 25, strip_zeros=False)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.parse_args()
    print("// Generated by scripts/gen_analytic_kerr_reference.py; do not edit by hand.")
    print(f"// mpmath {mp.__version__}, {WORK_DPS} digits, confirmed at {CHECK_DPS} digits.")
    print(f"// lambda = {{{', '.join(str(v) for v in LAMBDAS)}}}")
    print("// {{r1, r2, r3, r4}, half period, {r(lambda)}, {condition number of r(lambda)}}")
    print("constexpr AnalyticKerrRow ANALYTIC_KERR_ROWS[] = {")
    for roots in ROOT_SETS:
        (hp,) = confirmed(lambda rr: [half_period(rr)], roots)
        rs = []
        conds = []
        for lam in LAMBDAS:
            (r,) = confirmed(lambda rr, lv: [radius(rr, lv)[0]], roots, lam)
            cond = radius(roots, lam)[1]
            rs.append(num(r))
            conds.append(mp.nstr(cond, 6))
        print(f"    {{{{{', '.join(v.hex() for v in roots)}}},")
        print(f"     {num(hp)},")
        print(f"     {{{', '.join(rs)}}},")
        print(f"     {{{', '.join(conds)}}}}},")
    print("};")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
