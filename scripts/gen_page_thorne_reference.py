#!/usr/bin/env python3
"""Reference values for the Page-Thorne thin-disk flux (G = c = M = 1).

Evaluates, at 30 significant digits, both the closed form of Page & Thorne
(1974) in x = sqrt(r) and a direct quadrature of

    F(r) = -(Mdot / 4 pi sqrt(-g)) Omega_,r / (E - Omega L)^2
           * integral_{r_isco}^{r} (E - Omega L) L_,r dr,   sqrt(-g) = r,

for Mdot = 1, prints their relative difference, the continuous flux peak in
units of r_isco, the efficiency 1 - E_isco and the face-on circular-emitter
redshift factor 1/u^t at the ISCO. src/physics/page_thorne.h and
tests/page_thorne_test.cpp carry the double-precision twins of these values.

Usage: $PYTHON scripts/gen_page_thorne_reference.py [--spins 0 0.5 0.9 0.998]
"""

from __future__ import annotations

import argparse

import mpmath as mp

mp.mp.dps = 30


def isco(a: mp.mpf) -> mp.mpf:
    """ISCO radius for a disk orbiting in +phi (signed spin)."""
    z1 = 1 + mp.cbrt(1 - a * a) * (mp.cbrt(1 + a) + mp.cbrt(1 - a))
    z2 = mp.sqrt(3 * a * a + z1 * z1)
    root = mp.sqrt((3 - z1) * (3 + z1 + 2 * z2))
    return 3 + z2 - root if a >= 0 else 3 + z2 + root


def orbit(r: mp.mpf, a: mp.mpf) -> tuple[mp.mpf, mp.mpf, mp.mpf]:
    """E, L, Omega of the circular equatorial geodesic at r."""
    x = mp.sqrt(r)
    q = x**3 - 3 * x + 2 * a
    denom = x ** mp.mpf(1.5) * mp.sqrt(q)
    energy = (x**3 - 2 * x + a) / denom
    ang_mom = (x**4 - 2 * a * x + a * a) / denom
    omega = 1 / (x**3 + a)
    return energy, ang_mom, omega


def closed_form(r: mp.mpf, a: mp.mpf) -> mp.mpf:
    """Page-Thorne flux F(r) for Mdot = 1 from the x0..x3 logarithmic form."""
    x = mp.sqrt(r)
    x0 = mp.sqrt(isco(a))
    theta = mp.acos(a) / 3
    roots = [
        2 * mp.cos(theta - mp.pi / 3),
        2 * mp.cos(theta + mp.pi / 3),
        -2 * mp.cos(theta),
    ]
    bracket = x - x0 - mp.mpf(3) / 2 * a * mp.log(x / x0)
    for i, xi in enumerate(roots):
        if abs(xi) < mp.mpf("1e-25"):
            continue
        xj = roots[(i + 1) % 3]
        xk = roots[(i + 2) % 3]
        bracket -= 3 * (xi - a) ** 2 / (xi * (xi - xj) * (xi - xk)) * mp.log((x - xi) / (x0 - xi))
    return 3 / (8 * mp.pi) * bracket / (x**4 * (x**3 - 3 * x + 2 * a))


def quadrature(r: mp.mpf, a: mp.mpf) -> mp.mpf:
    """Page-Thorne flux F(r) for Mdot = 1 by direct quadrature."""

    def ang_mom(s: mp.mpf) -> mp.mpf:
        return orbit(s, a)[1]

    def omega(s: mp.mpf) -> mp.mpf:
        return orbit(s, a)[2]

    def integrand(s: mp.mpf) -> mp.mpf:
        energy, lz, om = orbit(s, a)
        return (energy - om * lz) * mp.diff(ang_mom, s)

    integral = mp.quad(integrand, [isco(a), r])
    energy, lz, om = orbit(r, a)
    return -(1 / (4 * mp.pi * r)) * mp.diff(omega, r) / (energy - om * lz) ** 2 * integral


def peak_radius(a: mp.mpf) -> mp.mpf:
    """Radius of the flux maximum, from dF/dr = 0 seeded between the ISCO and 2 r_isco."""
    r_isco = isco(a)
    return mp.findroot(
        lambda s: mp.diff(lambda t: closed_form(t, a), s),
        (r_isco * mp.mpf("1.05"), 2 * r_isco),
        solver="anderson",
    )


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("--spins", type=float, nargs="+", default=[0.0, 0.5, 0.9, 0.998, -0.5])
    parser.add_argument("--ratios", type=float, nargs="+", default=[1.1, 1.5, 3.0, 10.0])
    args = parser.parse_args()

    for spin in args.spins:
        a = mp.mpf(spin)
        r_isco = isco(a)
        r_peak = peak_radius(a)
        x = mp.sqrt(r_isco)
        u_t = (1 + a / x**3) / mp.sqrt(1 - 3 / r_isco + 2 * a / x**3)
        print(f"a = {spin}")
        print(f"  r_isco         = {mp.nstr(r_isco, 15)}")
        print(f"  r_peak         = {mp.nstr(r_peak, 15)}  ({mp.nstr(r_peak / r_isco, 10)} r_isco)")
        print(f"  eta            = {mp.nstr(1 - orbit(r_isco, a)[0], 15)}")
        print(f"  1/u^t (ISCO)   = {mp.nstr(1 / u_t, 15)}")
        for ratio in args.ratios:
            r = r_isco * mp.mpf(ratio)
            closed = closed_form(r, a)
            quad = quadrature(r, a)
            rel = closed / quad - 1
            print(
                f"  r = {ratio:5.2f} r_isco: closed {mp.nstr(closed, 15)}"
                f"  quad {mp.nstr(quad, 15)}  rel {mp.nstr(rel, 3)}"
            )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
