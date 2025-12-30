#!/usr/bin/env python3
"""Generate emissivity and redshift LUTs for Blackhole.

Uses compact-common if available for ISCO reference; otherwise falls back to
cleanroom formulas. Outputs CSV files under assets/luts.
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
from datetime import datetime, timezone
from typing import Callable

# Physical constants (cgs)
G = 6.67430e-8
C = 2.99792458e10
C2 = C * C
M_SUN = 1.98841e33


def kerr_isco_cleanroom(mass: float, spin_param: float, prograde: bool = True) -> float:
    m_geom = G * mass / C2
    a_star = spin_param / m_geom
    if abs(a_star) > 1.0:
        a_star = math.copysign(1.0, a_star)
    z1 = 1.0 + (1.0 - a_star * a_star) ** (1.0 / 3.0) * (
        (1.0 + a_star) ** (1.0 / 3.0) + (1.0 - a_star) ** (1.0 / 3.0)
    )
    z2 = math.sqrt(3.0 * a_star * a_star + z1 * z1)
    sqrt_term = math.sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2))
    r_isco = m_geom * (3.0 + z2 - sqrt_term if prograde else 3.0 + z2 + sqrt_term)
    return r_isco


def novikov_thorne_flux(r: float, mass: float, mdot: float, r_in: float, a_star: float) -> float:
    if r < r_in:
        return 0.0
    prefactor = 3.0 * G * mass * mdot / (8.0 * math.pi * r ** 3)
    basic = 1.0 - math.sqrt(r_in / r)
    spin_factor = 1.0 + 0.5 * a_star * math.sqrt((G * mass / C2) / r)
    return prefactor * basic * spin_factor


def kerr_redshift_equatorial(r: float, mass: float, spin_param: float) -> float:
    m_geom = G * mass / C2
    sigma = r * r
    factor = 1.0 - (2.0 * m_geom * r) / sigma
    if factor <= 0.0:
        return 0.0
    return 1.0 / math.sqrt(factor) - 1.0


def resolve_isco(mass: float, spin_param: float, prograde: bool) -> float:
    try:
        from compact_common.spacetime import kerr_isco  # type: ignore

        return float(kerr_isco(mass, spin_param, prograde))
    except Exception:
        return kerr_isco_cleanroom(mass, spin_param, prograde)


def write_csv(path: str, rows: list[list[float]]) -> None:
    with open(path, "w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["u", "value"])
        writer.writerows(rows)


def generate_lut(size: int, mass_solar: float, spin: float, mdot: float,
                 func: Callable[[float, float, float], float]) -> tuple[list[float], float, float]:
    mass = mass_solar * M_SUN
    r_g = G * mass / C2
    a = spin * r_g
    r_in = resolve_isco(mass, a, True)
    r_out = r_in * 4.0
    values = []
    for i in range(size):
        u = i / (size - 1)
        r = r_in + u * (r_out - r_in)
        values.append(func(r, mass, a))
    return values, r_in, r_out


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--size", type=int, default=256)
    parser.add_argument("--spin", type=float, default=0.0)
    parser.add_argument("--mass-solar", type=float, default=4.0e6)
    parser.add_argument("--mdot", type=float, default=0.1)
    args = parser.parse_args()

    size = max(args.size, 8)
    spin = max(min(args.spin, 0.99), -0.99)
    mass_solar = args.mass_solar
    mass = mass_solar * M_SUN
    r_g = G * mass / C2
    r_s = 2.0 * r_g
    a = spin * r_g
    r_in = resolve_isco(mass, a, True)
    r_out = r_in * 4.0

    l_edd = 1.26e38 * mass_solar
    mdot_edd = l_edd / (0.1 * C2)
    mdot = args.mdot * mdot_edd

    emissivity = []
    for i in range(size):
        u = i / (size - 1)
        r = r_in + u * (r_out - r_in)
        emissivity.append(novikov_thorne_flux(r, mass, mdot, r_in, spin))

    max_flux = max(emissivity) if emissivity else 1.0
    if max_flux > 0.0:
        emissivity = [v / max_flux for v in emissivity]

    redshift = []
    for i in range(size):
        u = i / (size - 1)
        r = r_in + u * (r_out - r_in)
        redshift.append(min(kerr_redshift_equatorial(r, mass, a), 10.0))

    lut_dir = os.path.join(os.path.dirname(__file__), "..", "assets", "luts")
    os.makedirs(lut_dir, exist_ok=True)

    emissivity_rows = [[i / (size - 1), v] for i, v in enumerate(emissivity)]
    redshift_rows = [[i / (size - 1), v] for i, v in enumerate(redshift)]

    write_csv(os.path.join(lut_dir, "emissivity_lut.csv"), emissivity_rows)
    write_csv(os.path.join(lut_dir, "redshift_lut.csv"), redshift_rows)

    meta = {
        "version": 1,
        "size": size,
        "spin": spin,
        "mass_solar": mass_solar,
        "mdot": args.mdot,
        "prograde": True,
        "r_in_over_rs": r_in / r_s,
        "r_out_over_rs": r_out / r_s,
        "r_in_cm": r_in,
        "r_out_cm": r_out,
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
    with open(os.path.join(lut_dir, "lut_meta.json"), "w", encoding="utf-8") as handle:
        json.dump(meta, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print("Wrote LUTs to", lut_dir)
    print("r_in/r_s=%.3f r_out/r_s=%.3f" % (r_in / r_s, r_out / r_s))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
