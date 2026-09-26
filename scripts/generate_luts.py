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
from collections.abc import Callable
from datetime import UTC, datetime
from importlib.metadata import PackageNotFoundError, version

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


def page_thorne_isco(a_star: float) -> float:
    """ISCO radius in units of M for a disk orbiting in +phi (signed spin)."""
    z1 = 1.0 + (1.0 - a_star * a_star) ** (1.0 / 3.0) * (
        (1.0 + a_star) ** (1.0 / 3.0) + (1.0 - a_star) ** (1.0 / 3.0)
    )
    z2 = math.sqrt(3.0 * a_star * a_star + z1 * z1)
    root = math.sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2))
    return 3.0 + z2 - root if a_star >= 0.0 else 3.0 + z2 + root


def page_thorne_shape(r: float, a_star: float) -> float:
    """Page-Thorne flux shape S = F * 8 pi / (3 Mdot) at r in units of M.

    Twin of physics::pageThorneFluxShape (src/physics/page_thorne.h).
    """
    r_isco = page_thorne_isco(a_star)
    if r <= r_isco:
        return 0.0
    x = math.sqrt(r)
    x0 = math.sqrt(r_isco)
    theta = math.acos(a_star) / 3.0
    roots = (
        2.0 * math.cos(theta - math.pi / 3.0),
        2.0 * math.cos(theta + math.pi / 3.0),
        -2.0 * math.cos(theta),
    )
    bracket = x - x0 - 1.5 * a_star * math.log(x / x0)
    for i, xi in enumerate(roots):
        if abs(xi) < 1e-14:
            continue
        xj = roots[(i + 1) % 3]
        xk = roots[(i + 2) % 3]
        coeff = 3.0 * (xi - a_star) ** 2 / (xi * (xi - xj) * (xi - xk))
        bracket -= coeff * math.log((x - xi) / (x0 - xi))
    return bracket / (x**4 * (x**3 - 3.0 * x + 2.0 * a_star))


def novikov_thorne_flux(r: float, mass: float, mdot: float, r_in: float, a_star: float) -> float:
    """Page-Thorne surface flux [erg cm^-2 s^-1] at r [cm]; zero inside r_in."""
    if r < r_in:
        return 0.0
    r_g = G * mass / C2
    prefactor = 3.0 * G * mass * mdot / (8.0 * math.pi * r**3)
    r_m = r / r_g
    return prefactor * r_m**3 * page_thorne_shape(r_m, a_star)


def disk_emitter_redshift(r: float, mass: float, spin_param: float) -> float:
    """Redshift z = u^t - 1 of the prograde Keplerian emitter at r [cm], face-on.

    Twin of physics::generateRedshiftLut (src/physics/lut.h); the spin enters as
    |a*| to match the prograde ISCO of the LUT's radial domain. Zero where no
    timelike circular orbit exists.
    """
    m_geom = G * mass / C2
    a_star = abs(spin_param / m_geom)
    x = r / m_geom
    inv_r32 = 1.0 / (x * math.sqrt(x))
    q = 1.0 - 3.0 / x + 2.0 * a_star * inv_r32
    if q <= 0.0:
        return 0.0
    u_t = (1.0 + a_star * inv_r32) / math.sqrt(q)
    return u_t - 1.0


def kerr_photon_orbit_cleanroom(mass: float, spin_param: float, prograde: bool = True) -> float:
    m_geom = G * mass / C2
    a_star = spin_param / m_geom
    a_star = max(min(a_star, 1.0), -1.0)
    if prograde:
        angle = (2.0 / 3.0) * math.acos(-a_star)
    else:
        angle = (2.0 / 3.0) * math.acos(a_star)
    return 2.0 * m_geom * (1.0 + math.cos(angle))


def compact_common_refs() -> dict[str, object] | None:
    try:
        from compact_common.spacetime import (  # type: ignore
            kerr_isco,
            kerr_photon_orbit,
        )

        try:
            cc_version = version("compact-common")
        except PackageNotFoundError:
            try:
                cc_version = version("compact_common")
            except PackageNotFoundError:
                cc_version = "unknown"

        return {
            "kerr_isco": kerr_isco,
            "kerr_photon_orbit": kerr_photon_orbit,
            "version": cc_version,
        }
    except Exception:
        return None


def resolve_isco(mass: float, spin_param: float, prograde: bool,
                 refs: dict[str, object] | None) -> tuple[float, str]:
    if refs:
        return float(refs["kerr_isco"](mass, spin_param, prograde)), "compact-common"
    return kerr_isco_cleanroom(mass, spin_param, prograde), "cleanroom"


def resolve_photon_orbit(mass: float, spin_param: float, prograde: bool,
                         refs: dict[str, object] | None) -> float:
    if refs:
        return float(refs["kerr_photon_orbit"](mass, spin_param, prograde))
    return kerr_photon_orbit_cleanroom(mass, spin_param, prograde)


def write_csv(path: str, rows: list[list[float]]) -> None:
    with open(path, "w", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(["u", "value"])
        writer.writerows(rows)


def write_spin_csv(path: str, rows: list[list[float]]) -> None:
    with open(path, "w", newline="") as handle:
        writer = csv.writer(handle, lineterminator="\n")
        writer.writerow(["spin", "r_isco_over_rs", "r_ph_over_rs"])
        writer.writerows(rows)


def generate_lut(size: int, mass_solar: float, spin: float, mdot: float,
                 func: Callable[[float, float, float], float],
                 refs: dict[str, object] | None = None) -> tuple[list[float], float, float]:
    mass = mass_solar * M_SUN
    r_g = G * mass / C2
    a = spin * r_g
    r_in, _ = resolve_isco(mass, a, True, refs)
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
    parser.add_argument("--spin-points", type=int, default=0)
    parser.add_argument("--spin-min", type=float, default=-0.99)
    parser.add_argument("--spin-max", type=float, default=0.99)
    args = parser.parse_args()

    size = max(args.size, 8)
    spin = max(min(args.spin, 0.99), -0.99)
    mass_solar = args.mass_solar
    mass = mass_solar * M_SUN
    r_g = G * mass / C2
    r_s = 2.0 * r_g
    a = spin * r_g
    refs = compact_common_refs()
    r_in, isco_source = resolve_isco(mass, a, True, refs)
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
        redshift.append(min(disk_emitter_redshift(r, mass, a), 10.0))

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
        "isco_source": isco_source,
        "emissivity_model": "page-thorne",
        "redshift_model": "circular-emitter-face-on",
        "units": {
            "system": "cgs",
            "length": "cm",
            "mass": "g",
            "time": "s",
        },
        "r_in_over_rs": r_in / r_s,
        "r_out_over_rs": r_out / r_s,
        "r_in_cm": r_in,
        "r_out_cm": r_out,
        "timestamp_utc": datetime.now(UTC).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
    if refs:
        meta["compact_common_version"] = refs["version"]

    spin_points = max(args.spin_points, 0)
    if spin_points > 0:
        spin_min = max(min(args.spin_min, 0.99), -0.99)
        spin_max = max(min(args.spin_max, 0.99), -0.99)
        if spin_max <= spin_min:
            spin_max = min(spin_min + 0.01, 0.99)
        spin_rows = []
        for i in range(spin_points):
            u = i / (spin_points - 1)
            spin_val = spin_min + u * (spin_max - spin_min)
            a_val = spin_val * r_g
            prograde = spin_val >= 0.0
            r_isco_spin, _ = resolve_isco(mass, a_val, prograde, refs)
            r_ph_spin = resolve_photon_orbit(mass, a_val, prograde, refs)
            spin_rows.append([spin_val, r_isco_spin / r_s, r_ph_spin / r_s])
        write_spin_csv(os.path.join(lut_dir, "spin_radii_lut.csv"), spin_rows)
        meta["spin_curve_points"] = spin_points
        meta["spin_curve_min"] = spin_min
        meta["spin_curve_max"] = spin_max
        meta["spin_curve_source"] = "compact-common" if refs else "cleanroom"
    with open(os.path.join(lut_dir, "lut_meta.json"), "w", encoding="utf-8") as handle:
        json.dump(meta, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print("Wrote LUTs to", lut_dir)
    print(f"r_in/r_s={r_in / r_s:.3f} r_out/r_s={r_out / r_s:.3f}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
