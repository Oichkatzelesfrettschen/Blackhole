#!/usr/bin/env python3
"""Generate validation tables for unit-system alignment.

Outputs:
  - assets/validation/redshift_curve.csv (r_over_rs,value)
  - assets/validation/metrics.json (r_s, r_ph, r_isco, metadata)
  - assets/validation/spin_radii_curve.csv (spin,r_isco_over_rs,r_ph_over_rs)
"""

from __future__ import annotations

import argparse
import csv
import json
import math
import os
from datetime import datetime, timezone
from importlib.metadata import PackageNotFoundError, version

from kerr_signed_spin import conventional_orbit_args

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
    # Signed spin (src/physics/kerr.h kerrIscoRadius): prograde means angular
    # momentum along +z; the orbit co-rotates when a_star and L_z share a sign.
    co_rotating = a_star >= 0.0 if prograde else a_star <= 0.0
    r_isco = m_geom * (3.0 + z2 - sqrt_term if co_rotating else 3.0 + z2 + sqrt_term)
    return r_isco


def kerr_photon_orbit(mass: float, spin_param: float, prograde: bool = True) -> float:
    m_geom = G * mass / C2
    a_star = spin_param / m_geom
    a_star = max(min(a_star, 1.0), -1.0)
    if prograde:
        angle = (2.0 / 3.0) * math.acos(-a_star)
    else:
        angle = (2.0 / 3.0) * math.acos(a_star)
    return 2.0 * m_geom * (1.0 + math.cos(angle))


def kerr_redshift_equatorial(r: float, mass: float, spin_param: float) -> float:
    """Equatorial redshift of a zero-angular-momentum emitter seen from infinity.

    1 + z = 1 / alpha with the ZAMO lapse alpha = sqrt(Sigma Delta / A), which
    at theta = pi/2 is sqrt(r^2 Delta / ((r^2 + a^2)^2 - a^2 Delta)), matching
    physics::kerrRedshift in src/physics/kerr.h. It stays finite inside the
    ergosphere (z = 2.3166 at a* = 0.9, r = 1.8 M) and diverges at the horizon;
    at and inside r_+ the function returns +inf. At a = 0 it is
    1/sqrt(1 - 2M/r) - 1.
    """
    m_geom = G * mass / C2
    a2 = spin_param * spin_param
    # physics::kerrZamoLapse requires r > r_+; below r_- Delta turns positive
    # again, so its sign alone would admit the region inside the Cauchy horizon.
    r_plus = m_geom + math.sqrt(max(0.0, m_geom * m_geom - a2))
    delta = r * r - 2.0 * m_geom * r + a2
    big_a = (r * r + a2) ** 2 - a2 * delta
    if r <= r_plus or delta <= 0.0 or big_a <= 0.0:
        return math.inf
    return 1.0 / math.sqrt(r * r * delta / big_a) - 1.0


# The runtime LUT (src/physics/lut.h, generate_luts.py) and physics_test clamp
# the redshift to this value; the horizon's infinite redshift maps onto it.
REDSHIFT_CAP = 10.0


def capped_redshift(z: float) -> float:
    """z clamped to [0, REDSHIFT_CAP]; a non-finite z (horizon, interior) is the cap."""
    if not math.isfinite(z):
        return REDSHIFT_CAP
    return min(max(z, 0.0), REDSHIFT_CAP)


def maybe_compact_common() -> dict[str, object] | None:
    try:
        from compact_common.spacetime import (  # type: ignore
            gravitational_redshift,
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
            "gravitational_redshift": gravitational_redshift,
            "source": "compact-common",
            "version": cc_version,
        }
    except Exception:
        return None


def resolve_isco(mass: float, spin_param: float, prograde: bool,
                 ref: dict[str, object] | None) -> float:
    """Signed-spin ISCO; compact-common receives |a| and the co-rotation flag."""
    if ref:
        magnitude, co_rotating = conventional_orbit_args(spin_param, prograde)
        return float(ref["kerr_isco"](mass, magnitude, co_rotating))
    return kerr_isco_cleanroom(mass, spin_param, prograde)


def resolve_photon_orbit(mass: float, spin_param: float, prograde: bool,
                         ref: dict[str, object] | None) -> float:
    """Signed-spin photon orbit; compact-common receives |a| and the co-rotation flag."""
    if ref:
        magnitude, co_rotating = conventional_orbit_args(spin_param, prograde)
        return float(ref["kerr_photon_orbit"](mass, magnitude, co_rotating))
    return kerr_photon_orbit(mass, spin_param, prograde)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--points", type=int, default=128)
    parser.add_argument("--spin", type=float, default=0.0)
    parser.add_argument("--mass-solar", type=float, default=4.0e6)
    parser.add_argument("--r-min-over-rs", type=float, default=0.0)
    parser.add_argument("--r-max-over-rs", type=float, default=20.0)
    parser.add_argument("--spin-points", type=int, default=64)
    parser.add_argument("--spin-min", type=float, default=-0.99)
    parser.add_argument("--spin-max", type=float, default=0.99)
    args = parser.parse_args()

    points = max(args.points, 16)
    spin = max(min(args.spin, 0.99), -0.99)
    mass_solar = args.mass_solar
    mass = mass_solar * M_SUN
    r_g = G * mass / C2
    r_s = 2.0 * r_g
    a = spin * r_g

    # The disk orbits along +z; the signed spin selects co- or counter-rotation.
    ref = maybe_compact_common()
    r_isco = resolve_isco(mass, a, True, ref)
    r_ph = resolve_photon_orbit(mass, a, True, ref)
    source = ref["source"] if ref else "cleanroom"

    r_min_over_rs = args.r_min_over_rs
    if r_min_over_rs <= 0.0:
        r_min_over_rs = max(r_isco / r_s, 1.1)
    r_max_over_rs = max(args.r_max_over_rs, r_min_over_rs + 1.0)
    spin_points = max(args.spin_points, 8)
    spin_min = max(min(args.spin_min, 0.99), -0.99)
    spin_max = max(min(args.spin_max, 0.99), -0.99)
    if spin_max <= spin_min:
        spin_max = min(spin_min + 0.01, 0.99)

    lut_dir = os.path.join(os.path.dirname(__file__), "..", "assets", "validation")
    os.makedirs(lut_dir, exist_ok=True)

    rows: list[list[float]] = []
    if ref and abs(spin) < 1e-8:
        redshift_source = "compact-common"
    else:
        redshift_source = "cleanroom"
    for i in range(points):
        u = i / (points - 1)
        r_over_rs = r_min_over_rs + u * (r_max_over_rs - r_min_over_rs)
        r = r_over_rs * r_s
        if redshift_source == "compact-common":
            z = float(ref["gravitational_redshift"](r, mass))
        else:
            z = kerr_redshift_equatorial(r, mass, a)
        rows.append([r_over_rs, capped_redshift(z)])

    with open(os.path.join(lut_dir, "redshift_curve.csv"), "w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["r_over_rs", "value"])
        writer.writerows(rows)

    spin_rows: list[list[float]] = []
    for i in range(spin_points):
        u = i / (spin_points - 1)
        spin_val = spin_min + u * (spin_max - spin_min)
        a_val = spin_val * r_g
        # The disk orbits along +z; the signed spin selects co- or
        # counter-rotation for both radii.
        r_isco_spin = resolve_isco(mass, a_val, True, ref)
        r_ph_spin = resolve_photon_orbit(mass, a_val, True, ref)
        spin_rows.append([spin_val, r_isco_spin / r_s, r_ph_spin / r_s])

    with open(os.path.join(lut_dir, "spin_radii_curve.csv"), "w", newline="") as handle:
        writer = csv.writer(handle)
        writer.writerow(["spin", "r_isco_over_rs", "r_ph_over_rs"])
        writer.writerows(spin_rows)

    meta = {
        "version": 1,
        "source": source,
        "isco_source": source,
        "photon_source": "compact-common" if ref else "cleanroom",
        "redshift_source": redshift_source,
        "redshift_model": "zamo-equatorial",
        "units": {
            "system": "cgs",
            "length": "cm",
            "mass": "g",
            "time": "s",
        },
        "points": points,
        "spin": spin,
        "mass_solar": mass_solar,
        "r_s_cm": r_s,
        "r_isco_cm": r_isco,
        "r_ph_cm": r_ph,
        "r_min_over_rs": r_min_over_rs,
        "r_max_over_rs": r_max_over_rs,
        "spin_curve_points": spin_points,
        "spin_curve_min": spin_min,
        "spin_curve_max": spin_max,
        "timestamp_utc": datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ"),
    }
    if ref:
        meta["compact_common_version"] = ref["version"]
    with open(os.path.join(lut_dir, "metrics.json"), "w", encoding="utf-8") as handle:
        json.dump(meta, handle, indent=2, sort_keys=True)
        handle.write("\n")

    print("Wrote validation tables to", lut_dir)
    print("source:", source)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
