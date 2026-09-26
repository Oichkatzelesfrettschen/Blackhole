"""Signed-spin adapter for Kerr orbit APIs that use the conventional labels.

Blackhole's convention (src/physics/kerr.h kerrIscoRadius): the spin a is
signed, a > 0 rotating about +z, and "prograde" names an orbit with angular
momentum along +z. An accretion disk that orbits along +z therefore
counter-rotates with a hole of negative spin, and its ISCO at a* = -0.9 is
8.7174 M.

compact-common's spacetime.kerr_isco and kerr_photon_orbit follow the
conventional labels instead: "prograde" means co-rotating with the hole. Fed
a negative spin and prograde=True they return the co-rotating radius
(2.3209 M at a* = -0.9). conventional_orbit_args converts Blackhole's
arguments to that API: the spin magnitude and whether the orbit co-rotates.
"""

from __future__ import annotations


def conventional_orbit_args(spin_param: float, prograde: bool) -> tuple[float, bool]:
    """Map (signed spin, angular momentum along +z) to (|spin|, co-rotating).

    The orbit co-rotates when the hole's spin and the orbit's angular momentum
    point the same way; at zero spin both branches coincide.
    """
    co_rotating = (spin_param >= 0.0) == prograde
    return abs(spin_param), co_rotating
