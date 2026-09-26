"""Signed-spin orbits and the ZAMO redshift in the LUT and validation-table generators.

Both generators resolve radii through compact-common when it is importable and
through their cleanroom formulas otherwise. The two paths must agree on the
signed convention of src/physics/kerr.h: at a* = -0.9 the +z disk's ISCO is
8.7174 M, not the co-rotating 2.3209 M. Their redshift curves follow
physics::kerrRedshift, the ZAMO lapse; the references are that lapse on the
equatorial Kerr metric evaluated in mpmath.
"""

import importlib
import importlib.util
import math
import sys
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1] / "scripts"
sys.path.insert(0, str(SCRIPTS))


def load(name):
    spec = importlib.util.spec_from_file_location(name, SCRIPTS / f"{name}.py")
    if spec is None or spec.loader is None:
        raise RuntimeError(f"Cannot load {name}")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


LUTS = load("generate_luts")
TABLES = load("generate_validation_tables")
MASS = 10.0 * LUTS.M_SUN
M_GEOM = LUTS.G * MASS / LUTS.C2

# Bardeen-Press-Teukolsky, angular momentum along +z, in units of M.
ISCO_PLUS_Z = {-0.9: 8.71735227960649, 0.0: 6.0, 0.9: 2.32088304176189}
PHOTON_PLUS_Z = {-0.9: 3.91026793910304, 0.0: 3.0, 0.9: 1.55785462742338}


def conventional_isco(mass, spin_param, prograde):
    """compact-common's labels: spin magnitude, prograde = co-rotating."""
    a_star = abs(spin_param) / (LUTS.G * mass / LUTS.C2)
    z1 = 1.0 + (1.0 - a_star**2) ** (1.0 / 3.0) * (
        (1.0 + a_star) ** (1.0 / 3.0) + (1.0 - a_star) ** (1.0 / 3.0)
    )
    z2 = math.sqrt(3.0 * a_star**2 + z1**2)
    root = math.sqrt((3.0 - z1) * (3.0 + z1 + 2.0 * z2))
    return (LUTS.G * mass / LUTS.C2) * (3.0 + z2 - root if prograde else 3.0 + z2 + root)


def conventional_photon(mass, spin_param, prograde):
    a_star = abs(spin_param) / (LUTS.G * mass / LUTS.C2)
    angle = (2.0 / 3.0) * math.acos(-a_star if prograde else a_star)
    return 2.0 * (LUTS.G * mass / LUTS.C2) * (1.0 + math.cos(angle))


CONVENTIONAL_REFS = {"kerr_isco": conventional_isco, "kerr_photon_orbit": conventional_photon}


class SignedSpinGenerators(unittest.TestCase):
    def check_paths(self, refs):
        for a_star, expected in ISCO_PLUS_Z.items():
            a = a_star * M_GEOM
            isco_luts, _ = LUTS.resolve_isco(MASS, a, True, refs)
            isco_tables = TABLES.resolve_isco(MASS, a, True, refs)
            self.assertAlmostEqual(isco_luts / M_GEOM, expected, delta=1e-9, msg=a_star)
            self.assertAlmostEqual(isco_tables / M_GEOM, expected, delta=1e-9, msg=a_star)
            photon_luts = LUTS.resolve_photon_orbit(MASS, a, True, refs)
            photon_tables = TABLES.resolve_photon_orbit(MASS, a, True, refs)
            self.assertAlmostEqual(photon_luts / M_GEOM, PHOTON_PLUS_Z[a_star], delta=1e-9)
            self.assertAlmostEqual(photon_tables / M_GEOM, PHOTON_PLUS_Z[a_star], delta=1e-9)
            # phi -> -phi: the -z orbit at a equals the +z orbit at -a.
            retro, _ = LUTS.resolve_isco(MASS, a, False, refs)
            self.assertAlmostEqual(retro / M_GEOM, ISCO_PLUS_Z[-a_star], delta=1e-9)

    def test_cleanroom_path(self):
        self.check_paths(None)

    def test_conventional_api_through_adapter(self):
        self.check_paths(CONVENTIONAL_REFS)

    def test_conventional_api_without_adapter_takes_co_rotating_branch(self):
        # The bug the adapter removes: prograde=True with a* = -0.9 gives 2.32 M.
        raw = conventional_isco(MASS, -0.9 * M_GEOM, True) / M_GEOM
        self.assertAlmostEqual(raw, ISCO_PLUS_Z[0.9], delta=1e-9)

    def test_zamo_redshift(self):
        # (a*, r / M, z): mpmath 1 / sqrt(Sigma Delta / A) - 1 at the equator.
        cases = [
            (0.9, 3.0, 0.64819156443383915),
            (0.9, 6.0, 0.2225214295493458),
            (0.9, 1.8, 2.3166247903553998),  # inside the ergosphere (r_ergo = 2 M)
            (0.0, 6.0, 1.0 / math.sqrt(1.0 - 2.0 / 6.0) - 1.0),
        ]
        for module in (LUTS, TABLES):
            for a_star, r_over_m, expected in cases:
                z = module.kerr_redshift_equatorial(r_over_m * M_GEOM, MASS, a_star * M_GEOM)
                self.assertAlmostEqual(z, expected, delta=1e-12, msg=(a_star, r_over_m))
            r_plus = (1.0 + math.sqrt(1.0 - 0.81)) * M_GEOM
            self.assertTrue(math.isinf(module.kerr_redshift_equatorial(r_plus, MASS, 0.9 * M_GEOM)))

    def test_validation_redshift_is_finite_and_capped(self):
        # A range reaching the horizon writes the cap, never inf or nan.
        r_plus = (1.0 + math.sqrt(1.0 - 0.81)) * M_GEOM
        for r in (0.5 * r_plus, r_plus, 1.0000001 * r_plus, 3.0 * M_GEOM):
            z = TABLES.capped_redshift(TABLES.kerr_redshift_equatorial(r, MASS, 0.9 * M_GEOM))
            self.assertTrue(math.isfinite(z), msg=r)
            self.assertLessEqual(z, TABLES.REDSHIFT_CAP)
            self.assertGreaterEqual(z, 0.0)
        self.assertEqual(TABLES.capped_redshift(math.inf), 10.0)
        self.assertEqual(TABLES.capped_redshift(math.nan), 10.0)
        self.assertAlmostEqual(TABLES.capped_redshift(0.648), 0.648)

    def test_installed_compact_common_agrees(self):
        refs = LUTS.compact_common_refs()
        if refs is None:
            self.skipTest("compact-common is not importable")
        self.check_paths(refs)


if __name__ == "__main__":
    unittest.main()
