"""Hold scripts/generate_luts.py to the runtime's signed-spin disk convention."""

import csv
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

GENERATOR_PATH = Path(__file__).resolve().parents[1] / "scripts" / "generate_luts.py"
SPEC = importlib.util.spec_from_file_location("generate_luts", GENERATOR_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"Cannot load LUT generator: {GENERATOR_PATH}")
GENERATOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GENERATOR
SPEC.loader.exec_module(GENERATOR)


def read_values(path: Path) -> list[float]:
    with path.open(newline="") as handle:
        return [float(row["value"]) for row in csv.DictReader(handle)]


class SignedSpinLuts(unittest.TestCase):
    """At --spin -0.9 the disk is retrograde: ISCO 8.717 M (r_in = 4.358 r_s)."""

    def generate(self, spin: float) -> tuple[list[float], list[float], dict]:
        with tempfile.TemporaryDirectory(prefix="generate-luts-") as directory:
            out = Path(directory)
            subprocess.run(
                [
                    sys.executable,
                    str(GENERATOR_PATH),
                    "--spin",
                    str(spin),
                    "--size",
                    "64",
                    "--out-dir",
                    str(out),
                ],
                check=True,
                capture_output=True,
                text=True,
            )
            meta = json.loads((out / "lut_meta.json").read_text(encoding="utf-8"))
            return (
                read_values(out / "emissivity_lut.csv"),
                read_values(out / "redshift_lut.csv"),
                meta,
            )

    def test_domain_starts_at_the_signed_isco(self):
        for spin in (0.9, -0.9):
            _, _, meta = self.generate(spin)
            self.assertAlmostEqual(
                2.0 * meta["r_in_over_rs"], GENERATOR.page_thorne_isco(spin), places=9
            )
            self.assertEqual(meta["prograde"], spin >= 0.0)

    def test_emissivity_is_nonzero_across_the_domain(self):
        for spin in (0.9, -0.9):
            emissivity, _, _ = self.generate(spin)
            # The first sample is the zero-torque ISCO edge; every later one emits.
            self.assertEqual(emissivity[0], 0.0)
            self.assertTrue(all(value > 0.0 for value in emissivity[1:]), spin)
            self.assertAlmostEqual(max(emissivity), 1.0, places=12)

    def test_redshift_is_the_signed_emitter_at_the_isco(self):
        for spin in (0.9, -0.9):
            _, redshift, _ = self.generate(spin)
            r_isco = GENERATOR.page_thorne_isco(spin)
            inv_r32 = r_isco**-1.5
            u_t = (1.0 + spin * inv_r32) / (1.0 - 3.0 / r_isco + 2.0 * spin * inv_r32) ** 0.5
            self.assertAlmostEqual(redshift[0], min(u_t - 1.0, 10.0), places=9)
            self.assertGreater(redshift[0], redshift[-1])


if __name__ == "__main__":
    unittest.main()
