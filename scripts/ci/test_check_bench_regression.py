"""Regression coverage for the physics_bench baseline comparison."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CHECKER = Path(__file__).resolve().parent.parent / "check_bench_regression.py"


def payload(**timings: object) -> dict:
    return {"results": [{"name": name, "avg_ms": ms} for name, ms in timings.items()]}


class BenchRegressionTests(unittest.TestCase):
    def compare(self, baseline: dict, current: dict | str) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as directory:
            base_path = Path(directory) / "baseline.json"
            current_path = Path(directory) / "current.json"
            base_path.write_text(json.dumps(baseline), encoding="utf-8")
            text = current if isinstance(current, str) else json.dumps(current)
            current_path.write_text(text, encoding="utf-8")
            return subprocess.run(
                [sys.executable, str(CHECKER), "--baseline", str(base_path), str(current_path)],
                check=False,
                capture_output=True,
                text=True,
            )

    def test_within_threshold_passes(self) -> None:
        result = self.compare(payload(a=10.0), payload(a=10.4))
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_slowdown_fails(self) -> None:
        result = self.compare(payload(a=10.0), payload(a=11.0))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("REGRESSION: a", result.stdout)

    def test_non_finite_current_timing_fails(self) -> None:
        # json.load reads NaN and Infinity as floats; null is physics_bench's form.
        for literal in ("NaN", "Infinity", "-Infinity", "null"):
            with self.subTest(literal=literal):
                text = f'{{"results": [{{"name": "a", "avg_ms": {literal}}}]}}'
                result = self.compare(payload(a=10.0), text)
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("INVALID: a", result.stdout)
                self.assertNotIn("ok: a", result.stdout)

    def test_non_finite_or_zero_baseline_timing_fails(self) -> None:
        for bad in (float("nan"), float("inf"), 0.0, None):
            with self.subTest(bad=bad):
                result = self.compare(payload(a=bad), payload(a=10.0))
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("INVALID: a", result.stdout)

    def test_missing_entry_fails(self) -> None:
        result = self.compare(payload(a=10.0, b=5.0), payload(a=10.0))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("MISSING: b", result.stdout)

    def test_new_entry_is_reported_not_failed(self) -> None:
        result = self.compare(payload(a=10.0), payload(a=10.0, c=1.0))
        self.assertEqual(result.returncode, 0, result.stdout)
        self.assertIn("NEW: c", result.stdout)


if __name__ == "__main__":
    unittest.main()
