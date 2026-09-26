"""Regression coverage for the physics_bench baseline comparison."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

CHECKER = Path(__file__).resolve().parent.parent / "check_bench_regression.py"


CONFIG = {"rays": 4000, "steps": 2000, "iterations": 10, "warmup": 1, "gpu_enabled": False}


def payload(config: dict | None = None, **timings: object) -> dict:
    return {
        "config": dict(CONFIG) if config is None else config,
        "results": [{"name": name, "avg_ms": ms, "iterations": 10} for name, ms in timings.items()],
    }


class BenchRegressionTests(unittest.TestCase):
    def compare(
        self, baseline: dict | None, *currents: dict | str, extra: tuple[str, ...] = ()
    ) -> subprocess.CompletedProcess:
        """Run the checker; baseline None leaves the baseline file absent."""
        with tempfile.TemporaryDirectory() as directory:
            base_path = Path(directory) / "baseline.json"
            if baseline is not None:
                base_path.write_text(json.dumps(baseline), encoding="utf-8")
            paths = []
            for index, current in enumerate(currents):
                path = Path(directory) / f"current{index}.json"
                text = current if isinstance(current, str) else json.dumps(current)
                path.write_text(text, encoding="utf-8")
                paths.append(str(path))
            return subprocess.run(
                [sys.executable, str(CHECKER), "--baseline", str(base_path), *extra, *paths],
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
                entry = f'{{"name": "a", "avg_ms": {literal}, "iterations": 10}}'
                text = f'{{"config": {json.dumps(CONFIG)}, "results": [{entry}]}}'
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

    def test_zeroed_result_fails(self) -> None:
        # physics_bench once reported a failed GPU init as avg_ms 0, iterations 0.
        cases = {
            "zeroed": {"name": "g", "avg_ms": 0.0, "iterations": 0},
            "zero time": {"name": "g", "avg_ms": 0.0, "iterations": 20},
            "zero iterations": {"name": "g", "avg_ms": 1.0, "iterations": 0},
            "no iterations": {"name": "g", "avg_ms": 1.0},
        }
        for label, entry in cases.items():
            with self.subTest(case=label):
                result = self.compare(payload(g=1.0), {"config": CONFIG, "results": [entry]})
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("INVALID: g", result.stdout)
                self.assertNotIn("ok: g", result.stdout)

    def test_missing_entry_is_checked_per_file(self) -> None:
        # b in the first file does not excuse its absence from the second.
        result = self.compare(payload(a=10.0, b=5.0), payload(a=10.0, b=5.0), payload(a=10.0))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("MISSING: b", result.stdout)
        self.assertIn("current1.json", result.stdout)

    def test_allow_missing_still_validates_current(self) -> None:
        zeroed = {"config": CONFIG, "results": [{"name": "g", "avg_ms": 0.0, "iterations": 0}]}
        result = self.compare(None, zeroed, extra=("--allow-missing",))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("INVALID: g", result.stdout)
        result = self.compare(None, payload(g=1.0), extra=("--allow-missing",))
        self.assertEqual(result.returncode, 0, result.stdout)
        result = self.compare(None, payload(g=1.0))
        self.assertEqual(result.returncode, 2, result.stdout)

    def test_record_refuses_invalid_run(self) -> None:
        zeroed = {"config": CONFIG, "results": [{"name": "g", "avg_ms": 0.0, "iterations": 0}]}
        result = self.compare(None, zeroed, extra=("--record",))
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("not recording", result.stdout)

    def test_threshold_must_be_finite_and_non_negative(self) -> None:
        for bad in ("nan", "inf", "-0.1", "abc"):
            with self.subTest(threshold=bad):
                result = self.compare(
                    payload(a=10.0), payload(a=10.0), extra=(f"--threshold={bad}",)
                )
                self.assertEqual(result.returncode, 2, result.stderr)
                self.assertIn("--threshold", result.stderr)
        result = self.compare(payload(a=10.0), payload(a=10.0), extra=("--threshold=0",))
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_workload_config_mismatch_fails(self) -> None:
        for key, value in (("rays", 2000), ("iterations", 5), ("gpu_enabled", True)):
            with self.subTest(key=key):
                config = dict(CONFIG, **{key: value})
                result = self.compare(payload(a=10.0), payload(config, a=10.0))
                self.assertEqual(result.returncode, 1, result.stdout)
                self.assertIn("CONFIG:", result.stdout)
                self.assertIn(key, result.stdout)
                self.assertNotIn("ok: a", result.stdout)
        no_config = {"results": [{"name": "a", "avg_ms": 10.0, "iterations": 10}]}
        result = self.compare(payload(a=10.0), no_config)
        self.assertEqual(result.returncode, 1, result.stdout)
        self.assertIn("config object is missing", result.stdout)

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
