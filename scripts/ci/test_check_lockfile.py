"""Regression coverage for exported recipes and dependency drift."""

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path


class LockfileTests(unittest.TestCase):
    def compare(self, committed: dict, resolved: dict) -> int:
        with tempfile.TemporaryDirectory() as directory:
            paths = [Path(directory) / name for name in ("committed", "resolved")]
            for path, data in zip(paths, (committed, resolved), strict=True):
                path.write_text(json.dumps(data), encoding="utf-8")
            return subprocess.run(
                [
                    sys.executable,
                    str(Path(__file__).with_name("check_lockfile.py")),
                    *map(str, paths),
                ],
                check=False,
                capture_output=True,
            ).returncode

    def test_export_timestamp_preserves_identity(self) -> None:
        self.assertEqual(
            self.compare(
                {"requires": ["imgui/1.92.5-docking#abc%1.2"]},
                {"requires": ["imgui/1.92.5-docking#abc%9.9"]},
            ),
            0,
        )

    def test_version_revision_and_removal_fail(self) -> None:
        for changed in (["imgui/1.92.5-docking#def%1.2"], ["imgui/1.92.6#abc%1.2"], []):
            with self.subTest(changed=changed):
                self.assertEqual(
                    self.compare(
                        {"requires": ["imgui/1.92.5-docking#abc%1.2"]},
                        {"requires": changed},
                    ),
                    1,
                )

    def test_build_dependency_drift_fails(self) -> None:
        self.assertEqual(
            self.compare(
                {"build_requires": ["cmake/3.31.6#abc%1.2"]},
                {"build_requires": ["cmake/3.31.6#def%1.2"]},
            ),
            1,
        )

    def test_lock_metadata_drift_fails(self) -> None:
        self.assertEqual(self.compare({"version": "0.5"}, {"version": "0.6"}), 1)


if __name__ == "__main__":
    unittest.main()
