"""Check HDF5 traversal, JSON metadata, and inspector CLI failure boundaries."""

import argparse
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import ClassVar

import h5py


class NubhlightInspectTest(unittest.TestCase):
    inspector: ClassVar[Path]

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="nubhlight-inspect-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)

    def run_inspector(self, fixture, *arguments):
        return subprocess.run(
            [str(self.inspector), "--input", str(fixture), *arguments],
            cwd=self.directory,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )

    def test_depth_first_order_and_bare_output_filename(self):
        fixture = self.directory / "nested.h5"
        paths = ["/a", "/b/a", "/b/b/a", "/b/c", "/z"]
        expected = []
        with h5py.File(fixture, "w") as data:
            for index, name in enumerate(paths):
                values = list(range(index + 1))
                dataset = data.create_dataset(name, data=values)
                dataset.attrs["vnams"] = ["rho", "u"]
                expected.append({"path": name, "dims": [index + 1], "vnams": ["rho", "u"]})
        result = self.run_inspector(fixture)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(json.loads(result.stdout), {"input": str(fixture), "datasets": expected})
        written = self.run_inspector(fixture, "--output", "metadata.json")
        self.assertEqual(written.returncode, 0, written.stderr)
        self.assertEqual((self.directory / "metadata.json").read_text(), result.stdout)

    def test_json_control_characters(self):
        fixture = self.directory / "controls.h5"
        name = "/control\x01\b\f"
        channel = 'rho\x01\b\f\t\n\\"'
        with h5py.File(fixture, "w") as data:
            data.create_dataset(name, data=[1.0]).attrs["vnams"] = [channel]
        result = self.run_inspector(fixture)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            json.loads(result.stdout)["datasets"],
            [{"path": name, "dims": [1], "vnams": [channel]}],
        )

    def test_malformed_metadata_is_rejected_before_output(self):
        fixture = self.directory / "malformed.h5"
        with h5py.File(fixture, "w") as data:
            data.create_dataset("/P", data=[1.0]).attrs["vnams"] = [1, 2, 3]
        result = self.run_inspector(fixture, "--output", "metadata.json")
        self.assertEqual(result.returncode, 1)
        self.assertTrue(result.stderr.strip())
        self.assertEqual(result.stdout, "")
        self.assertFalse((self.directory / "metadata.json").exists())

    @unittest.skipUnless(Path("/dev/full").exists(), "requires a device that rejects writes")
    def test_late_write_failure_returns_error(self):
        fixture = self.directory / "valid.h5"
        with h5py.File(fixture, "w") as data:
            data.create_dataset("/P", data=[1.0])
        result = self.run_inspector(fixture, "--output", "/dev/full")
        self.assertEqual(result.returncode, 1)
        self.assertIn("Failed to complete output", result.stderr)

    def test_missing_input_returns_error(self):
        result = self.run_inspector(self.directory / "missing.h5")
        self.assertEqual(result.returncode, 1)
        self.assertTrue(result.stderr.strip())
        self.assertEqual(result.stdout, "")

    def test_deep_group_traversal(self):
        fixture = self.directory / "deep.h5"
        depth = 1024
        with h5py.File(fixture, "w") as data:
            group = data
            for _ in range(depth):
                group = group.create_group("g")
            group.create_dataset("P", data=[1.0])
        result = self.run_inspector(fixture)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(
            json.loads(result.stdout)["datasets"],
            [{"path": "/g" * depth + "/P", "dims": [1]}],
        )


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--inspector", required=True, type=Path)
    arguments = parser.parse_args()
    NubhlightInspectTest.inspector = arguments.inspector.resolve(strict=True)
    unittest.main(argv=[__file__], verbosity=2)


if __name__ == "__main__":
    main()
