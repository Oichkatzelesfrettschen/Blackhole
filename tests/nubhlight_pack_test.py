"""Exercise HDF5 packing through the CLI so layout and input checks cannot drift."""

import argparse
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from typing import ClassVar

import h5py
import numpy as np


class NubhlightPackTest(unittest.TestCase):
    packer: ClassVar[Path]

    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="nubhlight-pack-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        self.channels = ["rho", "u", "v1", "v2"]
        self.voxels = np.arange(12, dtype=np.float32).reshape(2, 3, 2, 1)
        self.values = self.voxels + np.arange(4, dtype=np.float32).reshape(1, 1, 1, 4) * 100

    def write_fixture(self, name, values, names=None):
        path = self.directory / f"{name}.h5"
        with h5py.File(path, "w") as fixture:
            dataset = fixture.create_dataset("/dump/P", data=values)
            if names is not None:
                dataset.attrs["vnams"] = names
        return path

    def run_packer(self, fixture, name, *arguments):
        output = self.directory / f"{name}.json"
        result = subprocess.run(
            [
                str(self.packer),
                "--input",
                str(fixture),
                "--dataset",
                "/dump/P",
                "--output",
                str(output),
                *arguments,
            ],
            cwd=self.directory,
            capture_output=True,
            text=True,
            timeout=30,
            check=False,
        )
        return result, output

    def assert_product(self, output, expected, channels, indices, layout):
        metadata = json.loads(output.read_text())
        payload = output.with_suffix(".bin").read_bytes()
        self.assertEqual(payload, np.asarray(expected, dtype=np.float32).tobytes())
        self.assertEqual(metadata["grid_dims"], list(expected.shape[:3]))
        self.assertEqual(metadata["channels"], channels)
        self.assertEqual(metadata["source_indices"], indices)
        self.assertEqual(metadata["layout"], layout)
        self.assertEqual(metadata["format"], "RGBA32F")
        self.assertEqual(metadata["schema_version"], 1)
        self.assertEqual(metadata["min"], expected.reshape(-1, 4).min(axis=0).tolist())
        self.assertEqual(metadata["max"], expected.reshape(-1, 4).max(axis=0).tolist())
        # FNV-1a hashes the stored bytes, including channel order and padding.
        checksum = 14695981039346656037
        for byte in payload:
            checksum = ((checksum ^ byte) * 1099511628211) & ((1 << 64) - 1)
        self.assertEqual(metadata["checksum_fnv1a64"], f"{checksum:016x}")
        return metadata

    def assert_rejected(self, fixture, name, *arguments):
        result, output = self.run_packer(fixture, name, *arguments)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertTrue(result.stderr.strip())
        self.assertNotIn("Wrote ", result.stdout)
        self.assertFalse(output.exists())
        self.assertFalse(output.with_suffix(".bin").exists())
        return result

    def test_channel_layouts_preserve_voxel_order(self):
        layouts = (
            ("channels-last", self.values, 3),
            ("channels-first", np.moveaxis(self.values, 3, 0), 0),
        )
        for layout, values, channel_dimension in layouts:
            with self.subTest(layout=layout):
                fixture = self.write_fixture(layout, values, self.channels)
                result, output = self.run_packer(fixture, layout)
                self.assertEqual(result.returncode, 0, result.stderr)
                metadata = self.assert_product(
                    output, self.values, self.channels, [0, 1, 2, 3], layout
                )
                self.assertEqual(metadata["dataset_dims"], list(values.shape))
                self.assertEqual(metadata["channel_dim_index"], channel_dimension)

    def test_scalar_channels_have_defined_padding(self):
        scalar = self.voxels[..., 0]
        fixture = self.write_fixture("scalar", scalar)
        result, output = self.run_packer(fixture, "scalar")
        self.assertEqual(result.returncode, 0, result.stderr)
        expected = np.zeros_like(self.values)
        expected[..., 0] = scalar
        expected[..., 3] = 1
        metadata = self.assert_product(
            output, expected, ["scalar", "unused", "unused", "unused"], [0, -1, -1, -1], "scalar"
        )
        self.assertNotIn("channel_dim_index", metadata)
        self.assertEqual(metadata["fill"], [0, 0, 0, 1])

    def test_field_and_index_subsets_preserve_requested_order(self):
        cases = (
            ("fields", self.values, "--fields", "u,rho", [1, 0], "channels-last"),
            (
                "indices",
                np.moveaxis(self.values, 3, 0),
                "--indices",
                "3,1",
                [3, 1],
                "channels-first",
            ),
        )
        for name, values, option, selection, indices, layout in cases:
            with self.subTest(selection=name):
                fixture = self.write_fixture(name, values, self.channels)
                result, output = self.run_packer(fixture, name, option, selection)
                self.assertEqual(result.returncode, 0, result.stderr)
                expected = np.zeros_like(self.values)
                expected[..., :2] = self.values[..., indices]
                expected[..., 3] = 1
                metadata = self.assert_product(
                    output,
                    expected,
                    [self.channels[index] for index in indices] + ["unused", "unused"],
                    [*indices, -1, -1],
                    layout,
                )
                self.assertEqual(metadata["fill"], [0, 0, 0, 1])

    def test_unreadable_attribute_is_an_error(self):
        fixture = self.write_fixture("numeric-names", self.values, np.arange(4, dtype=np.int32))
        result = self.assert_rejected(fixture, "numeric-names")
        self.assertIn("Packing failed:", result.stderr)

    def test_attribute_count_must_match_selected_dimension(self):
        fixture = self.write_fixture("short-names", self.values, ["rho", "u"])
        result = self.assert_rejected(fixture, "short-names", "--layout", "channels-last")
        self.assertIn("vnams count differs", result.stderr)

    def test_invalid_rank_and_selectors_are_rejected(self):
        invalid_rank = self.write_fixture("rank-two", np.zeros((3, 4), dtype=np.float32))
        self.assert_rejected(invalid_rank, "rank-two")
        fixture = self.write_fixture("channels", self.values, self.channels)
        cases = (
            ("exclusive-selectors", "--fields", "rho", "--indices", "0"),
            ("unknown-field", "--fields", "absent"),
            ("invalid-index", "--indices", "99"),
            ("invalid-layout", "--layout", "invalid"),
            ("too-many-channels", "--indices", "0,1,2,3,0"),
        )
        for name, *arguments in cases:
            with self.subTest(case=name):
                self.assert_rejected(fixture, name, *arguments)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--packer", required=True, type=Path)
    arguments = parser.parse_args()
    NubhlightPackTest.packer = arguments.packer.resolve(strict=True)
    unittest.main(argv=[__file__], verbosity=2)


if __name__ == "__main__":
    main()
