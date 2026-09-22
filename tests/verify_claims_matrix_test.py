"""Keep configured applicability separate from missing evidence and test execution."""

import copy
import importlib.util
import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

VERIFIER_PATH = Path(__file__).resolve().parents[1] / "scripts" / "verify_claims_matrix.py"
SPEC = importlib.util.spec_from_file_location("verify_claims_matrix", VERIFIER_PATH)
assert SPEC is not None and SPEC.loader is not None
VERIFIER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(VERIFIER)


class ClaimsMatrixTest(unittest.TestCase):
    def setUp(self):
        temporary = tempfile.TemporaryDirectory(prefix="claims-matrix-")
        self.addCleanup(temporary.cleanup)
        self.directory = Path(temporary.name)
        (self.directory / "physics.h").write_text("// Fixture evidence.\n")
        self.manifest = {
            "claims": [
                {
                    "id": "mixed_physics",
                    "claim": "CPU and CUDA implementation contracts.",
                    "status": "local-validation",
                    "files": ["physics.h"],
                    "tests": [
                        "cpu_validation",
                        {"name": "cuda_validation", "requires": ["ENABLE_CUDA"]},
                    ],
                }
            ]
        }

    def assess(self, option="OFF", tests=None, manifest=None):
        options = VERIFIER.parse_build_options(f"ENABLE_CUDA:BOOL={option}\n")
        claims = VERIFIER.assess_claims(
            self.manifest if manifest is None else manifest,
            self.directory,
            {"cpu_validation"} if tests is None else tests,
            options,
        )
        return claims, options

    def test_disabled_cuda_is_explicitly_inapplicable(self):
        claims, options = self.assess()
        claim = claims[0]
        self.assertTrue(claim["tests_ok"])
        self.assertEqual(claim["missing_tests"], [])
        self.assertEqual(claim["not_applicable_tests"], ["cuda_validation"])
        self.assertEqual(claim["registration_status"], "partially-applicable")
        self.assertEqual(options["ENABLE_CUDA"], {"raw": "OFF", "enabled": False})
        self.assertEqual(claim["test_requirements"][1]["requires"], {"ENABLE_CUDA": False})

    def test_enabled_cuda_keeps_its_test_mandatory(self):
        claims, _ = self.assess(option="ON")
        self.assertFalse(claims[0]["tests_ok"])
        self.assertEqual(claims[0]["missing_tests"], ["cuda_validation"])
        self.assertEqual(claims[0]["registration_status"], "missing-evidence")
        claims, _ = self.assess(option="ON", tests={"cpu_validation", "cuda_validation"})
        self.assertTrue(claims[0]["tests_ok"])
        self.assertEqual(claims[0]["registration_status"], "registered")

    def test_cuda_only_claim_is_not_reported_as_registered(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["claims"][0]["tests"].pop(0)
        claims, _ = self.assess(manifest=manifest, tests=set())
        self.assertEqual(claims[0]["registration_status"], "not-applicable")
        self.assertIsNone(claims[0]["tests_ok"])

    def test_cpu_tests_and_source_files_stay_mandatory(self):
        (self.directory / "physics.h").unlink()
        claims, _ = self.assess(tests=set())
        self.assertEqual(claims[0]["missing_tests"], ["cpu_validation"])
        self.assertEqual(claims[0]["missing_files"], ["physics.h"])
        self.assertFalse(claims[0]["files_ok"])
        self.assertFalse(claims[0]["tests_ok"])

    def test_unknown_or_malformed_build_requirement_fails_closed(self):
        for cache in (
            "",
            "ENABLE_CUDA:STRING=OFF\n",
            "ENABLE_CUDA:BOOL=misspelled\n",
            "ENABLE_CUDA:BOOL=OFF\nENABLE_CUDA:BOOL=ON\n",
        ):
            with self.subTest(cache=cache), self.assertRaises(ValueError):
                options = VERIFIER.parse_build_options(cache)
                VERIFIER.assess_claims(self.manifest, self.directory, {"cpu_validation"}, options)
        for requirement in (
            None,
            [],
            "ENABLE_CUDA",
            ["UNKNOWN_OPTION"],
            ["ENABLE_CUDA", "UNKNOWN_OPTION"],
            ["ENABLE_CUDA", "ENABLE_CUDA"],
        ):
            manifest = copy.deepcopy(self.manifest)
            manifest["claims"][0]["tests"][1]["requires"] = requirement
            with self.subTest(requirement=requirement), self.assertRaises(ValueError):
                self.assess(manifest=manifest)

    def test_manifest_cannot_erase_its_evidence_obligations(self):
        cases = [{}, {"claims": []}]
        for field, value in (("files", []), ("files", ["../physics.h"]), ("tests", [])):
            manifest = copy.deepcopy(self.manifest)
            manifest["claims"][0][field] = value
            cases.append(manifest)
        for manifest in cases:
            with self.subTest(manifest=manifest), self.assertRaises(ValueError):
                self.assess(manifest=manifest)

    def test_ctest_discovery_uses_structured_names_and_checks_errors(self):
        with patch.object(VERIFIER.shutil, "which", return_value="ctest"):
            inventory = subprocess.CompletedProcess(
                [], 0, '{"tests":[{"name":"cpu_validation"}]}', ""
            )
            with patch.object(VERIFIER, "run_command", return_value=inventory) as command:
                self.assertEqual(VERIFIER.parse_ctest(self.directory), {"cpu_validation"})
                self.assertIn("--show-only=json-v1", command.call_args.args[0])
            failures = (
                subprocess.CompletedProcess([], 1, "", "discovery failed"),
                subprocess.CompletedProcess([], 0, "invalid json", ""),
                subprocess.CompletedProcess([], 0, '{"tests":[{}]}', ""),
                subprocess.CompletedProcess([], 0, '{"tests":[{"name":"x"},{"name":"x"}]}', ""),
            )
            for failure in failures:
                with (
                    self.subTest(failure=failure),
                    patch.object(VERIFIER, "run_command", return_value=failure),
                    self.assertRaises((ValueError, RuntimeError)),
                ):
                    VERIFIER.parse_ctest(self.directory)
        with (
            patch.object(VERIFIER.shutil, "which", return_value=None),
            self.assertRaises(RuntimeError),
        ):
            VERIFIER.parse_ctest(self.directory)

    def test_cli_replaces_stale_success_report_on_discovery_failure(self):
        manifest = self.directory / "manifest.json"
        manifest.write_text(json.dumps(self.manifest))
        report = self.directory / "report.json"
        report.write_text('{"summary":{"missing_tests":0}}')
        result = subprocess.run(
            [
                sys.executable,
                str(VERIFIER_PATH),
                "--source-dir",
                str(self.directory),
                "--build-dir",
                str(self.directory),
                "--manifest",
                str(manifest),
                "--md-out",
                str(self.directory / "report.md"),
                "--json-out",
                str(report),
            ],
            capture_output=True,
            text=True,
            check=False,
            timeout=10,
        )
        self.assertEqual(result.returncode, 1, result.stderr)
        evidence = json.loads(report.read_text())
        self.assertIn("verification_error", evidence)
        self.assertNotIn("summary", evidence)
        self.assertEqual(evidence["execution_status"], "not-assessed")
        self.assertIn("CUDA device execution", (self.directory / "report.md").read_text())


if __name__ == "__main__":
    unittest.main(verbosity=2)
