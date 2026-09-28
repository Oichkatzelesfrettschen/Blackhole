"""Keep configured applicability separate from missing evidence and test execution."""

import copy
import importlib.util
import json
import os
import re
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
TRUTH_PATH = VERIFIER_PATH.with_name("repo_truth.py")
TRUTH_SPEC = importlib.util.spec_from_file_location("repo_truth", TRUTH_PATH)
assert TRUTH_SPEC is not None and TRUTH_SPEC.loader is not None
TRUTH = importlib.util.module_from_spec(TRUTH_SPEC)
TRUTH_SPEC.loader.exec_module(TRUTH)


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
                    "required_evidence_class": "formula-unit",
                    "files": ["physics.h"],
                    "tests": [
                        {"name": "cpu_validation", "evidence_class": "formula-unit"},
                        {
                            "name": "cuda_validation",
                            "evidence_class": "formula-unit",
                            "requires": ["ENABLE_CUDA"],
                        },
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

    def test_mock_cannot_satisfy_renderer_output_claim(self):
        manifest = copy.deepcopy(self.manifest)
        claim = manifest["claims"][0]
        claim["required_evidence_class"] = "render-output"
        claim["tests"][0]["evidence_class"] = "mock-observable"
        claims, _ = self.assess(manifest=manifest)
        self.assertEqual(claims[0]["registration_status"], "inadequate-evidence")
        self.assertEqual(claims[0]["matching_evidence"], [])
        claim["tests"][0]["evidence_class"] = "render-output"
        claims, _ = self.assess(manifest=manifest)
        self.assertEqual(claims[0]["registration_status"], "partially-applicable")

    def test_canonical_eht_shadow_is_mock_evidence(self):
        manifest_path = VERIFIER_PATH.parents[1] / "docs" / "physics" / "claims_evidence.json"
        manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
        claim = next(entry for entry in manifest["claims"] if entry["id"] == "eht_observables")
        shadow = next(entry for entry in claim["tests"] if entry["name"] == "eht_shadow_validation")
        self.assertEqual(shadow["evidence_class"], "mock-observable")
        self.assertNotEqual(claim["required_evidence_class"], "render-output")

    def test_repo_truth_records_executed_skips(self):
        self.assertEqual(TRUTH.recent_ctest_execution(self.directory)["status"], "not-assessed")
        log = self.directory / "Testing" / "Temporary" / "LastTest.log"
        log.parent.mkdir(parents=True)
        log.write_text(
            "1/2 Testing: gpu_parity\n1/2 Test: gpu_parity\n"
            "Output:\nSkipped without GL context\nTest Skipped.\n"
            "2/2 Testing: cpu_validation\n2/2 Test: cpu_validation\n"
            "Output:\nPASS\nTest Pass Reason:\nRequired regular expression found.\n",
            encoding="utf-8",
        )
        execution = TRUTH.recent_ctest_execution(self.directory)
        self.assertEqual(execution["tests"], {"gpu_parity": "skipped", "cpu_validation": "passed"})
        self.assertEqual(Path(execution["log"]).read_bytes(), log.read_bytes())
        log.write_text("Start testing:\nEnd testing:\n", encoding="utf-8")
        self.assertEqual(TRUTH.recent_ctest_execution(self.directory)["tests"], execution["tests"])

    def test_documentation_paths_are_portable(self):
        source_dir = VERIFIER_PATH.parents[1]
        documentation = list(source_dir.glob("*.md"))
        for directory in ("docs", "blender", "shader", "rocq", "bench", "tools", "cmake", "assets"):
            documentation.extend((source_dir / directory).rglob("*.md"))
        local_path = re.compile(r"/(?:home|Users)/[A-Za-z0-9_.-]+/")
        dangling = [
            str(path.relative_to(source_dir))
            for path in documentation
            if local_path.search(path.read_text(encoding="utf-8"))
        ]
        self.assertEqual(dangling, [])

    def test_release_summary_declares_both_product_boundaries(self):
        source_dir = VERIFIER_PATH.parents[1]
        summary_path = source_dir / "docs" / "developer-guide" / "release-evidence.json"
        summary = json.loads(summary_path.read_text(encoding="utf-8"))
        self.assertEqual(summary["schema_version"], 1)
        self.assertEqual(
            set(summary["products"]),
            {"blackhole_simulator_workbench", "singularity_gororoba"},
        )
        simulator = summary["products"]["blackhole_simulator_workbench"]
        game = summary["products"]["singularity_gororoba"]
        self.assertEqual(
            set(simulator) - {"maturity"},
            {
                "active_default_renderer_contract",
                "output_validation_scenes_metrics",
                "backend_availability_parity",
                "performance_tiers",
                "physical_approximations",
            },
        )
        self.assertEqual(
            set(game) - {"maturity"},
            {
                "authoritative_game_session_type",
                "deterministic_test_replay_status",
                "save_schema_version",
                "canonical_scenario_completion_tests",
                "ui_screenshot_status",
            },
        )
        save_source = (source_dir / "src/game/save_format.h").read_text(encoding="utf-8")
        version = re.search(r"K_SAVE_FORMAT_VERSION\s*=\s*(\d+)", save_source)
        self.assertIsNotNone(version)
        self.assertEqual(game["save_schema_version"]["value"], int(version.group(1)))
        contract_source = (source_dir / "src/render/renderer_contract.h").read_text(
            encoding="utf-8"
        )
        self.assertIn("RenderBackend backend = RenderBackend::Fragment;", contract_source)
        classifications = {
            "measured-fact",
            "local-inference",
            "approximation",
            "unvalidated-roadmap",
        }
        for product in summary["products"].values():
            self.assertIn("maturity", product)
            for name, obligation in product.items():
                if name == "maturity":
                    continue
                self.assertIn(obligation["classification"], classifications)
                self.assertIn("value", obligation)
                source = obligation["source"]
                if not source.startswith("build/"):
                    self.assertTrue((source_dir / source).exists(), source)

    def test_missing_or_unknown_evidence_class_fails_closed(self):
        for field in ("required_evidence_class", "evidence_class"):
            manifest = copy.deepcopy(self.manifest)
            target = (
                manifest["claims"][0]
                if field == "required_evidence_class"
                else manifest["claims"][0]["tests"][0]
            )
            for value in (None, "renderer-output"):
                with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                    target[field] = value
                    self.assess(manifest=manifest)

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

    def test_cli_rejects_registered_but_inadequate_evidence(self):
        manifest = copy.deepcopy(self.manifest)
        manifest["claims"][0]["required_evidence_class"] = "render-output"
        manifest["claims"][0]["tests"][0]["evidence_class"] = "mock-observable"
        manifest_path = self.directory / "manifest.json"
        manifest_path.write_text(json.dumps(manifest), encoding="utf-8")
        (self.directory / "CMakeCache.txt").write_text("ENABLE_CUDA:BOOL=OFF\n", encoding="utf-8")
        ctest = self.directory / "ctest"
        ctest.write_text('#!/bin/sh\nprintf \'{"tests":[{"name":"cpu_validation"}]}\\n\'\n')
        ctest.chmod(0o755)
        json_out = self.directory / "report.json"
        result = subprocess.run(
            [
                sys.executable,
                str(VERIFIER_PATH),
                "--source-dir",
                str(self.directory),
                "--build-dir",
                str(self.directory),
                "--manifest",
                str(manifest_path),
                "--md-out",
                str(self.directory / "report.md"),
                "--json-out",
                str(json_out),
            ],
            capture_output=True,
            text=True,
            check=False,
            env={**os.environ, "PATH": f"{self.directory}:{os.environ['PATH']}"},
        )
        self.assertEqual(result.returncode, 1)
        self.assertEqual(json.loads(json_out.read_text())["summary"]["inadequate_evidence"], 1)


if __name__ == "__main__":
    unittest.main(verbosity=2)
