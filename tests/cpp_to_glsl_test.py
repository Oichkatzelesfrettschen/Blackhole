"""Verify shader-name compatibility without claiming GLSL syntax validation."""

import importlib.util
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

GENERATOR_PATH = Path(__file__).resolve().parents[1] / "scripts" / "cpp_to_glsl.py"
SPEC = importlib.util.spec_from_file_location("cpp_to_glsl", GENERATOR_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"Cannot load GLSL generator: {GENERATOR_PATH}")
GENERATOR = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GENERATOR
SPEC.loader.exec_module(GENERATOR)


class ShaderNamingCompatibility(unittest.TestCase):
    def test_synthetic_header_preserves_public_interfaces(self):
        source = """
inline constexpr double C_KM_S = 299792.458;
struct MetricComponents {
    double gTt;
    double gRr;
};
[[nodiscard]] inline double schwarzschildGTt(double radius, double mass) noexcept {
    return -(1.0 - 2.0 * mass / radius);
}
[[nodiscard]] inline double probe(MetricComponents metric, double inputValue) noexcept {
    return metric.gTt + metric.gRr + schwarzschildGTt(10.0, 1.0) + C_KM_S + inputValue;
}
"""
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            source_dir = root / "source"
            output_dir = root / "output"
            source_dir.mkdir()
            output_dir.mkdir()
            (source_dir / "fixture.hpp").write_text(source, encoding="utf-8")
            transpiler = GENERATOR.CPPToGLSLTranspiler(source_dir, output_dir, verbose=False)
            result = transpiler.transpile_file("fixture.hpp")
            self.assertEqual(result, output_dir / "fixture.glsl")
            self.assertEqual(transpiler.transpilation_stats["files_failed"], 0)
            generated = result.read_text(encoding="utf-8")
        self.assertIn("const float c_km_s = 299792.458;", generated)
        self.assertIn("float g_tt;", generated)
        self.assertIn("float g_rr;", generated)
        self.assertIn("float schwarzschild_g_tt(float radius, float mass)", generated)
        self.assertIn("metric.g_tt + metric.g_rr + schwarzschild_g_tt(10.0, 1.0)", generated)
        self.assertIn("+ c_km_s + inputValue;", generated)
        self.assertIn("float probe(MetricComponents metric, float inputValue)", generated)

    def test_all_aliases_preserve_identifier_boundaries(self):
        for cpp_name, glsl_name in GENERATOR.GLSL_PUBLIC_NAMES.items():
            with self.subTest(cpp_name=cpp_name):
                source = f"{cpp_name} {cpp_name}Suffix prefix_{cpp_name}"
                expected = f"{glsl_name} {cpp_name}Suffix prefix_{cpp_name}"
                self.assertEqual(GENERATOR.preserve_glsl_public_names(source), expected)

    def test_comments_and_literals_retain_original_spelling(self):
        fragments = [
            "// schwarzschildGTt C_KM_S gTt",
            "/* schwarzschildGTt\nC_KM_S gTt */",
            '"schwarzschildGTt C_KM_S gTt"',
            r'"escaped \" schwarzschildGTt"',
            "'k'",
            'R"(schwarzschildGTt "nested" C_KM_S)"',
            'u8R"marker(gTt\n"nested" C_KM_S)marker"',
        ]
        for fragment in fragments:
            with self.subTest(fragment=fragment):
                self.assertEqual(GENERATOR.preserve_glsl_public_names(fragment), fragment)

    def test_unmapped_identifiers_remain_unchanged(self):
        source = "unmappedFunction(inputValue, StateVector, metric.untouchedMember);"
        self.assertEqual(GENERATOR.preserve_glsl_public_names(source), source)


class GeneratorExitStatus(unittest.TestCase):
    def run_generator(self, broken_input):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            script = root / "scripts" / GENERATOR_PATH.name
            script.parent.mkdir()
            script.write_bytes(GENERATOR_PATH.read_bytes())
            inputs = root / "src" / "physics" / "verified"
            inputs.mkdir(parents=True)
            originals = GENERATOR_PATH.parents[1] / "src" / "physics" / "verified"
            for header in originals.glob("*.hpp"):
                destination = inputs / header.name
                if header.name == "eos.hpp" and broken_input == "missing":
                    continue
                if header.name == "eos.hpp" and broken_input == "read-error":
                    destination.mkdir()
                    continue
                destination.write_text(
                    "[[nodiscard]] constexpr double fixtureRadius(double mass) noexcept "
                    "{ return 2.0 * mass; }\n",
                    encoding="utf-8",
                )
            result = subprocess.run(
                [sys.executable, str(script)], capture_output=True, text=True, check=False
            )
            outputs = sorted(
                path.name for path in (root / "shader/include/verified").glob("*.glsl")
            )
        return result, outputs

    def test_missing_input_returns_failure_and_retains_other_outputs(self):
        result, outputs = self.run_generator("missing")
        self.assertEqual(result.returncode, 1)
        self.assertIn("eos.hpp not found", result.stderr)
        self.assertRegex(result.stdout, r"Files failed:\s+1")
        self.assertEqual(len(outputs), 9)
        self.assertNotIn("eos.glsl", outputs)

    def test_translation_exception_returns_failure_and_retains_other_outputs(self):
        result, outputs = self.run_generator("read-error")
        self.assertEqual(result.returncode, 1)
        self.assertIn("[ERROR] Failed to transpile eos.hpp:", result.stderr)
        self.assertRegex(result.stdout, r"Files failed:\s+1")
        self.assertEqual(len(outputs), 9)
        self.assertNotIn("eos.glsl", outputs)

    def test_successful_translation_returns_zero(self):
        result, outputs = self.run_generator("valid")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertRegex(result.stdout, r"Files failed:\s+0")
        self.assertEqual(len(outputs), 10)


if __name__ == "__main__":
    unittest.main()
