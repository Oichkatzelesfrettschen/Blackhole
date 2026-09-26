"""Hold the headless capture wrapper to the native CLI's record options."""

import importlib.util
import sys
import unittest
from pathlib import Path
from unittest import mock

WRAPPER_PATH = Path(__file__).resolve().parents[1] / "scripts" / "run_glsl_headless.py"
SPEC = importlib.util.spec_from_file_location("run_glsl_headless", WRAPPER_PATH)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError(f"Cannot load headless wrapper: {WRAPPER_PATH}")
WRAPPER = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = WRAPPER
SPEC.loader.exec_module(WRAPPER)


def command_for(*arguments: str) -> list[str]:
    argv = ["run_glsl_headless.py", "--record-dir", "frames", *arguments]
    with mock.patch.object(sys, "argv", argv):
        return WRAPPER.build_command(WRAPPER.parse_args())


def option(command: list[str], flag: str) -> str | None:
    return command[command.index(flag) + 1] if flag in command else None


class HeadlessWrapper(unittest.TestCase):
    def test_default_composition_is_the_native_default(self):
        # src/platform/cli_options.h: recordComposition = "above-disk".
        self.assertEqual(option(command_for(), "--record-composition"), "above-disk")

    def test_record_spin_is_forwarded(self):
        self.assertEqual(option(command_for("--record-spin", "0.9"), "--record-spin"), "0.9")
        self.assertIsNone(option(command_for(), "--record-spin"))


if __name__ == "__main__":
    unittest.main()
