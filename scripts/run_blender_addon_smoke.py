#!/usr/bin/env python3
"""Prepare an isolated addon install and run a headless Blender smoke test."""

from __future__ import annotations

import argparse
import json
import os
import pathlib
import shutil
import subprocess
import tempfile


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blender-executable", required=True)
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--addon-zip", required=True)
    parser.add_argument("--bridge-lib", required=True)
    parser.add_argument("--label", required=True)
    parser.add_argument("--expect-engine", choices=["", "cycles", "octane"], default="")
    parser.add_argument("--json-out")
    parser.add_argument("--log-out")
    parser.add_argument("--timeout-seconds", type=int, default=120)
    return parser


def main() -> int:
    args = build_parser().parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    addon_zip = pathlib.Path(args.addon_zip).resolve()
    bridge_lib = pathlib.Path(args.bridge_lib).resolve()
    inner_script = source_dir / "scripts" / "blender_addon_smoke_inner.py"
    json_out = pathlib.Path(args.json_out).resolve() if args.json_out else None
    log_out = pathlib.Path(args.log_out).resolve() if args.log_out else None

    if not addon_zip.exists():
        raise SystemExit(f"Addon package not found: {addon_zip}")
    if not bridge_lib.exists():
        raise SystemExit(f"Bridge library not found: {bridge_lib}")
    if not inner_script.exists():
        raise SystemExit(f"Inner Blender smoke script not found: {inner_script}")
    blender_path = shutil.which(args.blender_executable) or args.blender_executable

    with tempfile.TemporaryDirectory(prefix="blackhole_blender_smoke_") as tmp:
        temp_root = pathlib.Path(tmp)
        user_scripts = temp_root / "scripts"
        addons_dir = user_scripts / "addons"
        addons_dir.mkdir(parents=True, exist_ok=True)
        shutil.unpack_archive(str(addon_zip), str(addons_dir), "zip")

        env = os.environ.copy()
        env["BLENDER_USER_SCRIPTS"] = str(user_scripts)
        env["BLACKHOLE_BRIDGE_LIB"] = str(bridge_lib)
        env["BLACKHOLE_SMOKE_LABEL"] = args.label
        env["BLACKHOLE_SMOKE_EXPECT_ENGINE"] = args.expect_engine
        env.pop("OCIO", None)
        inner_report = temp_root / "smoke_report.json"
        env["BLACKHOLE_SMOKE_REPORT_JSON"] = str(inner_report)

        command = [
            blender_path,
            "--background",
            "--factory-startup",
            "--python-exit-code",
            "1",
            "--python",
            str(inner_script),
        ]
        report = {
            "blender_executable": blender_path,
            "label": args.label,
            "expect_engine": args.expect_engine,
            "addon_zip": str(addon_zip),
            "bridge_lib": str(bridge_lib),
            "command": command,
            "log_path": str(log_out) if log_out is not None else "",
            "inner_report": {},
        }
        try:
            proc = subprocess.run(
                command,
                env=env,
                check=False,
                capture_output=True,
                text=True,
                timeout=args.timeout_seconds,
            )
            combined_output = (proc.stdout or "") + (proc.stderr or "")
            report["returncode"] = proc.returncode
        except subprocess.TimeoutExpired as exc:
            combined_output = (exc.stdout or "") + (exc.stderr or "")
            report["returncode"] = 124
            report["error"] = f"Timed out after {args.timeout_seconds} seconds"
        if combined_output:
            print(combined_output, end="")
        if inner_report.exists():
            report["inner_report"] = json.loads(inner_report.read_text(encoding="utf-8"))
        if log_out is not None:
            log_out.parent.mkdir(parents=True, exist_ok=True)
            log_out.write_text(combined_output, encoding="utf-8")
        if json_out is not None:
            json_out.parent.mkdir(parents=True, exist_ok=True)
            json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        return int(report["returncode"])


if __name__ == "__main__":
    raise SystemExit(main())
