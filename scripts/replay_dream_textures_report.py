#!/usr/bin/env python3
"""Replay a Dream Textures direct-pipeline report through the verifier."""

from __future__ import annotations

import argparse
import json
import pathlib
import subprocess
import sys


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", type=pathlib.Path, required=True)
    parser.add_argument("--verifier", type=pathlib.Path, default=pathlib.Path("scripts/verify_dream_textures_direct_pipeline.py"))
    parser.add_argument("--json-out", type=pathlib.Path)
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--log-out", type=pathlib.Path)
    parser.add_argument("--print-only", action="store_true")
    return parser.parse_args(argv)


def build_command(args: argparse.Namespace, report: dict[str, object]) -> list[str]:
    inner = report.get("inner_report", {})
    if not isinstance(inner, dict):
        raise SystemExit("Report did not contain inner_report metadata")
    provenance = inner.get("prompt_provenance", {})
    if not isinstance(provenance, dict):
        raise SystemExit("Report did not contain prompt_provenance metadata")

    command = [
        sys.executable,
        str(args.verifier),
        "--label",
        str(report.get("label", "dream-replay")),
        "--blender-executable",
        str(report.get("blender_executable", "")),
        "--source-dir",
        str(report.get("source_dir", "")),
        "--slot",
        str(inner.get("slot", "disk")),
        "--model-id",
        str(inner.get("model_id", provenance.get("model_id", ""))),
        "--prompt-style",
        str(inner.get("prompt_style", provenance.get("prompt_style", "scientific"))),
        "--width",
        str(inner.get("width", provenance.get("width", 64))),
        "--height",
        str(inner.get("height", provenance.get("height", 64))),
        "--steps",
        str(inner.get("steps", provenance.get("steps_requested", 8))),
        "--seed",
        str(inner.get("seed", provenance.get("seed", 7))),
        "--timeout-seconds",
        "180",
        "--json-out",
        str(args.json_out or args.report.with_name(args.report.stem + "_replay.json")),
    ]
    user_scripts = str(report.get("user_scripts", ""))
    if user_scripts:
        command.extend(["--user-scripts", user_scripts])
    if "octane" in str(report.get("label", "")).lower():
        command.append("--sanitize-ocio")
    if args.md_out:
        command.extend(["--md-out", str(args.md_out)])
    if args.log_out:
        command.extend(["--log-out", str(args.log_out)])
    return command


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    report = json.loads(args.report.read_text(encoding="utf-8"))
    command = build_command(args, report)
    if args.print_only:
        print(json.dumps({"command": command}, indent=2))
        return 0
    completed = subprocess.run(command, check=False)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
