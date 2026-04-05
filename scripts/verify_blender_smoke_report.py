#!/usr/bin/env python3
"""Verify a generated Blender or Octane smoke report."""

from __future__ import annotations

import argparse
import json
import pathlib
import sys


def parse_args(argv: list[str]) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--report", required=True, type=pathlib.Path)
    parser.add_argument("--expect-engine", choices=["", "cycles", "octane"], default="")
    parser.add_argument("--md-out", type=pathlib.Path)
    parser.add_argument("--json-out", type=pathlib.Path)
    return parser.parse_args(argv)


def normalize_engine(name: str) -> str:
    lowered = name.lower()
    if "octane" in lowered:
        return "octane"
    if lowered == "cycles":
        return "cycles"
    return lowered


def write_text(path: pathlib.Path | None, content: str) -> None:
    if path is None:
        return
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def render_markdown(report: dict) -> str:
    inner = report.get("inner_report", {})
    lines = [
        "# Blender Smoke Report Verification",
        "",
        f"- Report: `{report.get('report_path', '')}`",
        f"- Label: `{report.get('label', '')}`",
        f"- Return code: `{report.get('returncode', -1)}`",
        f"- Status: `{inner.get('status', '')}`",
        f"- Selected engine: `{inner.get('selected_engine', '')}`",
        f"- Bridge path: `{inner.get('bridge_library_path', '')}`",
        "",
    ]
    return "\n".join(lines).strip() + "\n"


def main(argv: list[str]) -> int:
    args = parse_args(argv)
    report_path = args.report.resolve()
    if not report_path.exists():
        raise SystemExit(f"Smoke report not found: {report_path}")
    report = json.loads(report_path.read_text(encoding="utf-8"))
    report["report_path"] = str(report_path)
    inner = report.get("inner_report", {})

    if report.get("returncode") != 0:
        raise SystemExit(f"Smoke report return code was non-zero: {report.get('returncode')}")
    if inner.get("status") != "success":
        raise SystemExit(f"Smoke report inner status was not success: {inner.get('status')}")
    bridge_path = pathlib.Path(inner.get("bridge_library_path", ""))
    if not bridge_path.exists():
        raise SystemExit(f"Bridge library path recorded in smoke report does not exist: {bridge_path}")
    capabilities = inner.get("bridge_capabilities", {})
    if int(capabilities.get("source_params_size", 0)) <= 0 or int(capabilities.get("disk_params_size", 0)) <= 0:
        raise SystemExit("Smoke report bridge capabilities did not include valid struct sizes")
    studio_quality = inner.get("studio_quality", {})
    if not studio_quality:
        raise SystemExit("Smoke report did not record studio_quality settings")
    if not studio_quality.get("engine"):
        raise SystemExit("Smoke report studio_quality did not record a render engine")
    if not studio_quality.get("view_transform"):
        raise SystemExit("Smoke report studio_quality did not record a view transform")
    if inner.get("generated_horizon") is not True:
        raise SystemExit("Smoke report did not confirm horizon generation")
    if inner.get("lensing_shape") != [8, 16, 4]:
        raise SystemExit(f"Unexpected lensing shape in smoke report: {inner.get('lensing_shape')}")
    if capabilities.get("cuda") and inner.get("cuda_smoke_rc", 0) != 0:
        raise SystemExit(f"CUDA smoke path returned non-zero: {inner.get('cuda_smoke_rc')}")

    if args.expect_engine:
        selected = normalize_engine(inner.get("selected_engine", ""))
        if selected != args.expect_engine:
            raise SystemExit(
                f"Selected engine mismatch: expected {args.expect_engine}, got {inner.get('selected_engine', '')}"
            )

    write_text(args.json_out.resolve() if args.json_out else None, json.dumps(report, indent=2, sort_keys=True) + "\n")
    write_text(args.md_out.resolve() if args.md_out else None, render_markdown(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
