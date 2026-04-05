#!/usr/bin/env python3
"""Verify the local physics claims manifest against files and configured tests."""

from __future__ import annotations

import argparse
import datetime as dt
import json
import pathlib
import re
import shutil
import subprocess
from typing import Any


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-dir", required=True)
    parser.add_argument("--build-dir", required=True)
    parser.add_argument("--manifest", required=True)
    parser.add_argument("--md-out", required=True)
    parser.add_argument("--json-out", required=True)
    return parser


def run_command(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, capture_output=True, text=True, check=False)


def parse_ctest(build_dir: pathlib.Path) -> set[str]:
    ctest = shutil.which("ctest")
    if ctest is None:
        return set()
    proc = run_command([ctest, "--test-dir", str(build_dir), "-N"])
    pattern = re.compile(r"^\s*Test\s+#?\d+:\s+(.+?)\s*$")
    tests: set[str] = set()
    for line in proc.stdout.splitlines():
        match = pattern.match(line)
        if match:
            tests.add(match.group(1))
    return tests


def render_markdown(report: dict[str, Any]) -> str:
    lines: list[str] = []
    lines.append("# Physics Claims Report")
    lines.append("")
    lines.append(f"- Generated: `{report['generated_at']}`")
    lines.append(f"- Source directory: `{report['source_dir']}`")
    lines.append(f"- Build directory: `{report['build_dir']}`")
    lines.append(f"- Manifest: `{report['manifest']}`")
    lines.append(f"- Claims checked: `{report['summary']['claims']}`")
    lines.append(f"- Missing files: `{report['summary']['missing_files']}`")
    lines.append(f"- Missing tests: `{report['summary']['missing_tests']}`")
    lines.append("")
    for claim in report["claims"]:
        lines.append(f"## `{claim['id']}`")
        lines.append("")
        lines.append(f"- Claim: {claim['claim']}")
        lines.append(f"- Status: `{claim['status']}`")
        lines.append(f"- Files ok: `{claim['files_ok']}`")
        lines.append(f"- Tests ok: `{claim['tests_ok']}`")
        if claim["missing_files"]:
            lines.append("- Missing files:")
            for path in claim["missing_files"]:
                lines.append(f"  - `{path}`")
        if claim["missing_tests"]:
            lines.append("- Missing tests:")
            for test_name in claim["missing_tests"]:
                lines.append(f"  - `{test_name}`")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    args = build_parser().parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    build_dir = pathlib.Path(args.build_dir).resolve()
    manifest_path = pathlib.Path(args.manifest).resolve()
    md_out = pathlib.Path(args.md_out).resolve()
    json_out = pathlib.Path(args.json_out).resolve()

    raw = json.loads(manifest_path.read_text(encoding="utf-8"))
    configured_tests = parse_ctest(build_dir)
    claims_report: list[dict[str, Any]] = []
    missing_files_total = 0
    missing_tests_total = 0

    for claim in raw.get("claims", []):
        files = claim.get("files", [])
        tests = claim.get("tests", [])
        missing_files = [path for path in files if not (source_dir / path).exists()]
        missing_tests = [name for name in tests if name not in configured_tests]
        missing_files_total += len(missing_files)
        missing_tests_total += len(missing_tests)
        claims_report.append(
            {
                "id": claim["id"],
                "claim": claim["claim"],
                "status": claim.get("status", "unspecified"),
                "files": files,
                "tests": tests,
                "missing_files": missing_files,
                "missing_tests": missing_tests,
                "files_ok": not missing_files,
                "tests_ok": not missing_tests,
            }
        )

    report = {
        "generated_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        "source_dir": str(source_dir),
        "build_dir": str(build_dir),
        "manifest": str(manifest_path),
        "claims": claims_report,
        "summary": {
            "claims": len(claims_report),
            "missing_files": missing_files_total,
            "missing_tests": missing_tests_total,
        },
    }

    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(render_markdown(report), encoding="utf-8")
    json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    if missing_files_total or missing_tests_total:
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
