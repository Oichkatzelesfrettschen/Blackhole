#!/usr/bin/env python3
"""Check source files and CTest registration against explicit build requirements."""

from __future__ import annotations

import argparse
import datetime as dt
import hashlib
import json
import pathlib
import re
import shutil
import subprocess
import sys
from typing import Any


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("source-dir", "build-dir", "manifest", "md-out", "json-out"):
        parser.add_argument(f"--{name}", required=True)
    return parser


def run_command(command: list[str]) -> subprocess.CompletedProcess[str]:
    return subprocess.run(command, capture_output=True, text=True, check=False)


def parse_ctest(build_dir: pathlib.Path) -> set[str]:
    ctest = shutil.which("ctest")
    if ctest is None:
        raise RuntimeError("CTest is required to discover configured test registrations")
    proc = run_command([ctest, "--test-dir", str(build_dir), "--show-only=json-v1"])
    if proc.returncode:
        raise RuntimeError(f"CTest discovery failed ({proc.returncode}): {proc.stderr.strip()}")
    payload = json.loads(proc.stdout)
    if not isinstance(payload, dict) or not isinstance(payload.get("tests"), list):
        raise ValueError("CTest discovery returned an invalid test inventory")
    tests: set[str] = set()
    for test in payload["tests"]:
        if not isinstance(test, dict) or not isinstance(test.get("name"), str) or not test["name"]:
            raise ValueError("CTest discovery contains a test without a name")
        if test["name"] in tests:
            raise ValueError(f"CTest discovery contains duplicate test name: {test['name']}")
        tests.add(test["name"])
    return tests


def parse_build_options(cache_text: str) -> dict[str, dict[str, Any]]:
    options: dict[str, dict[str, Any]] = {}
    for line in cache_text.splitlines():
        match = re.fullmatch(r"([A-Za-z_][A-Za-z_0-9]*):BOOL=(.*)", line)
        if match:
            name, raw_value = match.groups()
            if name in options:
                raise ValueError(f"Duplicate CMake BOOL option: {name}")
            options[name] = {"raw": raw_value}
    return options


def option_value(name: str, options: dict[str, dict[str, Any]]) -> bool:
    if name not in options:
        raise ValueError(f"Required CMake BOOL option is absent: {name}")
    raw_value = options[name]["raw"].upper()
    if raw_value in {"1", "ON", "YES", "TRUE", "Y"}:
        value = True
    elif raw_value in {
        "",
        "0",
        "OFF",
        "NO",
        "FALSE",
        "N",
        "IGNORE",
        "NOTFOUND",
    } or raw_value.endswith("-NOTFOUND"):
        value = False
    else:
        raise ValueError(f"Unrecognized CMake BOOL value for {name}: {options[name]['raw']!r}")
    options[name]["enabled"] = value
    return value


def test_requirement(entry: Any, options: dict[str, dict[str, Any]]) -> dict[str, Any]:
    if isinstance(entry, str) and entry:
        return {"name": entry, "requires": {}, "applicability": "required"}
    if not isinstance(entry, dict) or set(entry) != {"name", "requires"}:
        raise ValueError("A conditional test requires exactly 'name' and 'requires' fields")
    name, requires = entry["name"], entry["requires"]
    if not isinstance(name, str) or not name:
        raise ValueError("A conditional test requires a nonempty name")
    if (
        not isinstance(requires, list)
        or not requires
        or any(not isinstance(option, str) or not option for option in requires)
        or len(set(requires)) != len(requires)
    ):
        raise ValueError(f"Test {name} requires a nonempty list of distinct CMake BOOL options")
    values = {option: option_value(option, options) for option in requires}
    return {
        "name": name,
        "requires": values,
        "applicability": "required" if all(values.values()) else "not-applicable",
    }


def assess_claims(
    manifest: Any,
    source_dir: pathlib.Path,
    configured_tests: set[str],
    options: dict[str, dict[str, Any]],
) -> list[dict[str, Any]]:
    if not isinstance(manifest, dict) or not isinstance(manifest.get("claims"), list):
        raise ValueError("Claims manifest requires a claims list")
    if not manifest["claims"]:
        raise ValueError("Claims manifest must contain at least one claim")
    claims_report: list[dict[str, Any]] = []
    identifiers: set[str] = set()
    for claim in manifest["claims"]:
        if not isinstance(claim, dict) or any(
            not isinstance(claim.get(field), str) or not claim[field] for field in ("id", "claim")
        ):
            raise ValueError("Each claim requires a nonempty id and claim text")
        if claim["id"] in identifiers:
            raise ValueError(f"Duplicate claim identifier: {claim['id']}")
        identifiers.add(claim["id"])
        files, tests = claim.get("files"), claim.get("tests")
        if (
            not isinstance(files, list)
            or not files
            or any(
                not isinstance(path, str)
                or not path
                or pathlib.Path(path).is_absolute()
                or ".." in pathlib.Path(path).parts
                for path in files
            )
        ):
            raise ValueError(f"Claim {claim['id']} requires source-relative file paths")
        if not isinstance(tests, list) or not tests:
            raise ValueError(f"Claim {claim['id']} requires at least one test")
        requirements = [test_requirement(entry, options) for entry in tests]
        names = [requirement["name"] for requirement in requirements]
        if len(names) != len(set(names)):
            raise ValueError(f"Claim {claim['id']} contains duplicate tests")
        missing_files = [path for path in files if not (source_dir / path).is_file()]
        missing_tests = [
            requirement["name"]
            for requirement in requirements
            if requirement["applicability"] == "required"
            and requirement["name"] not in configured_tests
        ]
        not_applicable = [
            requirement["name"]
            for requirement in requirements
            if requirement["applicability"] == "not-applicable"
        ]
        if missing_files or missing_tests:
            registration_status = "missing-evidence"
        elif len(not_applicable) == len(requirements):
            registration_status = "not-applicable"
        elif not_applicable:
            registration_status = "partially-applicable"
        else:
            registration_status = "registered"
        claims_report.append(
            {
                "id": claim["id"],
                "claim": claim["claim"],
                "status": claim.get("status", "unspecified"),
                "registration_status": registration_status,
                "files": files,
                "tests": names,
                "test_requirements": requirements,
                "not_applicable_tests": not_applicable,
                "missing_files": missing_files,
                "missing_tests": missing_tests,
                "files_ok": not missing_files,
                "tests_ok": not missing_tests if len(not_applicable) < len(requirements) else None,
            }
        )
    return claims_report


def render_markdown(report: dict[str, Any]) -> str:
    lines = [
        "# Physics Claims Report",
        "",
        f"- Generated: `{report['generated_at']}`",
        f"- Source directory: `{report['source_dir']}`",
        f"- Build directory: `{report['build_dir']}`",
        f"- Manifest: `{report['manifest']}`",
        "- Evidence scope: source-file presence and configured CTest registration.",
        "- Test execution and CUDA device execution are outside this verifier's scope.",
    ]
    if "verification_error" in report:
        lines += ["", f"Verification failed: {report['verification_error']}"]
        return "\n".join(lines) + "\n"
    lines += [
        f"- Claims checked: `{report['summary']['claims']}`",
        f"- Missing files: `{report['summary']['missing_files']}`",
        f"- Missing required test references: `{report['summary']['missing_tests']}`",
        f"- Inapplicable test references: `{report['summary']['not_applicable_tests']}`",
        f"- CMake cache SHA-256: `{report['cmake_cache_sha256']}`",
        f"- Manifest SHA-256: `{report['manifest_sha256']}`",
        "",
    ]
    for claim in report["claims"]:
        test_status = claim["tests_ok"] if claim["tests_ok"] is not None else "not-applicable"
        lines += [
            f"## `{claim['id']}`",
            "",
            f"- Claim: {claim['claim']}",
            f"- Declared status: `{claim['status']}`",
            f"- Registration status: `{claim['registration_status']}`",
            f"- Files present: `{claim['files_ok']}`",
            f"- Required tests registered: `{test_status}`",
        ]
        for label, field in (
            ("Missing files", "missing_files"),
            ("Missing tests", "missing_tests"),
        ):
            if claim[field]:
                lines.append(f"- {label}:")
                lines.extend(f"  - `{entry}`" for entry in claim[field])
        for requirement in claim["test_requirements"]:
            if requirement["applicability"] == "not-applicable":
                reason = ", ".join(
                    f"{option}={report['build_options'][option]['raw']}"
                    for option in requirement["requires"]
                )
                lines.append(f"- Inapplicable: `{requirement['name']}` ({reason}).")
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    args = build_parser().parse_args()
    source_dir = pathlib.Path(args.source_dir).resolve()
    build_dir = pathlib.Path(args.build_dir).resolve()
    manifest_path = pathlib.Path(args.manifest).resolve()
    md_out = pathlib.Path(args.md_out).resolve()
    json_out = pathlib.Path(args.json_out).resolve()
    report: dict[str, Any] = {
        "generated_at": dt.datetime.now(dt.UTC).isoformat(timespec="seconds"),
        "source_dir": str(source_dir),
        "build_dir": str(build_dir),
        "manifest": str(manifest_path),
        "evidence_scope": "source-files-and-ctest-registration",
        "execution_status": "not-assessed",
    }
    failed = False
    try:
        manifest_bytes = manifest_path.read_bytes()
        cache_bytes = (build_dir / "CMakeCache.txt").read_bytes()
        options = parse_build_options(cache_bytes.decode("utf-8"))
        configured_tests = parse_ctest(build_dir)
        claims = assess_claims(json.loads(manifest_bytes), source_dir, configured_tests, options)
        report.update(
            manifest_sha256=hashlib.sha256(manifest_bytes).hexdigest(),
            cmake_cache_sha256=hashlib.sha256(cache_bytes).hexdigest(),
            build_options={name: value for name, value in options.items() if "enabled" in value},
            configured_test_count=len(configured_tests),
            claims=claims,
            summary={
                "claims": len(claims),
                "missing_files": sum(len(claim["missing_files"]) for claim in claims),
                "missing_tests": sum(len(claim["missing_tests"]) for claim in claims),
                "not_applicable_tests": sum(len(claim["not_applicable_tests"]) for claim in claims),
            },
        )
        failed = bool(report["summary"]["missing_files"] or report["summary"]["missing_tests"])
    except (OSError, ValueError, RuntimeError) as error:
        report["verification_error"] = str(error)
        print(f"[FAIL] Physics claims verification: {error}", file=sys.stderr)
        failed = True
    md_out.parent.mkdir(parents=True, exist_ok=True)
    json_out.parent.mkdir(parents=True, exist_ok=True)
    md_out.write_text(render_markdown(report), encoding="utf-8")
    json_out.write_text(json.dumps(report, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return int(failed)


if __name__ == "__main__":
    raise SystemExit(main())
